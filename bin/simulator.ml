(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86
(* open Int64_overflow *)

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
  | Eq -> if (fz) then true else false
  | Neq -> if (not fz) then true else false
  | Gt -> if (fs = fo && (not fz)) then true else false
  | Lt -> if (fs <> fo) then true else false (* (SF && not OF) || (not SF && OF) *)
  | Ge -> if (fs = fo) then true else false
  | Le -> if (fs <> fo || fz) then true else false

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr : quad) : int option =
    if (addr > (Int64.sub mem_top 8L)) || (addr < mem_bot) then None
    else Some (Int64.to_int (Int64.sub addr mem_bot))

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let update_rip(m : mach) (rip_addr : int64) : unit =
  if (rip_addr = 0L) 
    then m.regs.(rind Rip) <- Int64.add m.regs.(rind Rip) 8L
  else m.regs.(rind Rip) <- rip_addr

(* Extract sbyte list from memory *)
let conv_sbyte_list (memory: sbyte array) (start: int) : sbyte list =
  Array.to_list (Array.sub memory start 8)

(* Convert int64 to sbyte list and write into sbyte array *)
let memory_write (ans: sbyte list) (memory: sbyte array) (dest_position: int) : unit =
  Array.blit (Array.of_list ans) 0 memory dest_position 8

(*Opex albm - Operand extraction for Arithmatic, logical and Bit manipulation Operations*)
(*As a placeholder, returning 0L for all else tests*)
let opex_albm (m:mach) (o:operand) : int64 =
  match o with 
  | Imm x -> begin match x with
              | Lit l1 -> l1
              | _ -> 0L
              end
  | Reg r -> m.regs.(rind r)
  | Ind1 y -> begin match y with
              | Lit l2 -> let index_l2 = map_addr l2 in 
                            begin match index_l2 with
                            | None-> 0L
                            | Some z -> int64_of_sbytes (conv_sbyte_list m.mem z)
                            end
              | _ -> 0L
            end
  | Ind2 ri -> let ri_index = map_addr (m.regs.(rind ri)) in
                            begin match ri_index with
                            | None-> 0L
                            | Some z -> int64_of_sbytes (conv_sbyte_list m.mem z)
                            end
  | Ind3 (i,r) -> begin match i with 
                  | Lit l3 -> let r_addr = map_addr ((Int64.add m.regs.(rind r) l3)) in
                              begin match r_addr with
                              | None-> 0L
                              | Some z -> int64_of_sbytes (conv_sbyte_list m.mem z)
                            end
                  | _ -> 0L
                  end

(* Function to update destination *)
let update_dest (dest:operand) (ans:int64) (m:mach) : unit =
  match dest with
  | Reg r -> m.regs.(rind r) <- ans
  | Imm i0 -> begin match i0 with
              | Lit l1 -> let l1_index = map_addr l1 in
                begin match l1_index with
                  | None -> raise X86lite_segfault
                  | Some y -> memory_write (sbytes_of_int64 ans) m.mem y
                end
              | _ -> ()
              end
  | Ind1 i1 -> begin match i1 with
              | Lit l1 -> let mem_index = map_addr l1 in
                          begin match mem_index with
                          | None -> raise X86lite_segfault
                          | Some y -> let addr = int64_of_sbytes (conv_sbyte_list m.mem y) in
                              let addr_index = map_addr addr in
                                begin match addr_index with
                                | None -> raise X86lite_segfault
                                | Some z -> memory_write (sbytes_of_int64 ans) m.mem z
                                end
                          end
              | _ -> ()
              end
  | Ind2 r -> let reg_addr_idx = map_addr (m.regs.(rind r)) in
                begin match reg_addr_idx with
                | None -> raise X86lite_segfault
                | Some a -> memory_write (sbytes_of_int64 ans) m.mem a
                end
  | Ind3 (i, r) -> begin match i with
                    | Lit im -> let addr_idx = map_addr (Int64.add m.regs.(rind r) im) in
                                  begin match addr_idx with
                                  | None -> raise X86lite_segfault
                                  | Some z -> memory_write (sbytes_of_int64 ans) m.mem z
                                  end
                    | _ -> ()
                    end

let update_fz (m : mach) (ans: int64) : unit =
  if (ans = 0L) then m.flags.fz <- true
  else m.flags.fz <- false

let update_fo (m : mach) (ans : bool) : unit =
  if (ans) then m.flags.fo <- true
  else m.flags.fo <- false

let update_fs (m : mach) (ans: int64) : unit =
  if (ans < 0L) then m.flags.fs <- true
  else m.flags.fs <- false

let update_flags(m : mach) (ans: Int64_overflow.t) : unit =
  update_fo m ans.overflow;
  update_fs m ans.value;
  update_fz m ans.value

(* This function handles two operand instructions of type arithmetic and 
   logical. *)
let arithmetic_log_ops (m: mach) (op: opcode) (oprnds: operand list) : unit =
  match oprnds with
    | [] -> ()
    | dest::[] -> let single_op_ans : Int64_overflow.t = begin match op with
                  | Incq -> Int64_overflow.succ (opex_albm m dest)
                  | Decq -> Int64_overflow.pred (opex_albm m dest)
                  | Negq -> Int64_overflow.neg (opex_albm m dest)
                  | Notq -> {value = (Int64.lognot (opex_albm m dest)); overflow = false}
                  | _ -> {value = 0L;overflow =false}
                  end
                in 
                update_dest dest single_op_ans.value m;
                if (op <> Notq) then update_flags m single_op_ans
    | src::dest::tl -> let two_op_ans : Int64_overflow.t = match op with
                       | Addq -> Int64_overflow.add (opex_albm m src) (opex_albm m dest)
                       | Subq -> Int64_overflow.sub (opex_albm m dest) (opex_albm m src) 
                       | Imulq -> Int64_overflow.mul (opex_albm m src) (opex_albm m dest)
                       | Andq -> {value = (Int64.logand (opex_albm m src) (opex_albm m dest)) ; overflow = false}
                       | Orq -> {value = (Int64.logor (opex_albm m src) (opex_albm m dest)); overflow = false}
                       | Xorq -> {value = (Int64.logxor (opex_albm m src) (opex_albm m dest)); overflow = false}
                       | _ -> {value = 0L;overflow =false}
                       in
                       update_dest dest two_op_ans.value m;
                       update_flags m two_op_ans


let data_mov_ops (m: mach) (op: opcode) (oprnd:operand list) : unit =
  match oprnd with
  | [] -> ()
  | value::[] -> begin match op with
                  | Pushq -> m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
                              let addr_idx = map_addr m.regs.(rind Rsp) in
                              begin match addr_idx with
                              | None -> raise X86lite_segfault
                              | Some z -> memory_write (sbytes_of_int64 (opex_albm m value)) m.mem z
                              end
                  | Popq -> let mem_idx = map_addr (m.regs.(rind Rsp)) in
                              begin match mem_idx with
                              | None -> raise X86lite_segfault
                              | Some b -> update_dest value (int64_of_sbytes (conv_sbyte_list m.mem b)) m;
                                          m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L
                              end
                  | _ -> ()
                  end
  | src::dest::[] -> begin match op with 
                      | Movq -> update_dest dest (opex_albm m src) m
                      | Leaq -> update_dest dest (opex_albm m src) m
                      | _ -> ()
                      end
  | _ -> ()

let bit_manip_ops (m: mach) (op: opcode) (oprnd:operand list) : unit =
  match oprnd with
  | [] -> ()
  | value :: [] -> begin match op with
                  | Set cc -> let orig_val = opex_albm m value in
                              if (interp_cnd m.flags cc) then
                                  update_dest value (Int64.logor (Int64.logand orig_val 0xFFFFFFFFFFFFFF00L) 0x01L) m
                              else
                                  update_dest value (Int64.logand orig_val 0xFFFFFFFFFFFFFF00L) m
                  | _ -> ()
                  end
  | amt :: dest :: [] -> let amount_val = Int64.to_int (opex_albm m amt) in 
                      begin match op with 
                      | Sarq -> let bit_ans_sarq = Int64.shift_right (opex_albm m dest) amount_val in
                                let _ =   match amount_val with
                                | 1 -> update_fo m true 
                                | 0 -> ()
                                | _ -> update_fs m bit_ans_sarq; update_fz m bit_ans_sarq
                                in
                                update_dest dest bit_ans_sarq m
                      | Shlq -> let bit_ans_shlq = Int64.shift_left (opex_albm m dest) amount_val in
                                let _ =   match amount_val with
                                | 1 -> let top_bit = Int64.shift_right_logical (opex_albm m dest) 63 in
                                       let sec_bit = Int64.shift_right_logical (opex_albm m dest) 62 in
                                        if (top_bit <> sec_bit) then update_fo m true else update_fo m false
                                | 0 -> ()
                                | _ -> update_fs m bit_ans_shlq; update_fz m bit_ans_shlq
                                in
                                update_dest dest bit_ans_shlq m
                      | Shrq -> let bit_ans_shrq = Int64.shift_right_logical (opex_albm m dest) amount_val in
                                let _ =   match amount_val with
                                | 1 -> let msb_bit = Int64.shift_right_logical (opex_albm m dest) 63 in
                                       if (msb_bit = 1L) then update_fo m true else update_fo m false
                                | 0 -> ()
                                | _ -> let msb_bit_ans = Int64.shift_right_logical bit_ans_shrq 63 in
                                       if (msb_bit_ans = 1L) then m.flags.fs <- true else m.flags.fs <- false ;
                                       update_fz m bit_ans_shrq
                                in
                                update_dest dest bit_ans_shrq m

                      | _ -> ()
                      end
  | _ -> ()

let ctrl_flow_ops (m: mach) (op: opcode) (oprnd:operand list) : int64 =
  match oprnd with
  | [] -> begin match op with
          | Retq -> data_mov_ops m Popq [Reg(Rip)]; opex_albm m (Reg Rip)
          | _ -> 0L
          end
  | src :: [] -> begin match op with
                  | Jmp -> opex_albm m src
                  (* Preserve rip by pushing it onto the stack and compute the call address *)
                  | Callq -> update_rip m 0L; data_mov_ops m Pushq [Reg(Rip)]; opex_albm m src
                  | J cc -> if (interp_cnd m.flags cc) then opex_albm m src else 0L
                  | _ -> 0L
                  end
  | src1 :: src2 :: _ -> begin match op with
                        | Cmpq -> let comp_ans : Int64_overflow.t = 
                                  Int64_overflow.sub (opex_albm m src2) (opex_albm m src1) in
                                  update_flags m comp_ans;
                                  
                         0L (*return *)
                        | _-> 0L
                        end


let step (m:mach) : unit =
    let addr = m.regs.(rind Rip) in
      let x = map_addr addr in
        match x with
        | None -> raise X86lite_segfault
        | Some y -> let curr_sbyte = m.mem.(y) in
          match curr_sbyte with
          | InsFrag -> update_rip m 0L
          | Byte b -> update_rip m 0L
          | InsB0 curr_insn -> let rip_val = match curr_insn with 
            (* Arithmetic Instructions *)
            | (Addq, oprnd) -> arithmetic_log_ops m Addq oprnd ; 0L
            | (Subq, oprnd) -> arithmetic_log_ops m Subq oprnd ; 0L
            | (Imulq, oprnd) -> arithmetic_log_ops m Imulq oprnd ; 0L
            | (Incq, oprnd) -> arithmetic_log_ops m Incq (oprnd) ; 0L
            | (Decq, oprnd) -> arithmetic_log_ops m Decq (oprnd) ; 0L
            | (Negq, oprnd) -> arithmetic_log_ops m Negq oprnd  ; 0L
            (* Logical Instructions *)
            | (Andq, oprnd) -> arithmetic_log_ops m Andq oprnd ; 0L
            | (Orq, oprnd) -> arithmetic_log_ops m Orq oprnd ; 0L
            | (Xorq, oprnd) -> arithmetic_log_ops m Xorq oprnd ; 0L
            | (Notq, oprnd)-> arithmetic_log_ops m Notq oprnd ; 0L
            (* Bitwise Manipulation Instructions *)
            | (Sarq, oprnd)-> bit_manip_ops m Sarq oprnd ; 0L
            | (Shlq, oprnd)-> bit_manip_ops m Shlq oprnd ; 0L
            | (Shrq, oprnd)-> bit_manip_ops m Shrq oprnd ; 0L
            | (Set cc, oprnd) -> bit_manip_ops m (Set cc) oprnd ; 0L 
            (* Data Movement Instructions *)
            | (Leaq, oprnd) -> data_mov_ops m Leaq oprnd; 0L
            | (Movq, oprnd) -> data_mov_ops m Movq oprnd ; 0L
            | (Pushq, oprnd) -> data_mov_ops m Pushq oprnd ; 0L
            | (Popq, oprnd) -> data_mov_ops m Popq oprnd ; 0L
            (* Control Flow Instructions *)
            | (Cmpq, oprnd) -> ctrl_flow_ops m Cmpq oprnd
            | (Jmp, oprnd) -> ctrl_flow_ops m Jmp oprnd
            | (Callq, oprnd) -> ctrl_flow_ops m Callq oprnd
            | (Retq, oprnd) -> ctrl_flow_ops m Retq oprnd
            | (J cc, oprnd) -> ctrl_flow_ops m (J cc) oprnd
            in
            update_rip m rip_val

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)

type symbol_table = lbl -> int64

let init_table : symbol_table = fun _ -> -1L

(*This function inserts a mapping of label to an address*)
let update_table (table : symbol_table) (label : lbl) (addr : int64) : symbol_table =
  fun (z:lbl) ->
  if label = z then addr else table z

(* Looking up the address of a label in table*)
let lookup_table (table: symbol_table) (label: lbl) : int64 = 
  table label

let look_and_add (table: symbol_table) (label: lbl) (addr : int64) : symbol_table =
  if (table label = -1L)
    then update_table table label addr 
  else
    raise (Redefined_sym label)

(*This function appends text(insn) to the provided sbyte list*)
let insn_handler (insn_list: sbyte list) (instruction : ins): sbyte list = 
insn_list @ sbytes_of_ins instruction

(*This function appends data(data) to the provided sbyte list*)
let data_handler (data_list: sbyte list) (data_elem : data) : sbyte list = 
  data_list @ sbytes_of_data data_elem

let accum_insn_sybtes  (insn_list : sbyte list) (element : elem) : sbyte list = 
  (* Label is updated in the symbol table*)
  (* implementation for global is undefined*)
  match element.asm with
  | Text insns -> List.fold_left insn_handler insn_list insns
  | Data _ -> insn_list
   
let accum_data_sybtes (data_list : sbyte list) (element : elem) : sbyte list = 
  (* Label is updated in the symbol table*)
  (* implementation for global is undefined*)
  match element.asm with
  | Text _ -> data_list
  | Data data_elems -> List.fold_left data_handler data_list data_elems

let rec label_handler (sym_tab : symbol_table) (p:prog) (curr_addr : int64) (data_addr : int64 ref) : symbol_table = 
  match p with
  | [] -> sym_tab
  | h::tl -> begin
                let asm_lenth = match h.asm with
                | Text t_len -> List.length t_len
                | Data d_len -> data_addr.contents <- curr_addr ; List.length d_len
                in
                let new_addr =  Int64.add curr_addr (Int64.mul (Int64.of_int asm_lenth) 8L) in
                label_handler (look_and_add sym_tab h.lbl curr_addr) tl new_addr data_addr
              end

let rec map_operand (curr_ops : operand list) (lbl_map : symbol_table) : operand list =
  match curr_ops with
  | [] -> []
  | h :: tl -> let ins_replace: operand = match h with
                | Imm i -> begin match i with
                          | Lbl l2 -> let lookup_val = lookup_table lbl_map l2 in
                                        if lookup_val <> -1L then Imm (Lit (lookup_val))
                                        else raise (Undefined_sym l2)
                          | _ -> h
                            end
                | Ind1 i1 -> begin match i1 with
                            | Lbl l1 -> let lookup_val = lookup_table lbl_map l1 in
                                        if lookup_val <> -1L then Ind1 ((Lit (lookup_val)))
                                        else raise (Undefined_sym l1)
                            | _ -> h
                            end
                | Ind3 (i2, r) -> begin match i2 with
                                  | Lbl l3 -> let lookup_val = lookup_table lbl_map l3 in
                                        if lookup_val <> -1L then Ind3 ((Lit (lookup_val)), r)
                                        else raise (Undefined_sym l3)
                                  | _ -> h
                                  end
                | _ -> h
                in
                ins_replace :: map_operand tl lbl_map

let rec map_text (text_: ins list) (lbl_map: symbol_table) : ins list =
  match text_ with
    | [] -> []
    | h :: tl -> let op_code = match h with x, _ -> x in
                  let op_list = match h with _, x -> x in
                    (op_code, map_operand op_list lbl_map) :: (map_text tl lbl_map)

let rec map_elem (elements : prog) (lbl_map : symbol_table) : prog = 
  match elements with
  | [] -> []
  | h :: tl -> match h.asm with
                | Text text_ -> {lbl = h.lbl;
                                 global = h.global;
                                 asm = Text (map_text text_ lbl_map)} :: (map_elem tl lbl_map)
                | _ -> h :: (map_elem tl lbl_map)

let assemble (p:prog) : exec =
  let data_addr = ref mem_bot in
  let lable_mapping = label_handler init_table p mem_bot data_addr in
    let main_label : lbl = "main" in
      if (lookup_table lable_mapping main_label) = -1L then raise (Undefined_sym main_label)
      else
        let resolved_labels = map_elem p lable_mapping in
        let texts  = List.fold_left accum_insn_sybtes [] resolved_labels in
        let datas = List.fold_left accum_data_sybtes [] resolved_labels in
        {entry = lookup_table lable_mapping main_label; 
         text_pos = mem_bot;
         data_pos = data_addr.contents;
         text_seg = texts;
         data_seg = datas}

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let mem = (Array.make mem_size (Byte '\x00')) in
  Array.blit (Array.of_list text_seg ) 0 mem 0 (List.length text_seg);
  let data_index = map_addr data_pos in
                    match data_index with
                    | None -> raise X86lite_segfault
                    | Some y -> Array.blit (Array.of_list data_seg) 0 mem y (List.length data_seg);
  let regs = Array.make nregs 0L in
  regs.(rind Rip) <- entry;
  regs.(rind Rsp) <- Int64.sub mem_top 8L;
  let exit_index =  map_addr (Int64.sub mem_top 8L) in
                    match exit_index with
                    | None -> raise X86lite_segfault
                    | Some idx -> memory_write (sbytes_of_int64 exit_addr) mem idx;
  { flags = {fo = false; fs = false; fz = false};
    regs = regs;
    mem = mem
  }