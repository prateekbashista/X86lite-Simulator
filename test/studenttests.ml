open Util.Assert
open X86
open Simulator
open Gradedtests
open Asm
(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let mov_ri =
 test_machine
 [
 InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 ]
(* let factorial_iter n = [ text "main"
                                  [ Movq,  [~$1; ~%Rax]
                                  ; Movq,  [~$n; ~%Rdi]
                                  ]
                           ; text "loop"
                                  [ Cmpq,  [~$0; ~%Rdi]
                                  ; J Eq,  [~$$"exit"]
                                  ; Imulq, [~%Rdi; ~%Rax]
                                  ; Decq,  [~%Rdi]
                                  ; Jmp,   [~$$"loop"]
                                  ]
                           ; text "exit"
                                  [ Retq,  [] 
                                  ]
                           ] *)


let binary_search_custom n = [ text "binary_search"
                                    [Pushq,  [~%Rbp];
                                     Movq,  [~%Rsp; ~%Rbp];
                                     Subq, [~$128; ~%Rsp];
                                     Movq, [~$4; stack_offset (-8L)];
                                     Movq, [~$5; stack_offset (-16L)];
                                     Movq, [~$90;stack_offset (-24L)];
                                     Movq, [~$100; stack_offset (-32L)];
                                     Movq, [~$160; stack_offset (-40L)];
                                     Movq, [~$1000; stack_offset (-48L)];
                                     Movq, [~$0; ~%R10];
                                     Movq, [~$5; ~%R12];
                                     Movq, [~$0; ~%R11];
                                     Movq, [~$(-1); ~%Rax]]
                               text "loop"
                                    ]                                    


let provided_tests : suite = [
  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
  ]);

] 
