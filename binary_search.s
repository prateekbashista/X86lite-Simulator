    .section .text
    .global main
binary_search:
    ;;#; Function Prologue
    pushq %rbp
    movq %rsp, %rbp
    subq $128, %rsp

    ;;#; Push the array onto the stack
    movq $4, -8(%rsp)
    movq $5, -16(%rsp)
    movq $90, -24(%rsp)
    movq $100, -32(%rsp)
    movq $160, -40(%rsp)
    movq $1000, -48(%rsp)

    ;;#; Create left, mid and right
    ;;#; Using r10 for left, r11 for mid, and r12 for right
    movq $0, %r10 ;;#; Left pointer
    movq $5, %r12 ;;#; Right pointer
    movq $0, %r11 ;;#; Mid pointer

    movq $-1, %rax ;;#; Save default result

loop:
    cmpq %r10, %r12
    jle exit

    movq %r12, %r8 ;;#; Save previous right pointer
    addq %r10, %r8 ;;#; l + r
    shrq $1, %r8 ;;#; (r + l) / 2

    movq %r8, %r11 ;;#; Mid pointer

    incq %r8
    imulq $-8, %r8
    lea (%rsp, %r8), %r8

    cmpq %rdi, (%r8) ;;#; Compare mid with target
    je found

    cmpq %rdi, (%r8)
    jl update_left
    ;;#; If value at mid less than target
    subq $1, %r11
    movq %r11, %r12
    jmp loop

    ;;#; If value at mid greater than target
update_left:
    addq $1, %r11
    movq %r11, %r10
    jmp loop

found:
    movq %r11, %rax

exit:
    ;;#; Function Epilogue
    addq $128, %rsp
    popq %rbp
    retq
main:
    ;;#; Function Prologue
    pushq %rbp
    movq %rsp, %rbp
    subq $32, %rsp

    movq $160, %rdi
    callq binary_search

    ;;#; Function Epilogue

    movq %rbp, %rsp
    popq %rbp
    retq
