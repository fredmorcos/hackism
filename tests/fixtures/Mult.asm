// Multiplies R0 and R1 and stores the result in R2.
// (R0, R1, R2 refer to RAM[0], RAM[1], and RAM[2], respectively.)

        @R2                     // Init the result to 0
        M=0

        (LOOP)
        @R0                     // If R0 == 0 we're done (jump to END)
        D=M
        @END
        D;JEQ

        @R0                     // If not, decrement R0
        M=M-1

        @R1                     // R2 += R1
        D=M
        @R2
        M=D+M

        @LOOP
        0;JMP

        (END)
        @END
        0;JMP
