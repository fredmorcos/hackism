// Runs an infinite loop that listens to the keyboard input.
// When a key is pressed (any key), the program blackens the screen,
// i.e. writes "black" in every pixel;
// the screen should remain fully black as long as the key is pressed.
// When no key is pressed, the program clears the screen, i.e. writes
// "white" in every pixel;
// the screen should remain fully clear as long as no key is pressed.

        @8192                   // Number of registers to set
        D=A
        @MAX
        M=D

(MAIN_LOOP)
        @KBD                    // Load keyboard status
        D=M
        @WHITE                  // Set color to white if keyboard is unpressed
        D;JEQ
        @BLACK                  // Otherwise, set color to black
        0;JMP

(BLACK)
        @COLOR                  // Set the color to black and jump to the drawing loop
        M=-1
        @START_DRAW_LOOP
        0;JMP

(WHITE)
        @COLOR                  // Set the color to white (and implicitly jump
        M=0                     // to the drawing loop)

(START_DRAW_LOOP)
        @COUNTER                // Initialize counter
        M=-1

(DRAW_LOOP)
        D=1                     // Increment the counter
        @COUNTER
        MD=D+M

        @SCREEN                 // Screen register offset
        D=D+A
        @CURRENT_SCREEN_LOC
        M=D

        @COLOR                  // Load the color
        D=M

        @CURRENT_SCREEN_LOC     // Store the color at the register
        A=M
        M=D

        @MAX                    // Load the max value - 1
        D=M-1

        @COUNTER                // Check if the counter == max - 1
        D=D-M
        @MAIN_LOOP
        D;JEQ                   // Jump to main loop if finished drawing
        @DRAW_LOOP
        0;JMP                   // Otherwise, jump to drawing loop
