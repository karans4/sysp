; tictactoe.s — Tic Tac Toe for Apple II (6502 assembly)
; Assemble: ca65 -o ttt.o tictactoe.s && ld65 -C ttt.cfg -o tictactoe.bin ttt.o
;
; Controls: 1-9 to place piece, any key to restart after game over
; Runs in text mode (40x24). Designed for the sysp Apple II emulator.

.segment "CODE"

; ============================================
; Zero page variables
; ============================================
BOARD   = $00       ; 9 bytes: 0=empty, $58='X', $4F='O'
TURN    = $09       ; 0 = X's turn, 1 = O's turn
STATE   = $0A       ; 0 = playing, 1 = game over
WINNER  = $0B       ; 0 = draw, $58 = X won, $4F = O won
SCRLO   = $F0       ; screen pointer lo
SCRHI   = $F1       ; screen pointer hi
SRCLO   = $F2       ; string source lo
SRCHI   = $F3       ; string source hi
TMPA    = $F4       ; temp storage

; I/O
KBD     = $C000
KBDSTRB = $C010

; ============================================
; Entry point
; ============================================
START:
    jsr INIT
    jsr DRAWALL

MAINLOOP:
    lda KBD
    bpl MAINLOOP        ; bit 7 clear = no key
    and #$7F            ; strip high bit -> ASCII
    pha
    bit KBDSTRB         ; clear keyboard strobe (any access to $C010)
    pla

    ; If game over, any key restarts
    ldx STATE
    beq @playing
    jsr INIT
    jsr DRAWALL
    jmp MAINLOOP

@playing:
    ; Convert '1'-'9' to cell index 0-8
    sec
    sbc #$31            ; '1' = $31
    bcc MAINLOOP        ; below '1'
    cmp #9
    bcs MAINLOOP        ; above '9'

    ; A = cell index. Check if empty.
    tax
    lda BOARD,x
    bne MAINLOOP        ; occupied

    ; Place piece
    lda TURN
    beq @placeX
    lda #$4F            ; 'O'
    jmp @store
@placeX:
    lda #$58            ; 'X'
@store:
    sta BOARD,x

    ; Check win
    jsr CHECKWIN
    lda WINNER
    bne @gameover

    ; Check draw
    jsr CHECKDRAW
    lda STATE
    bne @gameover

    ; Toggle turn
    lda TURN
    eor #1
    sta TURN

@gameover:
    jsr DRAWALL
    jmp MAINLOOP

; ============================================
; INIT — reset game state
; ============================================
INIT:
    ldx #8
@clr:
    lda #0
    sta BOARD,x
    dex
    bpl @clr
    sta TURN
    sta STATE
    sta WINNER
    rts

; ============================================
; CHECKWIN — test 8 win lines
; ============================================
CHECKWIN:
    ldx #0
@line:
    ldy WINLINES,x
    lda BOARD,y
    beq @next           ; empty cell
    ldy WINLINES+1,x
    cmp BOARD,y
    bne @next
    ldy WINLINES+2,x
    cmp BOARD,y
    bne @next
    ; Found winner!
    sta WINNER
    lda #1
    sta STATE
    rts
@next:
    inx
    inx
    inx
    cpx #24             ; 8 lines * 3
    bcc @line
    rts

; ============================================
; CHECKDRAW — board full = draw
; ============================================
CHECKDRAW:
    ldx #0
@cell:
    lda BOARD,x
    beq @nope           ; empty cell found
    inx
    cpx #9
    bcc @cell
    ; All full, no winner
    lda #1
    sta STATE
    rts
@nope:
    rts

; ============================================
; CLEARSCR — fill screen with spaces
; ============================================
CLEARSCR:
    lda #$A0            ; space (normal mode: $20 | $80)
    ldx #0
@fill:
    sta $0400,x
    sta $0500,x
    sta $0600,x
    sta $0700,x
    inx
    bne @fill
    rts

; ============================================
; DRAWCHAR — write char to screen
;   A = character, X = row (0-23), Y = col (0-39)
; ============================================
DRAWCHAR:
    pha
    lda ROWLO,x
    sta SCRLO
    lda ROWHI,x
    sta SCRHI
    pla
    ora #$80            ; Apple II normal mode: set high bit
    sta (SCRLO),y
    rts

; ============================================
; DRAWSTR — draw null-terminated string
;   SRCLO/SRCHI = string ptr, X = row, Y = start col
; ============================================
DRAWSTR:
    sty TMPA
    lda ROWLO,x
    clc
    adc TMPA
    sta SCRLO
    lda ROWHI,x
    adc #0
    sta SCRHI
    ldy #0
@ch:
    lda (SRCLO),y
    beq @done
    ora #$80            ; Apple II normal mode: set high bit
    sta (SCRLO),y
    iny
    bne @ch
@done:
    rts

; ============================================
; DRAWALL — full screen redraw
; ============================================
DRAWALL:
    jsr CLEARSCR

    ; --- Title on row 1 ---
    lda #<STR_TITLE
    sta SRCLO
    lda #>STR_TITLE
    sta SRCHI
    ldx #1
    ldy #12
    jsr DRAWSTR

    ; --- Grid separator rows 6 and 10 ---
    lda #<STR_SEP
    sta SRCLO
    lda #>STR_SEP
    sta SRCHI
    ldx #6
    ldy #7
    jsr DRAWSTR

    lda #<STR_SEP
    sta SRCLO
    lda #>STR_SEP
    sta SRCHI
    ldx #10
    ldy #7
    jsr DRAWSTR

    ; --- Vertical bars ---
    ; Rows 3,4,5 / 7,8,9 / 11,12,13 at cols 15 and 24
    ldx #3
    jsr DRAWVBARS
    ldx #7
    jsr DRAWVBARS
    ldx #11
    jsr DRAWVBARS

    ; --- Cell contents (pieces or numbers) ---
    ldx #0
@cells:
    stx TMPA
    lda BOARD,x
    bne @piece
    ; Empty: show cell number
    ldx TMPA
    lda CELLNUM,x
    jmp @draw
@piece:
    ; A has 'X' or 'O'
@draw:
    pha
    ldx TMPA
    lda CELLROW,x
    tax                 ; X = screen row
    ldy TMPA
    lda CELLCOL,y
    tay                 ; Y = screen col
    pla                 ; A = char
    jsr DRAWCHAR

    ldx TMPA
    inx
    cpx #9
    bcc @cells

    ; --- Status line (row 16) ---
    lda STATE
    bne @over

    ; Playing: show whose turn
    lda TURN
    bne @oturn
    lda #<STR_XTURN
    sta SRCLO
    lda #>STR_XTURN
    sta SRCHI
    jmp @showstat
@oturn:
    lda #<STR_OTURN
    sta SRCLO
    lda #>STR_OTURN
    sta SRCHI
    jmp @showstat

@over:
    lda WINNER
    cmp #$58            ; 'X'
    bne @notx
    lda #<STR_XWINS
    sta SRCLO
    lda #>STR_XWINS
    sta SRCHI
    jmp @showstat
@notx:
    cmp #$4F            ; 'O'
    bne @isdraw
    lda #<STR_OWINS
    sta SRCLO
    lda #>STR_OWINS
    sta SRCHI
    jmp @showstat
@isdraw:
    lda #<STR_DRAW
    sta SRCLO
    lda #>STR_DRAW
    sta SRCHI

@showstat:
    ldx #16
    ldy #12
    jsr DRAWSTR

    ; --- Instructions (row 18) ---
    lda STATE
    bne @restart
    lda #<STR_PRESS
    sta SRCLO
    lda #>STR_PRESS
    sta SRCHI
    jmp @showinst
@restart:
    lda #<STR_RESTART
    sta SRCLO
    lda #>STR_RESTART
    sta SRCHI
@showinst:
    ldx #18
    ldy #8
    jsr DRAWSTR

    rts

; ============================================
; DRAWVBARS — draw | at cols 15 and 24 for 3 rows
;   X = starting row
; ============================================
DRAWVBARS:
    lda #$7C            ; '|'
    ldy #15
    jsr DRAWCHAR
    ldy #24
    jsr DRAWCHAR
    inx
    ldy #15
    jsr DRAWCHAR
    ldy #24
    jsr DRAWCHAR
    inx
    ldy #15
    jsr DRAWCHAR
    ldy #24
    jsr DRAWCHAR
    rts

; ============================================
; Data tables
; ============================================

; Screen row base addresses (Apple II text page 1)
ROWLO:
    .byte $00,$80,$00,$80,$00,$80,$00,$80
    .byte $28,$A8,$28,$A8,$28,$A8,$28,$A8
    .byte $50,$D0,$50,$D0,$50,$D0,$50,$D0
ROWHI:
    .byte $04,$04,$05,$05,$06,$06,$07,$07
    .byte $04,$04,$05,$05,$06,$06,$07,$07
    .byte $04,$04,$05,$05,$06,$06,$07,$07

; Cell screen positions
CELLROW: .byte 4,  4,  4,  8,  8,  8,  12, 12, 12
CELLCOL: .byte 11, 19, 28, 11, 19, 28, 11, 19, 28

; Cell number chars for empty cells
CELLNUM: .byte $31,$32,$33,$34,$35,$36,$37,$38,$39  ; '1'-'9'

; Win line triples (cell indices)
WINLINES:
    .byte 0,1,2        ; row 0
    .byte 3,4,5        ; row 1
    .byte 6,7,8        ; row 2
    .byte 0,3,6        ; col 0
    .byte 1,4,7        ; col 1
    .byte 2,5,8        ; col 2
    .byte 0,4,8        ; diagonal
    .byte 2,4,6        ; anti-diagonal

; Strings
STR_TITLE:   .byte "TIC-TAC-TOE", 0
STR_SEP:     .byte "--------+--------+--------", 0
STR_XTURN:   .byte "X'S TURN", 0
STR_OTURN:   .byte "O'S TURN", 0
STR_XWINS:   .byte "X WINS!", 0
STR_OWINS:   .byte "O WINS!", 0
STR_DRAW:    .byte "DRAW!", 0
STR_PRESS:   .byte "PRESS 1-9 TO PLAY", 0
STR_RESTART: .byte "ANY KEY TO RESTART", 0
