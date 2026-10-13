.text
// 每条指令单独执行；验证寄存器重叠、宽度、访存和标志。
mov w0, w1
mov x0, x1
add w0, w1, w2
subs w0, w1, w2
adds x0, x1, x2
cmp w1, w2
cmn x1, x2
tst w1, w2
and w0, w1, #255
orr x0, x1, x2
eor x0, x1, x2
add x0, x1, x2, lsl #3
add x0, x1, x2, lsr #3
add x0, x1, x2, asr #3
add x0, x1, w2, sxtw #2
lsr w0, w1, #8
asr x0, x1, #8
cset w0, eq
cset w0, lt
csel w0, w1, w2, ne
fmov s0, w1
fmov w0, s1
fmov d0, x1
fmov x0, d1
fmov s0, #1.0
fdiv s0, s1, s2
frintp d0, d1
scvtf s0, w1
fcvtps w0, s1
fcmp s1, s2
ldr w0, [x3, #4]
ldrb w0, [x3, #1]
ldrh w0, [x3, #2]
ldrsw x0, [x3, #4]
ldr s0, [x3, #4]
ldr d0, [x3, #8]
ldr q0, [x3, #16]
strb w1, [x3, #1]
strh w1, [x3, #2]
str x1, [x3, #8]
stp x1, x2, [sp, #-16]!
ldp x0, x1, [sp], #16
stp w1, w2, [x3, #8]!
ldp w0, w1, [x3], #8
ldr x0, [x3, x4, lsl #3]
str w1, [x3, w4, sxtw #2]
add x0, x29, #8
