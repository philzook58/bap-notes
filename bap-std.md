

https://github.com/ivg/bap/blob/master/lib/bap/bap.mli

# Image
I don't really know what this is

# Loader
I don't really know what this is

# Disassembler
Dark magic here.

# BIR Terms
BIR is a control flow graph like representation that I have found most useful and intuitive for things I want to do.

Some very useful functionality common to all the terms is found in the Term module

- `Term.enum blk_t sub` - Basically how you traverse down through terms. You can also use a visitor pattern, but I don't really know how to do this.
- `Term.find`

The meat and potatos
- Sub. `Sub.ssa` is an interesting function
- Blk
- Def. `Def.lhs` `Def.rhs`
- Jmp

Eh:
- Phi

# Variables
Bap has a pretty nice implementation of variables. Lots of nice little functionality here.

# Expressions

