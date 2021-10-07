# rbpf-dx

A testing project for using dx to transform exam_rbpf in Coq to C

# Test example

Just replacing dx's 'tests/Tests.v' with the 'Tests.v' of this repo.

# Overview

The toy project is to use [dx](https://gitlab.univ-lille.fr/samuel.hym/dx) to generate C code from our toy rBPF interpreter (in Coq).

The toy Coq interpreter consists of:
- src/Type/\*.v: some libraries we may use. (just copy them to the same folder of dx)
- tests/
    - Asm.v: the syntax of rBPF instruciton set, this toy includes NEG, ADD and EXIT.
    - Monad.v: our monad information
    - Sem.v: the semantics part.
    - Interp.v: the rBPF interpreter in Coq.
    - ListOp.v, Int16.v: some necessary libraries.
    - TestMain.v, ExtraMain.v: the existing files of dx
    - Tests.v: we will reuse this file and add our interpreter information!
