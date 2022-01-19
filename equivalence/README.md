# Equivalence proof (rbpf = rbpf_dx)

This folder is used to prove the equality between rbpf-coq interpreter and rbpf-coq-dx interpreter. 

*using the make command: `make equivalence`*

**NB: The coq proof checking are time-costing because we must traverse `opcode \in [0,255]` in order to prove the different decoding ways are exactly same.**

The target thoerem is:

```Coq
(**r equivalence.v *)
Theorem equivalence_between_formal_and_dx:
  forall f,
    Semantics.bpf_interpreter f = DxInstructions.bpf_interpreter f.
```
where `f` is a fuel to ensure that the coq functions always terminate.

## Proof idea

1. translating `model/Decode.get_instruction` (match-pattern version) to `switch.get_instruction_if` (if-then-else version), and proving that they are same

```Coq
(**r switch.v *)
Lemma switch_if_same :
  forall (opcode:nat) (rd rs:reg) (ofs: int) (i: int),
    get_instruction opcode rd rs ofs i = get_instruction_if opcode rd rs ofs i.
```

2. proving each opcode of rbpf instructions are less or equal than 255 (because it only has 8-bits) so that if one opcode is greater than 255, we will get a contradiction in the hypothesis, then the rest proof is done!

```Coq
(**r equivalence.v *)
Lemma opcode_le_255 :
  forall st,
    (Z.to_nat (Int64.unsigned
                  (Int64.and (State.eval_ins (State.eval_pc st) st) (Int64.repr 255))))%Z <= 255.
```

3. considering the fact that the main difference between`Semantics.bpf_interpreter/Semantics.bpf_interpreter_aux` and `DxInstructions.bpf_interpreter/DxInstructions.bpf_interpreter_aux` is the `step` function, we prove the follow lemma.
```Coq
Lemma equivalence_between_formal_and_dx_step:
  Semantics.step = DxInstructions.step.
```

- we firstly discuss if opcode is one of the defined instructions, such `add64 dst imm (opcode = 0x07)`; 
- then if we consider all defined instructions, we get the fact, `opcode <> 0x07/0x0f...`; 
- the rest are all undefined instructions, so we traverse `opcode \in [0,255]`, and prove the other case in [0,255] are undefined;
- finally, when `opcode > 255`, we use the lemma `opcode_le_255` to finish the whole proof.
