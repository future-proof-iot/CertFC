# Isolation proof (Certirbpf ensures the sandboxing property)

This folder is used to prove the isolation property of the proof model (rbpf-coq interpreter).

*using the make command: `make isolation`*

There are two target thoerems:

```Coq
(**r Isolation.v *)
Theorem step_preserving_inv:
  forall st1 st2
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hsem: step st1 = Some (tt, st2)),
       register_inv st2 /\ memory_inv st2.
       
Theorem inv_avoid_undef:
  forall st
    (Hreg: register_inv st)
    (Hmem: memory_inv st),
      step st <> None.       
```
where `register_inv` is the register invariant and `memory_inv` is the memory invariant for Certirbpf.

## File struct
- `CommonLib.v`: some common lemmas
- `AlignChunk.v`: some definitions and lemmas about **Memory Aligned**
- `RegsInv.v`: the register invariant and related lemmas
- `MemInv.v`: the memory invariant and related lemmas
- `IsolationLemma.v`: some lemmas used by the proof of the isolation property
- `Isolation.v`: two target thoerems.

## Proof idea

The whole way to prove the theorems are do case discussion on each instruction.

But there is a gap between proof idea and code generation idea: To simulate `Coq List type` correctly, we define `comm/MemType.v/MyMemRegionsType` in Coq, it use List.nth_error to access a list. This way makes the code generation easier but complex the isolation proof. Because we have a list of memory regions `Coq List type`, when we define its invariants, it natually uses native Coq List constructions `nil` and `hd::tl`, but remember we are using `nth\_error` to access the list. So it is hard to do `induction` on the list.

To solve this question, we use the relation among `List.In`, `List.nth_error` and Coq List constructions!
- `inv_memory_regions` is defined by using Coq List constructions
- `In_inv_memory_regions` says the relation between the former and `List.In`
- `IsolationLemma.v` uses the relation with `List.nth_error`, and complete the proof.
```Coq
(**r MemInv.v *)
Fixpoint inv_memory_regions (m:mem) (mrs: list memory_region): Prop :=
  match mrs with
  | [] => True
  | hd :: tl => inv_memory_region m hd /\ inv_memory_regions m tl
  end.

Lemma In_inv_memory_regions:
  forall mr m l,
    List.In mr l -> inv_memory_regions m l ->
      inv_memory_region m mr.
Proof.

(**r IsolationLemma.v L773 & L805 *)

  (**r we rely on the fact if Heqmr get the default memory region, check_mem_aux2P should return Vnullptr! *)
  assert (Hdefault: check_mem_aux2P default_memory_region Readable (Vint vi) chunk = Vnullptr). {
  ...
  
  (**r now we get the evidence `In mr (bpf_mrs st1)`, and reuse the lemma `In_inv_memory_regions` *)
  apply In_inv_memory_regions with (m:=bpf_m st1) in Hin_mem_regions; [| intuition].

```
