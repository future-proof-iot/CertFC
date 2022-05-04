# Link the coq development to CAV22 paper
The markdown file is used to explain how to link the CertrBPF coq repo with CAV22 paper:
- we first have two repo: [The latest version (202205)](https://gitlab.inria.fr/syuan/rbpf-dx/-/tree/CAV22-AE) v.s. [the initial version (202001)](https://anonymous.4open.science/r/AnonymousCAV22-59DC). This file focuses on the former, the latter is the version when submitting the initial CAV22 manuscript. 
- we also have two pdf: The latest version (202205) and the initial version (202001). This file focuses on the former, NB the latest version is not the camera-ready version.

We will explain each concept/definition/theorems/code appearing in the latest pdf.
Let's go~

# Monad
In the section `A generic method for end-to-end verification in Coq`, we use the standard option-state monad `M`, its [coq definition](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/comm/Monad.v):
```coq
Definition M (St: Type) (A: Type) := St -> option (A * St).

Definition returnM {A: Type} {St: Type} (a: A) : M St A := fun st => Some (a, st).
Definition bindM {A B: Type} {St: Type} (x: M St A) (f: A -> M St B) : M St B :=
...
```

# Proof Model

In the section `A proof-oriented virtual machine model`:
- syntax (i.e. `Fig. 2: Core syntax of rBPF instruction set`), the [corresponding coq code](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/model/Syntax.v)
```coq
Inductive instruction: Type :=
  (**r ALU64/32*)
  | BPF_NEG    : arch -> reg -> instruction
  | BPF_BINARY : arch -> binOp -> reg -> reg+imm -> instruction
  (**r Branch *)
   ...
```
- state : the [corresponding coq code](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/comm/State.v) *NB: the coq definition has additional `mrs_num` and `ins_len` which is not necessary for Coq (we could use List.length to get them) but is necessary for C definition*
```coq
Record state := mkst {
  pc_loc  : int;
  flag    : bpf_flag;
  regs_st : regmap;
  mrs_num : nat;
  bpf_mrs : MyMemRegionsType;
  ins_len : nat;
  ins     : MyListType;
  bpf_m   : Memory.mem;
}.
```
- dynamic checks: `check_alu` and `check_mem`,their [coq code](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/model/Semantics.v)
```
(**r check_alu is an abstract function, consists of : comp_ne_32, etc *)
    match bop with
    | BPF_ADD  => upd_reg d (Val.longofintu (Val.add  d32 s32))
    | BPF_SUB  => upd_reg d (Val.longofintu (Val.sub  d32 s32))
    | BPF_MUL  => upd_reg d (Val.longofintu (Val.mul  d32 s32))
    | BPF_DIV  => if comp_ne_32 s32 Vzero then (** run-time checking *)
                    match Val.divu d32 s32 with (**r Val.divu... *)
                    | Some res => upd_reg d (Val.longofintu res)
                    | None     => errorM
                    end
                  else
                    upd_flag BPF_ILLEGAL_DIV
   ...
(**r check_mem function is here *)
Definition check_mem (perm: permission) (chunk: memory_chunk) (addr: val): M state val :=
  do well_chunk <- is_well_chunk_bool chunk; ...
```
- semantics & interpreter: [coq code](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/model/Semantics.v)
```coq
Definition step : M state unit := ...
    match ins with
    | BPF_NEG a d => ...
    | BPF_BINARY a bop d s => ...
    | BPF_JA ofs => upd_pc (Int.add pc ofs)
    | BPF_JUMP c d s ofs => ...

Definition bpf_interpreter (fuel: nat): M state val := ...
```
- invairants
  + `register_inv`: the [coq file](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/isolation/RegsInv.v)
```coq
Definition register_inv (st: state): Prop :=
  is_vlong (r0_val  (regs_st st)) /\
   ...
```
  + `memory_inv`: [the code](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/isolation/MemInv.v) 
```coq
Definition inv_memory_region (m:mem) (mr: memory_region): Prop :=
  exists b,
    (block_ptr mr) = Vptr b Ptrofs.zero /\ Mem.valid_block m b /\ is_byte_block b m /\
    exists base len,
      start_addr mr = Vint base /\ block_size mr = Vint len /\
      perm_order (block_perm mr) Readable /\
      Mem.range_perm m b 0 (Int.unsigned len) Cur (block_perm mr).

Definition memory_inv (st: state): Prop :=
  (1 <= mrs_num st)%nat /\
  List.length (bpf_mrs st) = mrs_num st /\
  (exists start_blk,
    disjoint_blocks start_blk (bpf_mrs st)) /\
  inv_memory_regions (bpf_m st) (bpf_mrs st).
```
  + `verifier_inv`: the [states including relation](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/isolation/StateInv.v) and [verifier_inv](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/isolation/VerifierInv.v)
```coq
Definition state_inv (st1 st2: state): Prop :=
  mrs_num st1 = mrs_num st2 /\
  bpf_mrs st1 = bpf_mrs st2 /\
  ins_len st1 = ins_len st2 /\
  ins     st1 = ins     st2.

Definition state_include (st: state.state) (ST: State.state): Prop :=
  state.ins_len st = State.ins_len ST /\ state.ins st = State.ins ST.

Definition bpf_verifier (st: state.state): bool :=
  let len := ins_len st in ..
```
- isolation: the two theorems [sem_preserve_inv](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/isolation/Isolation1.v) (*NB: we prove a wearker assumption currently i.e. `state_include` instead of `verifier_inv` in Coq*) and [inv_ensure_no_undef](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/isolation/Isolation2.v)
```coq
Theorem bpf_interpreter_preserving_inv:
  forall st fuel st1 st2 t
    (Hreg: register_inv st1)
    (Hmem: memory_inv st1)
    (Hst0 : state_include st st1)
    (Hsem: bpf_interpreter fuel st1 = Some (t, st2)),
       register_inv st2 /\ memory_inv st2 /\ state_include st st2.
Proof.

Theorem inv_avoid_bpf_interpreter_undef:
  forall st f st0
    (Hreg: register_inv st)
    (Hmem: memory_inv st)
    (Hlen: ins_len st = length (ins st))
    (Hlen_max: (length (ins st) <= Z.to_nat Ptrofs.max_unsigned)%nat)
    (Hst0: state_include st0 st)
    (Hver: bpf_verifier st0 = true),
      bpf_interpreter f st <> None.
Proof.
...
```
# Synthesis Model

In the section `A synthesis-oriented eBPF interpreter`:
- syntehsis model: see the [coq file](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/monadicmodel/rBPFInterpreter.v)
```coq
Definition bpf_interpreter (fuel: nat): M state val :=
...
```
- dx configuration: see the last [coq file](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/dxmodel/DxInstructions.v) which relies on many dx configruation files e.g. 
`DxIntegers DxValues DxList64 DxNat`
```coq

(**In the paper: step_mem_st_reg *)
Definition step_opcode_mem_st_reg (src64: val64_t) (addr: valu32_t) (dst: reg) (op: nat8): M unit :=
  do opcode_st <-- get_opcode_mem_st_reg op;
  ...

Definition bpf_interpreter (fuel: nat): M val64_t :=
```
- equivalence theorem: we prove the equivalence among the proof/synthesis/dx model
```coq
(**r https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/equivalence/equivalence1.v *)
Theorem equivalence_between_formal_and_dx:
  forall f,
    Semantics.bpf_interpreter f = rBPFInterpreter.bpf_interpreter f.
Proof.

(**r https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/equivalence/equivalence2.v *)
Lemma equivalence_between_coq_and_dx_aux:
  forall f,
    rBPFInterpreter.bpf_interpreter_aux f = DxInstructions.bpf_interpreter_aux f.
Proof.
```

- the extracted & executable C code: see [here](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/clight/interpreter.c) (*NB: from extracted C to executable, a repatching process is necessary, see [here](https://gitlab.inria.fr/syuan/rbpf-dx/-/tree/CAV22-AE/repatch) *)

# Simulation Proof
In the section `Simulation Proof of the C rBPF Virtual Machine`:

- Clight model: see [the coq file](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/clight/interpreter.v)
- simulation relation: the Figure `Simulation relation R between strbpf , left, and rBPFClight, right.` please see the [definition](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/simulation/MatchState.v)
```coq

  Record match_state  (st: State.state) (m: mem) : Prop :=
    {
      munchange: Mem.unchanged_on (fun b _ => b <> st_blk /\ b <> mrs_blk /\ b <> ins_blk) (bpf_m st) m; (**r (bpf_m st) = m - {state_blk, mrs_blk, ins_blk} *)
      mpc      : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 0)) = Some (Vint  (pc_loc st));
      mflags   : Mem.loadv AST.Mint32 m (Vptr st_blk (Ptrofs.repr 4)) = Some (Vint  (int_of_flag (flag st))); ...
    }.

```

- clightlogic: see the [file](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/clightlogic/Clightlogic.v), Theorem 4 is formalized in Coq:
```coq
  Class correct_function (a: DList.t (fun x => x) args) :=
    mk_correct_function3
      {
        fn_eval_ok3 : forall (st:St),
          match cl_app (r:=M St res) f  a st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall (lval: DList.t (fun _ => val) (all_args  args is_pure)) k m
                (MS : match_state st m),
                (* they satisfy the pre-condition *)
                DList.Forall2 (fun (a:Type) (R: a -> Inv St) (X:a * val) => eval_inv (R (fst X)) (snd X) st m)
                              match_arg_list (DList.zip  (all_args_list args is_pure a ) lval) ->
                (* We prove that we can reach a return state *)
                Forall2 (fun v t => Cop.val_casted v (snd t)) (DList.to_list (fun _ v => v) lval) (fn_params fn) ->

                exists v m' t,
                Star (Clight.semantics2 p) (Callstate  (Ctypes.Internal fn)
                                                       (DList.to_list (fun x v => v) lval)  k m) t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  eval_inv (match_res  v') v st' m' /\ Cop.val_casted v (fn_return fn) /\
                  unmodifies_effect modifies m m' st st' /\
                  match_state st' m'
              end
      }.

```
And for each Coq function (and corresponding Clight code). we have a simulation proof instance, the top function `bpf_interpreter`'s proof instance is [here](https://gitlab.inria.fr/syuan/rbpf-dx/-/blob/CAV22-AE/simulation/correct_bpf_interpreter.v) 
```coq
  Instance correct_function_bpf_interpreter : forall a, correct_function _ p args res f fn ModSomething false match_state match_arg_list match_res a.
  Proof.
  ...
```
