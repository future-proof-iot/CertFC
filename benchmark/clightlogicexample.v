From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "clightlogicexample.c".
  Definition normalized := false.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _block_perm : ident := $"block_perm".
Definition _block_ptr : ident := $"block_ptr".
Definition _block_size : ident := $"block_size".
Definition _bpf_flag : ident := $"bpf_flag".
Definition _bpf_state : ident := $"bpf_state".
Definition _calc_sum : ident := $"calc_sum".
Definition _chunk : ident := $"chunk".
Definition _dst : ident := $"dst".
Definition _eval_mem_regions : ident := $"eval_mem_regions".
Definition _f : ident := $"f".
Definition _get_add : ident := $"get_add".
Definition _get_addr_ofs : ident := $"get_addr_ofs".
Definition _get_immediate : ident := $"get_immediate".
Definition _get_mem_region : ident := $"get_mem_region".
Definition _get_opcode_mem_ld_imm : ident := $"get_opcode_mem_ld_imm".
Definition _i : ident := $"i".
Definition _idx : ident := $"idx".
Definition _imm : ident := $"imm".
Definition _ins : ident := $"ins".
Definition _is_well_chunk_bool : ident := $"is_well_chunk_bool".
Definition _l : ident := $"l".
Definition _len : ident := $"len".
Definition _list_get : ident := $"list_get".
Definition _main : ident := $"main".
Definition _mem_num : ident := $"mem_num".
Definition _memory_region : ident := $"memory_region".
Definition _mrs : ident := $"mrs".
Definition _n : ident := $"n".
Definition _n1 : ident := $"n1".
Definition _next_imm : ident := $"next_imm".
Definition _next_ins : ident := $"next_ins".
Definition _nv : ident := $"nv".
Definition _ofs : ident := $"ofs".
Definition _op : ident := $"op".
Definition _opcode_ld : ident := $"opcode_ld".
Definition _pc : ident := $"pc".
Definition _regsmap : ident := $"regsmap".
Definition _st : ident := $"st".
Definition _start_addr : ident := $"start_addr".
Definition _state_pc : ident := $"state_pc".
Definition _step_opcode_mem_ld_imm : ident := $"step_opcode_mem_ld_imm".
Definition _upd_flag : ident := $"upd_flag".
Definition _upd_pc_incr : ident := $"upd_pc_incr".
Definition _upd_reg : ident := $"upd_reg".
Definition _v : ident := $"v".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition f_upd_pc_incr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
        (Tstruct _bpf_state noattr)) _state_pc tuint)
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _state_pc tuint)
      (Econst_int (Int.repr 1) tint) tuint))
  (Sreturn None))
|}.

Definition f_upd_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_i, tuint) ::
                (_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
            (Tstruct _bpf_state noattr)) _regsmap (tarray tulong 11))
        (Etempvar _i tuint) (tptr tulong)) tulong) (Etempvar _v tulong))
  (Sreturn None))
|}.

Definition f_upd_flag := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_f, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
        (Tstruct _bpf_state noattr)) _bpf_flag tint) (Etempvar _f tint))
  (Sreturn None))
|}.

Definition f_eval_mem_regions := {|
  fn_return := (tptr (Tstruct _memory_region noattr));
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                   (Tstruct _bpf_state noattr)) _mrs
                 (tptr (Tstruct _memory_region noattr)))))
|}.

Definition f_list_get := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr tulong)) :: (_idx, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd (Etempvar _l (tptr tulong))
                   (Etempvar _idx tint) (tptr tulong)) tulong)))
|}.

Definition f_get_mem_region := {|
  fn_return := (tptr (Tstruct _memory_region noattr));
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_n, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_mrs, (tptr (Tstruct _memory_region noattr))) ::
               (_t'1, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_mem_regions (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  Tnil)
                                (tptr (Tstruct _memory_region noattr))
                                cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
    (Sset _mrs (Etempvar _t'1 (tptr (Tstruct _memory_region noattr)))))
  (Sreturn (Some (Ebinop Oadd
                   (Etempvar _mrs (tptr (Tstruct _memory_region noattr)))
                   (Etempvar _n tuint)
                   (tptr (Tstruct _memory_region noattr))))))
|}.

Definition f_get_immediate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr (Etempvar _ins tulong)
                   (Econst_long (Int64.repr 32) tulong) tulong) tint)))
|}.

Definition f_get_opcode_mem_ld_imm := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 255) tint) tint) tuchar)))
|}.

Definition f_get_add := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_y, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _x tuint) (Etempvar _y tuint) tuint)))
|}.

Definition f_get_addr_ofs := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_ofs, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oadd (Etempvar _x tulong)
                   (Ecast (Etempvar _ofs tint) tulong) tulong) tuint)))
|}.

Definition f_is_well_chunk_bool := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_chunk, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk tuint)
  (LScons (Some 1)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (LScons (Some 2)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      (LScons (Some 4)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
        (LScons (Some 8)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          (LScons None (Sreturn (Some (Econst_int (Int.repr 0) tint))) LSnil))))))
|}.

Definition f_calc_sum := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n1, tuint) :: (_nv, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _n tuint) (Econst_int (Int.repr 0) tuint)
               tint)
  (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
  (Ssequence
    (Sset _n1
      (Ebinop Osub (Etempvar _n tuint) (Econst_int (Int.repr 1) tuint) tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_add (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                           cc_default))
          ((Etempvar _v tuint) :: (Econst_int (Int.repr 1) tuint) :: nil))
        (Sset _nv (Etempvar _t'1 tuint)))
      (Ssequence
        (Scall (Some _t'2)
          (Evar _calc_sum (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                            cc_default))
          ((Etempvar _nv tuint) :: (Etempvar _n1 tuint) :: nil))
        (Sreturn (Some (Etempvar _t'2 tuint)))))))
|}.

Definition f_step_opcode_mem_ld_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_imm, tint) ::
                (_pc, tint) :: (_len, tint) :: (_dst, tuint) ::
                (_op, tuchar) :: (_l, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_ld, tuchar) :: (_next_ins, tulong) ::
               (_next_imm, tint) :: (_t'3, tint) :: (_t'2, tulong) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_ld_imm (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_ld (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_ld tuchar)
    (LScons (Some 24)
      (Sifthenelse (Ebinop Olt
                     (Ebinop Oadd (Etempvar _pc tint)
                       (Econst_int (Int.repr 1) tint) tint)
                     (Etempvar _len tint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _list_get (Tfunction
                                (Tcons (tptr tulong) (Tcons tint Tnil))
                                tulong cc_default))
              ((Etempvar _l (tptr tulong)) ::
               (Ebinop Oadd (Etempvar _pc tint)
                 (Econst_int (Int.repr 1) tint) tint) :: nil))
            (Sset _next_ins (Etempvar _t'2 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _get_immediate (Tfunction (Tcons tulong Tnil) tint
                                       cc_default))
                ((Etempvar _next_ins tulong) :: nil))
              (Sset _next_imm (Etempvar _t'3 tint)))
            (Ssequence
              (Scall None
                (Evar _upd_reg (Tfunction
                                 (Tcons (tptr (Tstruct _bpf_state noattr))
                                   (Tcons tuint (Tcons tulong Tnil))) tvoid
                                 cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Etempvar _dst tuint) ::
                 (Ebinop Oor
                   (Ecast (Ecast (Etempvar _imm tint) tuint) tulong)
                   (Ebinop Oshl
                     (Ecast (Ecast (Etempvar _next_imm tint) tuint) tulong)
                     (Econst_int (Int.repr 32) tuint) tulong) tulong) :: nil))
              (Ssequence
                (Scall None
                  (Evar _upd_pc_incr (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _bpf_state noattr))
                                         Tnil) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None))))))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Eunop Oneg (Econst_int (Int.repr 5) tint) tint) :: nil))
          (Sreturn None)))
      (LScons None
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
          (Sreturn None))
        LSnil))))
|}.

Definition composites : list composite_definition :=
(Composite _memory_region Struct
   ((_start_addr, tuint) :: (_block_size, tuint) :: (_block_perm, tuint) ::
    (_block_ptr, tuint) :: nil)
   noattr ::
 Composite _bpf_state Struct
   ((_state_pc, tuint) :: (_bpf_flag, tint) :: (_mem_num, tuint) ::
    (_regsmap, (tarray tulong 11)) ::
    (_mrs, (tptr (Tstruct _memory_region noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_upd_pc_incr, Gfun(Internal f_upd_pc_incr)) ::
 (_upd_reg, Gfun(Internal f_upd_reg)) ::
 (_upd_flag, Gfun(Internal f_upd_flag)) ::
 (_eval_mem_regions, Gfun(Internal f_eval_mem_regions)) ::
 (_list_get, Gfun(Internal f_list_get)) ::
 (_get_mem_region, Gfun(Internal f_get_mem_region)) ::
 (_get_immediate, Gfun(Internal f_get_immediate)) ::
 (_get_opcode_mem_ld_imm, Gfun(Internal f_get_opcode_mem_ld_imm)) ::
 (_get_add, Gfun(Internal f_get_add)) ::
 (_get_addr_ofs, Gfun(Internal f_get_addr_ofs)) ::
 (_is_well_chunk_bool, Gfun(Internal f_is_well_chunk_bool)) ::
 (_calc_sum, Gfun(Internal f_calc_sum)) ::
 (_step_opcode_mem_ld_imm, Gfun(Internal f_step_opcode_mem_ld_imm)) :: nil).

Definition public_idents : list ident :=
(_step_opcode_mem_ld_imm :: _calc_sum :: _is_well_chunk_bool ::
 _get_addr_ofs :: _get_add :: _get_opcode_mem_ld_imm :: _get_immediate ::
 _get_mem_region :: _list_get :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


