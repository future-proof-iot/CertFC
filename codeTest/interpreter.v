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
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "interpreter.c".
  Definition normalized := false.
End Info.

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
Definition _addr : ident := $"addr".
Definition _addr0 : ident := $"addr0".
Definition _addr1 : ident := $"addr1".
Definition _addr_dst : ident := $"addr_dst".
Definition _addr_src : ident := $"addr_src".
Definition _block_size : ident := $"block_size".
Definition _bpf_ctx : ident := $"bpf_ctx".
Definition _bpf_flag : ident := $"bpf_flag".
Definition _bpf_interpreter : ident := $"bpf_interpreter".
Definition _bpf_interpreter_aux : ident := $"bpf_interpreter_aux".
Definition _bpf_state : ident := $"bpf_state".
Definition _bpf_stk : ident := $"bpf_stk".
Definition _check_ldxb : ident := $"check_ldxb".
Definition _check_ldxdw : ident := $"check_ldxdw".
Definition _check_ldxh : ident := $"check_ldxh".
Definition _check_ldxw : ident := $"check_ldxw".
Definition _check_mem : ident := $"check_mem".
Definition _check_mem_aux : ident := $"check_mem_aux".
Definition _check_mem_content : ident := $"check_mem_content".
Definition _check_mem_ctx : ident := $"check_mem_ctx".
Definition _check_mem_stk : ident := $"check_mem_stk".
Definition _check_stb : ident := $"check_stb".
Definition _check_stdw : ident := $"check_stdw".
Definition _check_sth : ident := $"check_sth".
Definition _check_stw : ident := $"check_stw".
Definition _check_stxb : ident := $"check_stxb".
Definition _check_stxdw : ident := $"check_stxdw".
Definition _check_stxh : ident := $"check_stxh".
Definition _check_stxw : ident := $"check_stxw".
Definition _chunk : ident := $"chunk".
Definition _chunk0 : ident := $"chunk0".
Definition _chunk1 : ident := $"chunk1".
Definition _chunk2 : ident := $"chunk2".
Definition _content : ident := $"content".
Definition _dst : ident := $"dst".
Definition _dst64 : ident := $"dst64".
Definition _eval_flag : ident := $"eval_flag".
Definition _eval_pc : ident := $"eval_pc".
Definition _eval_reg : ident := $"eval_reg".
Definition _f : ident := $"f".
Definition _f1 : ident := $"f1".
Definition _f2 : ident := $"f2".
Definition _fuel0 : ident := $"fuel0".
Definition _fuel1 : ident := $"fuel1".
Definition _fuel2 : ident := $"fuel2".
Definition _getMemRegion_block_ptr : ident := $"getMemRegion_block_ptr".
Definition _getMemRegion_block_size : ident := $"getMemRegion_block_size".
Definition _getMemRegion_start_addr : ident := $"getMemRegion_start_addr".
Definition _get_addl : ident := $"get_addl".
Definition _get_dst : ident := $"get_dst".
Definition _get_immediate : ident := $"get_immediate".
Definition _get_offset : ident := $"get_offset".
Definition _get_opcode : ident := $"get_opcode".
Definition _get_src : ident := $"get_src".
Definition _get_subl : ident := $"get_subl".
Definition _hi_ofs : ident := $"hi_ofs".
Definition _i : ident := $"i".
Definition _i0 : ident := $"i0".
Definition _i1 : ident := $"i1".
Definition _idx0 : ident := $"idx0".
Definition _imm : ident := $"imm".
Definition _ins : ident := $"ins".
Definition _ins0 : ident := $"ins0".
Definition _ins1 : ident := $"ins1".
Definition _ins2 : ident := $"ins2".
Definition _is_well_chunk_bool : ident := $"is_well_chunk_bool".
Definition _l : ident := $"l".
Definition _l0 : ident := $"l0".
Definition _l1 : ident := $"l1".
Definition _l2 : ident := $"l2".
Definition _len0 : ident := $"len0".
Definition _len1 : ident := $"len1".
Definition _len2 : ident := $"len2".
Definition _list_get : ident := $"list_get".
Definition _lo_ofs : ident := $"lo_ofs".
Definition _load_mem : ident := $"load_mem".
Definition _main : ident := $"main".
Definition _memory_region : ident := $"memory_region".
Definition _memory_regions : ident := $"memory_regions".
Definition _mr0 : ident := $"mr0".
Definition _mr1 : ident := $"mr1".
Definition _mr2 : ident := $"mr2".
Definition _mr3 : ident := $"mr3".
Definition _mrs : ident := $"mrs".
Definition _mrs4 : ident := $"mrs4".
Definition _next_imm : ident := $"next_imm".
Definition _next_ins : ident := $"next_ins".
Definition _ofs : ident := $"ofs".
Definition _op : ident := $"op".
Definition _pc : ident := $"pc".
Definition _pc1 : ident := $"pc1".
Definition _ptr : ident := $"ptr".
Definition _regsmap : ident := $"regsmap".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _src64 : ident := $"src64".
Definition _st : ident := $"st".
Definition _start : ident := $"start".
Definition _start_addr : ident := $"start_addr".
Definition _state_pc : ident := $"state_pc".
Definition _step : ident := $"step".
Definition _store_mem_imm : ident := $"store_mem_imm".
Definition _store_mem_reg : ident := $"store_mem_reg".
Definition _upd_flag : ident := $"upd_flag".
Definition _upd_pc : ident := $"upd_pc".
Definition _upd_pc_incr : ident := $"upd_pc_incr".
Definition _upd_reg : ident := $"upd_reg".
Definition _v : ident := $"v".
Definition _v_xb : ident := $"v_xb".
Definition _v_xdw : ident := $"v_xdw".
Definition _v_xh : ident := $"v_xh".
Definition _v_xw : ident := $"v_xw".
Definition _well_chunk : ident := $"well_chunk".
Definition _x : ident := $"x".
Definition _x1 : ident := $"x1".
Definition _y : ident := $"y".
Definition _y1 : ident := $"y1".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_eval_pc := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                   (Tstruct _bpf_state noattr)) _state_pc tulong)))
|}.

Definition f_upd_pc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_pc, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
        (Tstruct _bpf_state noattr)) _state_pc tulong) (Etempvar _pc tulong))
  (Sreturn None))
|}.

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
        (Tstruct _bpf_state noattr)) _state_pc tulong)
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _state_pc tulong)
      (Econst_int (Int.repr 1) tint) tulong))
  (Sreturn None))
|}.

Definition f_eval_reg := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_i, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr 11) tint)
               tint)
  (Sreturn (Some (Ederef
                   (Ebinop Oadd
                     (Efield
                       (Ederef
                         (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                         (Tstruct _bpf_state noattr)) _regsmap
                       (tarray tulong 11)) (Etempvar _i tuint) (tptr tulong))
                   tulong)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _bpf_flag tint)
      (Econst_int (Int.repr (-6)) tint))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
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
  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                 (Econst_int (Int.repr 11) tint) tint)
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
              (Tstruct _bpf_state noattr)) _regsmap (tarray tulong 11))
          (Etempvar _i tuint) (tptr tulong)) tulong) (Etempvar _v tulong))
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _bpf_flag tint)
      (Econst_int (Int.repr (-6)) tint)))
  (Sreturn None))
|}.

Definition f_eval_flag := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                   (Tstruct _bpf_state noattr)) _bpf_flag tint)))
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

Definition f_load_mem := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_chunk, tuint) :: (_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk tuint)
  (LScons (Some 1)
    (Sreturn (Some (Ederef (Ecast (Etempvar _v tulong) (tptr tuchar)) tuchar)))
    (LScons (Some 2)
      (Sreturn (Some (Ederef (Ecast (Etempvar _v tulong) (tptr tushort))
                       tushort)))
      (LScons (Some 4)
        (Sreturn (Some (Ederef (Ecast (Etempvar _v tulong) (tptr tuint))
                         tuint)))
        (LScons (Some 8)
          (Sreturn (Some (Ederef (Ecast (Etempvar _v tulong) (tptr tulong))
                           tulong)))
          (LScons None
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                    (Tstruct _bpf_state noattr)) _bpf_flag tint)
                (Econst_int (Int.repr (-2)) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))
            LSnil))))))
|}.

Definition f_store_mem_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_chunk, tuint) :: (_addr, tulong) :: (_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk tuint)
  (LScons (Some 1)
    (Ssequence
      (Sassign (Ederef (Ecast (Etempvar _addr tulong) (tptr tuchar)) tuchar)
        (Etempvar _v tulong))
      (Sreturn None))
    (LScons (Some 2)
      (Ssequence
        (Sassign
          (Ederef (Ecast (Etempvar _addr tulong) (tptr tushort)) tushort)
          (Etempvar _v tulong))
        (Sreturn None))
      (LScons (Some 4)
        (Ssequence
          (Sassign
            (Ederef (Ecast (Etempvar _addr tulong) (tptr tuint)) tuint)
            (Etempvar _v tulong))
          (Sreturn None))
        (LScons (Some 8)
          (Ssequence
            (Sassign
              (Ederef (Ecast (Etempvar _addr tulong) (tptr tulong)) tulong)
              (Etempvar _v tulong))
            (Sreturn None))
          (LScons None
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                    (Tstruct _bpf_state noattr)) _bpf_flag tint)
                (Econst_int (Int.repr (-2)) tint))
              (Sreturn None))
            LSnil))))))
|}.

Definition f_store_mem_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_chunk, tuint) :: (_addr, tulong) :: (_v, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk tuint)
  (LScons (Some 1)
    (Ssequence
      (Sassign (Ederef (Ecast (Etempvar _addr tulong) (tptr tuchar)) tuchar)
        (Etempvar _v tint))
      (Sreturn None))
    (LScons (Some 2)
      (Ssequence
        (Sassign
          (Ederef (Ecast (Etempvar _addr tulong) (tptr tushort)) tushort)
          (Etempvar _v tint))
        (Sreturn None))
      (LScons (Some 4)
        (Ssequence
          (Sassign
            (Ederef (Ecast (Etempvar _addr tulong) (tptr tuint)) tuint)
            (Etempvar _v tint))
          (Sreturn None))
        (LScons (Some 8)
          (Ssequence
            (Sassign
              (Ederef (Ecast (Etempvar _addr tulong) (tptr tulong)) tulong)
              (Etempvar _v tint))
            (Sreturn None))
          (LScons None
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                    (Tstruct _bpf_state noattr)) _bpf_flag tint)
                (Econst_int (Int.repr (-2)) tint))
              (Sreturn None))
            LSnil))))))
|}.

Definition f_list_get := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr tulong)) :: (_idx0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd (Etempvar _l (tptr tulong))
                   (Etempvar _idx0 tulong) (tptr tulong)) tulong)))
|}.

Definition f_get_opcode := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_ins0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _ins0 tulong)
                   (Econst_long (Int64.repr 255) tulong) tulong) tuchar)))
|}.

Definition f_get_dst := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins1, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _ins1 tulong)
                     (Econst_long (Int64.repr 4095) tulong) tulong)
                   (Econst_long (Int64.repr 8) tulong) tulong) tuint)))
|}.

Definition f_get_src := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins2, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _ins2 tulong)
                     (Econst_long (Int64.repr 65535) tulong) tulong)
                   (Econst_long (Int64.repr 12) tulong) tulong) tuint)))
|}.

Definition f_get_offset := {|
  fn_return := tshort;
  fn_callconv := cc_default;
  fn_params := ((_i0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oshl (Etempvar _i0 tulong)
                     (Econst_long (Int64.repr 32) tulong) tulong)
                   (Econst_long (Int64.repr 48) tulong) tulong) tshort)))
|}.

Definition f_get_immediate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i1, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr (Etempvar _i1 tulong)
                   (Econst_long (Int64.repr 32) tulong) tulong) tint)))
|}.

Definition f_get_addl := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_y, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _x tulong) (Etempvar _y tulong) tulong)))
|}.

Definition f_get_subl := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x1, tulong) :: (_y1, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Osub (Etempvar _x1 tulong) (Etempvar _y1 tulong)
                 tulong)))
|}.

Definition f_getMemRegion_block_ptr := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_mr0, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
|}.

Definition f_getMemRegion_start_addr := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_mr1, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef
                   (Etempvar _mr1 (tptr (Tstruct _memory_region noattr)))
                   (Tstruct _memory_region noattr)) _start_addr tulong)))
|}.

Definition f_getMemRegion_block_size := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_mr2, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef
                   (Etempvar _mr2 (tptr (Tstruct _memory_region noattr)))
                   (Tstruct _memory_region noattr)) _block_size tulong)))
|}.

Definition f_is_well_chunk_bool := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_chunk0, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk0 tuint)
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

Definition f_check_mem_aux := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_mr3, (tptr (Tstruct _memory_region noattr))) ::
                (_addr0, tulong) :: (_chunk1, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_well_chunk, tbool) :: (_ptr, tulong) :: (_start, tulong) ::
               (_size, tulong) :: (_lo_ofs, tulong) :: (_hi_ofs, tulong) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_well_chunk_bool (Tfunction (Tcons tuint Tnil) tbool
                                  cc_default))
      ((Etempvar _chunk1 tuint) :: nil))
    (Sset _well_chunk (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _well_chunk tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _getMemRegion_block_ptr (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _memory_region noattr))
                                            Tnil) tulong cc_default))
          ((Etempvar _mr3 (tptr (Tstruct _memory_region noattr))) :: nil))
        (Sset _ptr (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _getMemRegion_start_addr (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _memory_region noattr))
                                               Tnil) tulong cc_default))
            ((Etempvar _mr3 (tptr (Tstruct _memory_region noattr))) :: nil))
          (Sset _start (Etempvar _t'3 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _getMemRegion_block_size (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _memory_region noattr))
                                                 Tnil) tulong cc_default))
              ((Etempvar _mr3 (tptr (Tstruct _memory_region noattr))) :: nil))
            (Sset _size (Etempvar _t'4 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _get_subl (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                  tulong cc_default))
                ((Etempvar _addr0 tulong) :: (Etempvar _start tulong) :: nil))
              (Sset _lo_ofs (Etempvar _t'5 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _get_addl (Tfunction
                                    (Tcons tulong (Tcons tulong Tnil)) tulong
                                    cc_default))
                  ((Etempvar _lo_ofs tulong) :: (Etempvar _chunk1 tuint) ::
                   nil))
                (Sset _hi_ofs (Etempvar _t'6 tulong)))
              (Ssequence
                (Sifthenelse (Ebinop Ole (Econst_long (Int64.repr 0) tulong)
                               (Etempvar _lo_ofs tulong) tint)
                  (Sset _t'8
                    (Ecast
                      (Ebinop Olt (Etempvar _hi_ofs tulong)
                        (Etempvar _size tulong) tint) tbool))
                  (Sset _t'8 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'8 tint)
                  (Ssequence
                    (Sifthenelse (Ebinop Ole (Etempvar _lo_ofs tulong)
                                   (Ebinop Osub
                                     (Econst_long (Int64.repr (-1)) tulong)
                                     (Etempvar _chunk1 tuint) tulong) tint)
                      (Sset _t'7
                        (Ecast
                          (Ebinop Oeq (Econst_long (Int64.repr 0) tulong)
                            (Ebinop Omod (Etempvar _lo_ofs tulong)
                              (Etempvar _chunk1 tuint) tulong) tint) tbool))
                      (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                    (Sifthenelse (Etempvar _t'7 tint)
                      (Sreturn (Some (Ebinop Oadd (Etempvar _ptr tulong)
                                       (Etempvar _lo_ofs tulong) tulong)))
                      (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))
                  (Sreturn (Some (Econst_long (Int64.repr 0) tulong))))))))))
    (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))
|}.

Definition f_check_mem := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_mrs4, (tptr (Tstruct _memory_regions noattr))) ::
                (_addr1, tulong) :: (_chunk2, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_check_mem_ctx, tulong) :: (_check_mem_stk, tulong) ::
               (_check_mem_content, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _check_mem_aux (Tfunction
                             (Tcons (tptr (Tstruct _memory_region noattr))
                               (Tcons tulong (Tcons tuint Tnil))) tulong
                             cc_default))
      ((Efield
         (Ederef (Etempvar _mrs4 (tptr (Tstruct _memory_regions noattr)))
           (Tstruct _memory_regions noattr)) _bpf_ctx
         (tptr (Tstruct _memory_region noattr))) ::
       (Etempvar _addr1 tulong) :: (Etempvar _chunk2 tuint) :: nil))
    (Sset _check_mem_ctx (Etempvar _t'1 tulong)))
  (Sifthenelse (Ebinop Oeq (Etempvar _check_mem_ctx tulong)
                 (Econst_long (Int64.repr 0) tulong) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _check_mem_aux (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _memory_region noattr))
                                   (Tcons tulong (Tcons tuint Tnil))) tulong
                                 cc_default))
          ((Efield
             (Ederef (Etempvar _mrs4 (tptr (Tstruct _memory_regions noattr)))
               (Tstruct _memory_regions noattr)) _bpf_stk
             (tptr (Tstruct _memory_region noattr))) ::
           (Etempvar _addr1 tulong) :: (Etempvar _chunk2 tuint) :: nil))
        (Sset _check_mem_stk (Etempvar _t'2 tulong)))
      (Sifthenelse (Ebinop Oeq (Etempvar _check_mem_stk tulong)
                     (Econst_long (Int64.repr 0) tulong) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _check_mem_aux (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _memory_region noattr))
                                       (Tcons tulong (Tcons tuint Tnil)))
                                     tulong cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _mrs4 (tptr (Tstruct _memory_regions noattr)))
                   (Tstruct _memory_regions noattr)) _content
                 (tptr (Tstruct _memory_region noattr))) ::
               (Etempvar _addr1 tulong) :: (Etempvar _chunk2 tuint) :: nil))
            (Sset _check_mem_content (Etempvar _t'3 tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _check_mem_content tulong)
                         (Econst_long (Int64.repr 0) tulong) tint)
            (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))
            (Sreturn (Some (Etempvar _check_mem_content tulong)))))
        (Sreturn (Some (Etempvar _check_mem_stk tulong)))))
    (Sreturn (Some (Etempvar _check_mem_ctx tulong)))))
|}.

Definition f_step := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_l0, (tptr tulong)) :: (_len0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_pc, tulong) :: (_ins, tulong) :: (_op, tuchar) ::
               (_dst, tuint) :: (_src, tuint) :: (_dst64, tulong) ::
               (_src64, tulong) :: (_ofs, tshort) :: (_imm, tint) ::
               (_addr_dst, tulong) :: (_addr_src, tulong) ::
               (_next_ins, tulong) :: (_next_imm, tint) ::
               (_check_ldxw, tulong) :: (_v_xw, tulong) ::
               (_check_ldxh, tulong) :: (_v_xh, tulong) ::
               (_check_ldxb, tulong) :: (_v_xb, tulong) ::
               (_check_ldxdw, tulong) :: (_v_xdw, tulong) ::
               (_check_stw, tulong) :: (_check_sth, tulong) ::
               (_check_stb, tulong) :: (_check_stdw, tulong) ::
               (_check_stxw, tulong) :: (_check_stxh, tulong) ::
               (_check_stxb, tulong) :: (_check_stxdw, tulong) ::
               (_t'29, tulong) :: (_t'28, tulong) :: (_t'27, tulong) ::
               (_t'26, tulong) :: (_t'25, tulong) :: (_t'24, tulong) ::
               (_t'23, tulong) :: (_t'22, tulong) :: (_t'21, tulong) ::
               (_t'20, tulong) :: (_t'19, tulong) :: (_t'18, tulong) ::
               (_t'17, tulong) :: (_t'16, tulong) :: (_t'15, tulong) ::
               (_t'14, tulong) :: (_t'13, tint) :: (_t'12, tulong) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tint) ::
               (_t'8, tshort) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuchar) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_pc (Tfunction
                       (Tcons (tptr (Tstruct _bpf_state noattr)) Tnil) tulong
                       cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
    (Sset _pc (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _list_get (Tfunction (Tcons (tptr tulong) (Tcons tulong Tnil))
                          tulong cc_default))
        ((Etempvar _l0 (tptr tulong)) :: (Etempvar _pc tulong) :: nil))
      (Sset _ins (Etempvar _t'2 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_opcode (Tfunction (Tcons tulong Tnil) tuchar cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _op (Ecast (Etempvar _t'3 tuchar) tuchar)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _dst (Etempvar _t'4 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _get_src (Tfunction (Tcons tulong Tnil) tuint cc_default))
              ((Etempvar _ins tulong) :: nil))
            (Sset _src (Etempvar _t'5 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _eval_reg (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tuint Tnil)) tulong cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Etempvar _dst tuint) :: nil))
              (Sset _dst64 (Etempvar _t'6 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _eval_reg (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tuint Tnil)) tulong cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Etempvar _src tuint) :: nil))
                (Sset _src64 (Etempvar _t'7 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _get_offset (Tfunction (Tcons tulong Tnil) tshort
                                        cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _ofs (Ecast (Etempvar _t'8 tshort) tshort)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'9)
                      (Evar _get_immediate (Tfunction (Tcons tulong Tnil)
                                             tint cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _imm (Etempvar _t'9 tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'10)
                        (Evar _get_addl (Tfunction
                                          (Tcons tulong (Tcons tulong Tnil))
                                          tulong cc_default))
                        ((Etempvar _dst64 tulong) ::
                         (Etempvar _ofs tshort) :: nil))
                      (Sset _addr_dst (Etempvar _t'10 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'11)
                          (Evar _get_addl (Tfunction
                                            (Tcons tulong
                                              (Tcons tulong Tnil)) tulong
                                            cc_default))
                          ((Etempvar _src64 tulong) ::
                           (Etempvar _ofs tshort) :: nil))
                        (Sset _addr_src (Etempvar _t'11 tulong)))
                      (Sswitch (Etempvar _op tuchar)
                        (LScons (Some 7)
                          (Ssequence
                            (Scall None
                              (Evar _upd_reg (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _bpf_state noattr))
                                                 (Tcons tuint
                                                   (Tcons tulong Tnil)))
                                               tvoid cc_default))
                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                               (Etempvar _dst tuint) ::
                               (Ebinop Oadd (Etempvar _dst64 tulong)
                                 (Ecast (Etempvar _imm tint) tulong) tulong) ::
                               nil))
                            (Ssequence
                              (Scall None
                                (Evar _upd_flag (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _bpf_state noattr))
                                                    (Tcons tint Tnil)) tvoid
                                                  cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Econst_int (Int.repr 0) tint) :: nil))
                              (Sreturn None)))
                          (LScons (Some 15)
                            (Ssequence
                              (Scall None
                                (Evar _upd_reg (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _bpf_state noattr))
                                                   (Tcons tuint
                                                     (Tcons tulong Tnil)))
                                                 tvoid cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Etempvar _dst tuint) ::
                                 (Ebinop Oadd (Etempvar _dst64 tulong)
                                   (Etempvar _src64 tulong) tulong) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _upd_flag (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _bpf_state noattr))
                                                      (Tcons tint Tnil))
                                                    tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Econst_int (Int.repr 0) tint) :: nil))
                                (Sreturn None)))
                            (LScons (Some 23)
                              (Ssequence
                                (Scall None
                                  (Evar _upd_reg (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _bpf_state noattr))
                                                     (Tcons tuint
                                                       (Tcons tulong Tnil)))
                                                   tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Etempvar _dst tuint) ::
                                   (Ebinop Osub (Etempvar _dst64 tulong)
                                     (Ecast (Etempvar _imm tint) tulong)
                                     tulong) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_flag (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Econst_int (Int.repr 0) tint) :: nil))
                                  (Sreturn None)))
                              (LScons (Some 31)
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_reg (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _bpf_state noattr))
                                                       (Tcons tuint
                                                         (Tcons tulong Tnil)))
                                                     tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Etempvar _dst tuint) ::
                                     (Ebinop Osub (Etempvar _dst64 tulong)
                                       (Etempvar _src64 tulong) tulong) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _upd_flag (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _bpf_state noattr))
                                                          (Tcons tint Tnil))
                                                        tvoid cc_default))
                                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                       (Econst_int (Int.repr 0) tint) :: nil))
                                    (Sreturn None)))
                                (LScons (Some 39)
                                  (Ssequence
                                    (Scall None
                                      (Evar _upd_reg (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _bpf_state noattr))
                                                         (Tcons tuint
                                                           (Tcons tulong
                                                             Tnil))) tvoid
                                                       cc_default))
                                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                       (Etempvar _dst tuint) ::
                                       (Ebinop Omul (Etempvar _dst64 tulong)
                                         (Ecast (Etempvar _imm tint) tulong)
                                         tulong) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _upd_flag (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _bpf_state noattr))
                                                            (Tcons tint Tnil))
                                                          tvoid cc_default))
                                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                         (Econst_int (Int.repr 0) tint) ::
                                         nil))
                                      (Sreturn None)))
                                  (LScons (Some 47)
                                    (Ssequence
                                      (Scall None
                                        (Evar _upd_reg (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _bpf_state noattr))
                                                           (Tcons tuint
                                                             (Tcons tulong
                                                               Tnil))) tvoid
                                                         cc_default))
                                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                         (Etempvar _dst tuint) ::
                                         (Ebinop Omul
                                           (Etempvar _dst64 tulong)
                                           (Etempvar _src64 tulong) tulong) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _upd_flag (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _bpf_state noattr))
                                                              (Tcons tint
                                                                Tnil)) tvoid
                                                            cc_default))
                                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                           (Econst_int (Int.repr 0) tint) ::
                                           nil))
                                        (Sreturn None)))
                                    (LScons (Some 55)
                                      (Sifthenelse (Ebinop One
                                                     (Ecast
                                                       (Etempvar _imm tint)
                                                       tulong)
                                                     (Econst_long (Int64.repr 0) tulong)
                                                     tint)
                                        (Ssequence
                                          (Scall None
                                            (Evar _upd_reg (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _bpf_state noattr))
                                                               (Tcons tuint
                                                                 (Tcons
                                                                   tulong
                                                                   Tnil)))
                                                             tvoid
                                                             cc_default))
                                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                             (Etempvar _dst tuint) ::
                                             (Ebinop Odiv
                                               (Etempvar _dst64 tulong)
                                               (Ecast (Etempvar _imm tint)
                                                 tulong) tulong) :: nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _upd_flag (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _bpf_state noattr))
                                                                  (Tcons tint
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               nil))
                                            (Sreturn None)))
                                        (Ssequence
                                          (Scall None
                                            (Evar _upd_flag (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _bpf_state noattr))
                                                                (Tcons tint
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                             (Eunop Oneg
                                               (Econst_int (Int.repr 9) tint)
                                               tint) :: nil))
                                          (Sreturn None)))
                                      (LScons (Some 63)
                                        (Sifthenelse (Ebinop One
                                                       (Etempvar _src64 tulong)
                                                       (Econst_long (Int64.repr 0) tulong)
                                                       tint)
                                          (Ssequence
                                            (Scall None
                                              (Evar _upd_reg (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _bpf_state noattr))
                                                                 (Tcons tuint
                                                                   (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                               tvoid
                                                               cc_default))
                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                               (Etempvar _dst tuint) ::
                                               (Ebinop Odiv
                                                 (Etempvar _dst64 tulong)
                                                 (Etempvar _src64 tulong)
                                                 tulong) :: nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _upd_flag (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                 (Econst_int (Int.repr 0) tint) ::
                                                 nil))
                                              (Sreturn None)))
                                          (Ssequence
                                            (Scall None
                                              (Evar _upd_flag (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _bpf_state noattr))
                                                                  (Tcons tint
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                               (Eunop Oneg
                                                 (Econst_int (Int.repr 9) tint)
                                                 tint) :: nil))
                                            (Sreturn None)))
                                        (LScons (Some 71)
                                          (Ssequence
                                            (Scall None
                                              (Evar _upd_reg (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _bpf_state noattr))
                                                                 (Tcons tuint
                                                                   (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                               tvoid
                                                               cc_default))
                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                               (Etempvar _dst tuint) ::
                                               (Ebinop Oor
                                                 (Etempvar _dst64 tulong)
                                                 (Ecast (Etempvar _imm tint)
                                                   tulong) tulong) :: nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _upd_flag (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                 (Econst_int (Int.repr 0) tint) ::
                                                 nil))
                                              (Sreturn None)))
                                          (LScons (Some 79)
                                            (Ssequence
                                              (Scall None
                                                (Evar _upd_reg (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _bpf_state noattr))
                                                                   (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                 tvoid
                                                                 cc_default))
                                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                 (Etempvar _dst tuint) ::
                                                 (Ebinop Oor
                                                   (Etempvar _dst64 tulong)
                                                   (Etempvar _src64 tulong)
                                                   tulong) :: nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _upd_flag (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   nil))
                                                (Sreturn None)))
                                            (LScons (Some 87)
                                              (Ssequence
                                                (Scall None
                                                  (Evar _upd_reg (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                   tvoid
                                                                   cc_default))
                                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                   (Etempvar _dst tuint) ::
                                                   (Ebinop Oand
                                                     (Etempvar _dst64 tulong)
                                                     (Ecast
                                                       (Etempvar _imm tint)
                                                       tulong) tulong) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _upd_flag (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                     (Econst_int (Int.repr 0) tint) ::
                                                     nil))
                                                  (Sreturn None)))
                                              (LScons (Some 95)
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _upd_reg (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                     (Etempvar _dst tuint) ::
                                                     (Ebinop Oand
                                                       (Etempvar _dst64 tulong)
                                                       (Etempvar _src64 tulong)
                                                       tulong) :: nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _upd_flag 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _bpf_state noattr))
                                                          (Tcons tint Tnil))
                                                        tvoid cc_default))
                                                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                       (Econst_int (Int.repr 0) tint) ::
                                                       nil))
                                                    (Sreturn None)))
                                                (LScons (Some 103)
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Ecast
                                                                   (Etempvar _imm tint)
                                                                   tulong)
                                                                 (Econst_long (Int64.repr 64) tulong)
                                                                 tint)
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _upd_reg 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _bpf_state noattr))
                                                            (Tcons tuint
                                                              (Tcons tulong
                                                                Tnil))) tvoid
                                                          cc_default))
                                                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                         (Etempvar _dst tuint) ::
                                                         (Ebinop Oshl
                                                           (Etempvar _dst64 tulong)
                                                           (Etempvar _imm tint)
                                                           tulong) :: nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _upd_flag 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _bpf_state noattr))
                                                              (Tcons tint
                                                                Tnil)) tvoid
                                                            cc_default))
                                                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                           (Econst_int (Int.repr 0) tint) ::
                                                           nil))
                                                        (Sreturn None)))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _upd_flag 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _bpf_state noattr))
                                                            (Tcons tint Tnil))
                                                          tvoid cc_default))
                                                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                         (Eunop Oneg
                                                           (Econst_int (Int.repr 10) tint)
                                                           tint) :: nil))
                                                      (Sreturn None)))
                                                  (LScons (Some 111)
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _src64 tulong)
                                                                   (Econst_long (Int64.repr 64) tulong)
                                                                   tint)
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _upd_reg 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _bpf_state noattr))
                                                              (Tcons tuint
                                                                (Tcons tulong
                                                                  Tnil)))
                                                            tvoid cc_default))
                                                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                           (Etempvar _dst tuint) ::
                                                           (Ebinop Oshl
                                                             (Etempvar _dst64 tulong)
                                                             (Ecast
                                                               (Etempvar _src64 tulong)
                                                               tuint) tulong) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _upd_flag 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _bpf_state noattr))
                                                                (Tcons tint
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                             (Econst_int (Int.repr 0) tint) ::
                                                             nil))
                                                          (Sreturn None)))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _upd_flag 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _bpf_state noattr))
                                                              (Tcons tint
                                                                Tnil)) tvoid
                                                            cc_default))
                                                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                           (Eunop Oneg
                                                             (Econst_int (Int.repr 10) tint)
                                                             tint) :: nil))
                                                        (Sreturn None)))
                                                    (LScons (Some 119)
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    (Econst_long (Int64.repr 64) tulong)
                                                                    tint)
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _upd_reg 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _bpf_state noattr))
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                             (Etempvar _dst tuint) ::
                                                             (Ebinop Oshr
                                                               (Etempvar _dst64 tulong)
                                                               (Etempvar _imm tint)
                                                               tulong) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _upd_flag 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _bpf_state noattr))
                                                                  (Tcons tint
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                               (Econst_int (Int.repr 0) tint) ::
                                                               nil))
                                                            (Sreturn None)))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _upd_flag 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _bpf_state noattr))
                                                                (Tcons tint
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                             (Eunop Oneg
                                                               (Econst_int (Int.repr 10) tint)
                                                               tint) :: nil))
                                                          (Sreturn None)))
                                                      (LScons (Some 127)
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _src64 tulong)
                                                            (Econst_long (Int64.repr 64) tulong)
                                                            tint)
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _upd_reg 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _bpf_state noattr))
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                               (Etempvar _dst tuint) ::
                                                               (Ebinop Oshr
                                                                 (Etempvar _dst64 tulong)
                                                                 (Ecast
                                                                   (Etempvar _src64 tulong)
                                                                   tuint)
                                                                 tulong) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _upd_flag 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                 (Econst_int (Int.repr 0) tint) ::
                                                                 nil))
                                                              (Sreturn None)))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _upd_flag 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _bpf_state noattr))
                                                                  (Tcons tint
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                               (Eunop Oneg
                                                                 (Econst_int (Int.repr 10) tint)
                                                                 tint) ::
                                                               nil))
                                                            (Sreturn None)))
                                                        (LScons (Some 135)
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _upd_reg 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _bpf_state noattr))
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                               (Etempvar _dst tuint) ::
                                                               (Eunop Oneg
                                                                 (Etempvar _dst64 tulong)
                                                                 tulong) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _upd_flag 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                 (Econst_int (Int.repr 0) tint) ::
                                                                 nil))
                                                              (Sreturn None)))
                                                          (LScons (Some 151)
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Ecast
                                                                  (Etempvar _imm tint)
                                                                  tulong)
                                                                (Econst_long (Int64.repr 0) tulong)
                                                                tint)
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _upd_reg 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                   (Etempvar _dst tuint) ::
                                                                   (Ebinop Omod
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _imm tint)
                                                                    tulong) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                  (Sreturn None)))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _upd_flag 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                   (Eunop Oneg
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint) ::
                                                                   nil))
                                                                (Sreturn None)))
                                                            (LScons (Some 159)
                                                              (Sifthenelse 
                                                                (Ebinop One
                                                                  (Etempvar _src64 tulong)
                                                                  (Econst_long (Int64.repr 0) tulong)
                                                                  tint)
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ebinop Omod
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint) ::
                                                                    nil))
                                                                  (Sreturn None)))
                                                              (LScons (Some 167)
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ebinop Oxor
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                (LScons (Some 175)
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ebinop Oxor
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                  (LScons (Some 183)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 191)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Etempvar _src64 tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 199)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    (Econst_long (Int64.repr 64) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ebinop Oshr
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Etempvar _imm tint)
                                                                    tlong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 207)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _src64 tulong)
                                                                    (Econst_long (Int64.repr 64) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ebinop Oshr
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tlong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 4)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 12)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 20)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 28)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 36)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 44)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Omul
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 52)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _imm tint)
                                                                    (Econst_int (Int.repr 0) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Odiv
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 60)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Odiv
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 68)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oor
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 76)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oor
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 84)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 92)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 100)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _imm tint)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 108)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 116)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _imm tint)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 124)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 132)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 148)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _imm tint)
                                                                    (Econst_int (Int.repr 0) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Omod
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 156)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Omod
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 164)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 172)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oxor
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tuint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 180)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Etempvar _imm tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 188)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 196)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _imm tint)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    tint)
                                                                    (Etempvar _imm tint)
                                                                    tint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 204)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tuint)
                                                                    tint)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tuint)
                                                                    tint)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 5)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 21)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 29)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 37)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 45)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 53)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 61)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 165)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 173)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 181)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 189)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 69)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Ebinop Oand
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 77)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Ebinop Oand
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 85)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 93)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _dst64 tulong)
                                                                    (Etempvar _src64 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 101)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 109)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 117)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 125)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 197)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 205)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 213)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 221)
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Etempvar _dst64 tulong)
                                                                    tlong)
                                                                    (Ecast
                                                                    (Etempvar _src64 tulong)
                                                                    tlong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Etempvar _ofs tshort)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 24)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    tulong)
                                                                    (Etempvar _len0 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'12)
                                                                    (Evar _list_get 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tulong)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _l0 (tptr tulong)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pc tulong)
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Sset _next_ins
                                                                    (Etempvar _t'12 tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'13)
                                                                    (Evar _get_immediate 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _next_ins tulong) ::
                                                                    nil))
                                                                    (Sset _next_imm
                                                                    (Etempvar _t'13 tint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Ebinop Oor
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _imm tint)
                                                                    tuint)
                                                                    tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _next_imm tint)
                                                                    tuint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 32) tuint)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_pc_incr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None))))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None)))
                                                                    (LScons (Some 97)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'14)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_src tulong) ::
                                                                    (Econst_int (Int.repr 4) tuint) ::
                                                                    nil))
                                                                    (Sset _check_ldxw
                                                                    (Etempvar _t'14 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_ldxw tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'15)
                                                                    (Evar _load_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 4) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Sset _v_xw
                                                                    (Etempvar _t'15 tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Etempvar _v_xw tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None))))))
                                                                    (LScons (Some 105)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'16)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_src tulong) ::
                                                                    (Econst_int (Int.repr 2) tuint) ::
                                                                    nil))
                                                                    (Sset _check_ldxh
                                                                    (Etempvar _t'16 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_ldxh tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'17)
                                                                    (Evar _load_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 2) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Sset _v_xh
                                                                    (Etempvar _t'17 tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Etempvar _v_xh tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None))))))
                                                                    (LScons (Some 113)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'18)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_src tulong) ::
                                                                    (Econst_int (Int.repr 1) tuint) ::
                                                                    nil))
                                                                    (Sset _check_ldxb
                                                                    (Etempvar _t'18 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_ldxb tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'19)
                                                                    (Evar _load_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 1) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Sset _v_xb
                                                                    (Etempvar _t'19 tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Etempvar _v_xb tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None))))))
                                                                    (LScons (Some 121)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'20)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_src tulong) ::
                                                                    (Econst_int (Int.repr 8) tuint) ::
                                                                    nil))
                                                                    (Sset _check_ldxdw
                                                                    (Etempvar _t'20 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_ldxdw tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'21)
                                                                    (Evar _load_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 8) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    nil))
                                                                    (Sset _v_xdw
                                                                    (Etempvar _t'21 tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Etempvar _dst tuint) ::
                                                                    (Etempvar _v_xdw tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None))))))
                                                                    (LScons (Some 98)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'22)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 4) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stw
                                                                    (Etempvar _t'22 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stw tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_imm 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 4) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _imm tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 106)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'23)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 2) tuint) ::
                                                                    nil))
                                                                    (Sset _check_sth
                                                                    (Etempvar _t'23 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_sth tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_imm 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 2) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _imm tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 114)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'24)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 1) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stb
                                                                    (Etempvar _t'24 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stb tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_imm 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 1) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _imm tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 122)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'25)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 8) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stdw
                                                                    (Etempvar _t'25 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stdw tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_imm 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 8) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _imm tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 99)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 4) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stxw
                                                                    (Etempvar _t'26 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stxw tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 4) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _src64 tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 107)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'27)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 2) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stxh
                                                                    (Etempvar _t'27 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stxh tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 2) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _src64 tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 115)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'28)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 1) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stxb
                                                                    (Etempvar _t'28 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stxb tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 1) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _src64 tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 123)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'29)
                                                                    (Evar _check_mem 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _memory_regions noattr))
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tulong
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                                                                    (Tstruct _bpf_state noattr))
                                                                    _mrs
                                                                    (tptr (Tstruct _memory_regions noattr))) ::
                                                                    (Etempvar _addr_dst tulong) ::
                                                                    (Econst_int (Int.repr 8) tuint) ::
                                                                    nil))
                                                                    (Sset _check_stxdw
                                                                    (Etempvar _t'29 tulong)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _check_stxdw tulong)
                                                                    (Econst_long (Int64.repr 0) tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _store_mem_reg 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 8) tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dst64 tulong)
                                                                    (Ecast
                                                                    (Etempvar _ofs tshort)
                                                                    tulong)
                                                                    tulong) ::
                                                                    (Etempvar _src64 tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sreturn None)))))
                                                                    (LScons (Some 149)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Econst_int (Int.repr 1) tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    (LScons None
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _upd_flag 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sreturn None))
                                                                    LSnil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_bpf_interpreter_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_l1, (tptr tulong)) :: (_len1, tulong) :: (_fuel1, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_fuel0, tuint) :: (_pc1, tulong) :: (_f1, tint) ::
               (_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _fuel1 tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Ssequence
    (Scall None
      (Evar _upd_flag (Tfunction
                        (Tcons (tptr (Tstruct _bpf_state noattr))
                          (Tcons tint Tnil)) tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
       (Eunop Oneg (Econst_int (Int.repr 5) tint) tint) :: nil))
    (Sreturn None))
  (Ssequence
    (Sset _fuel0
      (Ebinop Osub (Etempvar _fuel1 tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_pc (Tfunction
                           (Tcons (tptr (Tstruct _bpf_state noattr)) Tnil)
                           tulong cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
        (Sset _pc1 (Etempvar _t'1 tulong)))
      (Sifthenelse (Ebinop Olt (Etempvar _pc1 tulong) (Etempvar _len1 tulong)
                     tint)
        (Ssequence
          (Scall None
            (Evar _step (Tfunction
                          (Tcons (tptr (Tstruct _bpf_state noattr))
                            (Tcons (tptr tulong) (Tcons tulong Tnil))) tvoid
                          cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Etempvar _l1 (tptr tulong)) :: (Etempvar _len1 tulong) :: nil))
          (Ssequence
            (Scall None
              (Evar _upd_pc_incr (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     Tnil) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _eval_flag (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       Tnil) tint cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
                (Sset _f1 (Etempvar _t'2 tint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _f1 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Scall None
                    (Evar _bpf_interpreter_aux (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _bpf_state noattr))
                                                   (Tcons (tptr tulong)
                                                     (Tcons tulong
                                                       (Tcons tuint Tnil))))
                                                 tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Etempvar _l1 (tptr tulong)) ::
                     (Etempvar _len1 tulong) :: (Etempvar _fuel0 tuint) ::
                     nil))
                  (Sreturn None))
                (Sreturn None)))))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Eunop Oneg (Econst_int (Int.repr 5) tint) tint) :: nil))
          (Sreturn None))))))
|}.

Definition f_bpf_interpreter := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_l2, (tptr tulong)) :: (_len2, tulong) :: (_fuel2, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_f2, tint) :: (_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _upd_reg (Tfunction
                     (Tcons (tptr (Tstruct _bpf_state noattr))
                       (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
     (Econst_int (Int.repr 1) tuint) ::
     (Efield
       (Ederef
         (Efield
           (Ederef
             (Efield
               (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                 (Tstruct _bpf_state noattr)) _mrs
               (tptr (Tstruct _memory_regions noattr)))
             (Tstruct _memory_regions noattr)) _bpf_ctx
           (tptr (Tstruct _memory_region noattr)))
         (Tstruct _memory_region noattr)) _start_addr tulong) :: nil))
  (Ssequence
    (Scall None
      (Evar _bpf_interpreter_aux (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons (tptr tulong)
                                       (Tcons tulong (Tcons tuint Tnil))))
                                   tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
       (Etempvar _l2 (tptr tulong)) :: (Etempvar _len2 tulong) ::
       (Etempvar _fuel2 tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_flag (Tfunction
                             (Tcons (tptr (Tstruct _bpf_state noattr)) Tnil)
                             tint cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
        (Sset _f2 (Etempvar _t'1 tint)))
      (Sifthenelse (Ebinop Oeq (Etempvar _f2 tint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _eval_reg (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tuint Tnil)) tulong cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 0) tuint) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))
        (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))))
|}.

Definition composites : list composite_definition :=
(Composite _memory_region Struct
   ((_start_addr, tulong) :: (_block_size, tulong) :: nil)
   noattr ::
 Composite _memory_regions Struct
   ((_bpf_ctx, (tptr (Tstruct _memory_region noattr))) ::
    (_bpf_stk, (tptr (Tstruct _memory_region noattr))) ::
    (_content, (tptr (Tstruct _memory_region noattr))) :: nil)
   noattr ::
 Composite _bpf_state Struct
   ((_state_pc, tulong) :: (_regsmap, (tarray tulong 11)) ::
    (_bpf_flag, tint) :: (_mrs, (tptr (Tstruct _memory_regions noattr))) ::
    nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
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
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_eval_pc, Gfun(Internal f_eval_pc)) ::
 (_upd_pc, Gfun(Internal f_upd_pc)) ::
 (_upd_pc_incr, Gfun(Internal f_upd_pc_incr)) ::
 (_eval_reg, Gfun(Internal f_eval_reg)) ::
 (_upd_reg, Gfun(Internal f_upd_reg)) ::
 (_eval_flag, Gfun(Internal f_eval_flag)) ::
 (_upd_flag, Gfun(Internal f_upd_flag)) ::
 (_load_mem, Gfun(Internal f_load_mem)) ::
 (_store_mem_reg, Gfun(Internal f_store_mem_reg)) ::
 (_store_mem_imm, Gfun(Internal f_store_mem_imm)) ::
 (_list_get, Gfun(Internal f_list_get)) ::
 (_get_opcode, Gfun(Internal f_get_opcode)) ::
 (_get_dst, Gfun(Internal f_get_dst)) ::
 (_get_src, Gfun(Internal f_get_src)) ::
 (_get_offset, Gfun(Internal f_get_offset)) ::
 (_get_immediate, Gfun(Internal f_get_immediate)) ::
 (_get_addl, Gfun(Internal f_get_addl)) ::
 (_get_subl, Gfun(Internal f_get_subl)) ::
 (_getMemRegion_block_ptr, Gfun(Internal f_getMemRegion_block_ptr)) ::
 (_getMemRegion_start_addr, Gfun(Internal f_getMemRegion_start_addr)) ::
 (_getMemRegion_block_size, Gfun(Internal f_getMemRegion_block_size)) ::
 (_is_well_chunk_bool, Gfun(Internal f_is_well_chunk_bool)) ::
 (_check_mem_aux, Gfun(Internal f_check_mem_aux)) ::
 (_check_mem, Gfun(Internal f_check_mem)) ::
 (_step, Gfun(Internal f_step)) ::
 (_bpf_interpreter_aux, Gfun(Internal f_bpf_interpreter_aux)) ::
 (_bpf_interpreter, Gfun(Internal f_bpf_interpreter)) :: nil).

Definition public_idents : list ident :=
(_bpf_interpreter :: _bpf_interpreter_aux :: _step :: ___builtin_debug ::
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
 ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


