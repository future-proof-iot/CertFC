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
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "interpreter.c".
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
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition _add_mem_region : ident := $"add_mem_region".
Definition _add_mem_region_ctx : ident := $"add_mem_region_ctx".
Definition _addr : ident := $"addr".
Definition _block_perm : ident := $"block_perm".
Definition _block_ptr : ident := $"block_ptr".
Definition _block_size : ident := $"block_size".
Definition _bpf_ctx : ident := $"bpf_ctx".
Definition _bpf_flag : ident := $"bpf_flag".
Definition _bpf_interpreter : ident := $"bpf_interpreter".
Definition _bpf_interpreter_aux : ident := $"bpf_interpreter_aux".
Definition _bpf_state : ident := $"bpf_state".
Definition _check_ld : ident := $"check_ld".
Definition _check_mem : ident := $"check_mem".
Definition _check_mem__1 : ident := $"check_mem__1".
Definition _check_mem_aux : ident := $"check_mem_aux".
Definition _check_mem_aux2 : ident := $"check_mem_aux2".
Definition _check_st : ident := $"check_st".
Definition _chunk : ident := $"chunk".
Definition _comp_and_0x08_byte : ident := $"comp_and_0x08_byte".
Definition _cur_mr : ident := $"cur_mr".
Definition _d : ident := $"d".
Definition _dst : ident := $"dst".
Definition _dst32 : ident := $"dst32".
Definition _dst64 : ident := $"dst64".
Definition _eval_flag : ident := $"eval_flag".
Definition _eval_immediate : ident := $"eval_immediate".
Definition _eval_mem_num : ident := $"eval_mem_num".
Definition _eval_mem_regions : ident := $"eval_mem_regions".
Definition _eval_pc : ident := $"eval_pc".
Definition _eval_reg : ident := $"eval_reg".
Definition _f : ident := $"f".
Definition _fuel : ident := $"fuel".
Definition _fuel0 : ident := $"fuel0".
Definition _get_addl : ident := $"get_addl".
Definition _get_dst : ident := $"get_dst".
Definition _get_immediate : ident := $"get_immediate".
Definition _get_mem_region : ident := $"get_mem_region".
Definition _get_offset : ident := $"get_offset".
Definition _get_opcode : ident := $"get_opcode".
Definition _get_opcode_alu32 : ident := $"get_opcode_alu32".
Definition _get_opcode_alu64 : ident := $"get_opcode_alu64".
Definition _get_opcode_branch : ident := $"get_opcode_branch".
Definition _get_opcode_ins : ident := $"get_opcode_ins".
Definition _get_opcode_mem_ld_imm : ident := $"get_opcode_mem_ld_imm".
Definition _get_opcode_mem_ld_reg : ident := $"get_opcode_mem_ld_reg".
Definition _get_opcode_mem_st_imm : ident := $"get_opcode_mem_st_imm".
Definition _get_opcode_mem_st_reg : ident := $"get_opcode_mem_st_reg".
Definition _get_src : ident := $"get_src".
Definition _get_subl : ident := $"get_subl".
Definition _hi_ofs : ident := $"hi_ofs".
Definition _i : ident := $"i".
Definition _idx : ident := $"idx".
Definition _imm : ident := $"imm".
Definition _imm64 : ident := $"imm64".
Definition _ins : ident := $"ins".
Definition _is_imm : ident := $"is_imm".
Definition _is_well_chunk_bool : ident := $"is_well_chunk_bool".
Definition _l : ident := $"l".
Definition _len : ident := $"len".
Definition _list_get : ident := $"list_get".
Definition _lo_ofs : ident := $"lo_ofs".
Definition _load_mem : ident := $"load_mem".
Definition _main : ident := $"main".
Definition _mem_num : ident := $"mem_num".
Definition _mem_reg_num : ident := $"mem_reg_num".
Definition _memory_region : ident := $"memory_region".
Definition _mr : ident := $"mr".
Definition _mrs : ident := $"mrs".
Definition _n : ident := $"n".
Definition _next_imm : ident := $"next_imm".
Definition _next_ins : ident := $"next_ins".
Definition _num : ident := $"num".
Definition _ofs : ident := $"ofs".
Definition _ofs64 : ident := $"ofs64".
Definition _op : ident := $"op".
Definition _opc : ident := $"opc".
Definition _opcode_alu32 : ident := $"opcode_alu32".
Definition _opcode_alu64 : ident := $"opcode_alu64".
Definition _opcode_jmp : ident := $"opcode_jmp".
Definition _opcode_ld : ident := $"opcode_ld".
Definition _opcode_st : ident := $"opcode_st".
Definition _pc : ident := $"pc".
Definition _perm : ident := $"perm".
Definition _print_bpf_state : ident := $"print_bpf_state".
Definition _printf : ident := $"printf".
Definition _reg64_to_reg32 : ident := $"reg64_to_reg32".
Definition _regsmap : ident := $"regsmap".
Definition _src : ident := $"src".
Definition _src32 : ident := $"src32".
Definition _src64 : ident := $"src64".
Definition _st : ident := $"st".
Definition _start_addr : ident := $"start_addr".
Definition _state_pc : ident := $"state_pc".
Definition _step : ident := $"step".
Definition _step_opcode_alu32 : ident := $"step_opcode_alu32".
Definition _step_opcode_alu64 : ident := $"step_opcode_alu64".
Definition _step_opcode_branch : ident := $"step_opcode_branch".
Definition _step_opcode_mem_ld_imm : ident := $"step_opcode_mem_ld_imm".
Definition _step_opcode_mem_ld_reg : ident := $"step_opcode_mem_ld_reg".
Definition _step_opcode_mem_st_imm : ident := $"step_opcode_mem_st_imm".
Definition _step_opcode_mem_st_reg : ident := $"step_opcode_mem_st_reg".
Definition _store_mem_imm : ident := $"store_mem_imm".
Definition _store_mem_reg : ident := $"store_mem_reg".
Definition _upd_flag : ident := $"upd_flag".
Definition _upd_pc : ident := $"upd_pc".
Definition _upd_pc_incr : ident := $"upd_pc_incr".
Definition _upd_reg : ident := $"upd_reg".
Definition _v : ident := $"v".
Definition _well_chunk : ident := $"well_chunk".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
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
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 10);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 59) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_print_bpf_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_1 (tarray tschar 9)) ::
     (Ecast
       (Efield
         (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
           (Tstruct _bpf_state noattr)) _state_pc tuint) tulong) :: nil))
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_2 (tarray tschar 10)) ::
       (Efield
         (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
           (Tstruct _bpf_state noattr)) _bpf_flag tint) :: nil))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 11) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_3 (tarray tschar 4)) ::
                 (Etempvar _i tint) :: nil))
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_4 (tarray tschar 7)) ::
                 (Ecast
                   (Ederef
                     (Ebinop Oadd
                       (Efield
                         (Ederef
                           (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                           (Tstruct _bpf_state noattr)) _regsmap
                         (tarray tulong 11)) (Etempvar _i tint)
                       (tptr tulong)) tulong) tulong) :: nil))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Scall None
        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
        ((Evar ___stringlit_5 (tarray tschar 2)) :: nil)))))
|}.

Definition f_eval_pc := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                   (Tstruct _bpf_state noattr)) _state_pc tuint)))
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
        (Tstruct _bpf_state noattr)) _state_pc tuint) (Etempvar _pc tulong))
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
        (Tstruct _bpf_state noattr)) _state_pc tuint)
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _state_pc tuint)
      (Econst_int (Int.repr 1) tint) tuint))
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
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                       (Tstruct _bpf_state noattr)) _regsmap
                     (tarray tulong 11)) (Etempvar _i tuint) (tptr tulong))
                 tulong)))
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

Definition f_eval_mem_num := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                   (Tstruct _bpf_state noattr)) _mem_num tuint)))
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

Definition f_add_mem_region := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_mr, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
            (Tstruct _bpf_state noattr)) _mrs
          (tptr (Tstruct _memory_region noattr)))
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
            (Tstruct _bpf_state noattr)) _mem_num tuint)
        (tptr (Tstruct _memory_region noattr)))
      (Tstruct _memory_region noattr))
    (Ederef (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
      (Tstruct _memory_region noattr)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _mem_num tuint)
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
            (Tstruct _bpf_state noattr)) _mem_num tuint)
        (Econst_int (Int.repr 1) tint) tuint))
    (Sreturn None)))
|}.

Definition f_add_mem_region_ctx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_mr, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
            (Tstruct _bpf_state noattr)) _mrs
          (tptr (Tstruct _memory_region noattr)))
        (Econst_int (Int.repr 0) tint)
        (tptr (Tstruct _memory_region noattr)))
      (Tstruct _memory_region noattr))
    (Ederef (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
      (Tstruct _memory_region noattr)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
          (Tstruct _bpf_state noattr)) _mem_num tuint)
      (Econst_int (Int.repr 1) tint))
    (Sreturn None)))
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
    (Sreturn (Some (Ederef
                     (Ecast (Ecast (Etempvar _v tulong) tlong) (tptr tuchar))
                     tuchar)))
    (LScons (Some 2)
      (Sreturn (Some (Ederef
                       (Ecast (Ecast (Etempvar _v tulong) tlong)
                         (tptr tushort)) tushort)))
      (LScons (Some 4)
        (Sreturn (Some (Ederef
                         (Ecast (Ecast (Etempvar _v tulong) tlong)
                           (tptr tuint)) tuint)))
        (LScons (Some 8)
          (Sreturn (Some (Ederef
                           (Ecast (Ecast (Etempvar _v tulong) tlong)
                             (tptr tulong)) tulong)))
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
      (Sassign
        (Ederef (Ecast (Ecast (Etempvar _addr tulong) tlong) (tptr tuchar))
          tuchar) (Etempvar _v tulong))
      (Sreturn None))
    (LScons (Some 2)
      (Ssequence
        (Sassign
          (Ederef
            (Ecast (Ecast (Etempvar _addr tulong) tlong) (tptr tushort))
            tushort) (Etempvar _v tulong))
        (Sreturn None))
      (LScons (Some 4)
        (Ssequence
          (Sassign
            (Ederef
              (Ecast (Ecast (Etempvar _addr tulong) tlong) (tptr tuint))
              tuint) (Etempvar _v tulong))
          (Sreturn None))
        (LScons (Some 8)
          (Ssequence
            (Sassign
              (Ederef
                (Ecast (Ecast (Etempvar _addr tulong) tlong) (tptr tulong))
                tulong) (Etempvar _v tulong))
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

Definition f_get_dst := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _ins tulong)
                     (Econst_long (Int64.repr 4095) tulong) tulong)
                   (Econst_long (Int64.repr 8) tulong) tulong) tuint)))
|}.

Definition f_reg64_to_reg32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_d, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _d tulong) tuint)))
|}.

Definition f_get_src := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _ins tulong)
                     (Econst_long (Int64.repr 65535) tulong) tulong)
                   (Econst_long (Int64.repr 12) tulong) tulong) tuint)))
|}.

Definition f_get_offset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ecast
                   (Ebinop Oshr
                     (Ebinop Oshl (Etempvar _ins tulong)
                       (Econst_long (Int64.repr 32) tulong) tulong)
                     (Econst_long (Int64.repr 48) tulong) tulong) tshort)
                 tint)))
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

Definition f_eval_immediate := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_ins, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _ins tint) tulong)))
|}.

Definition f_get_opcode_ins := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _ins tulong)
                   (Econst_long (Int64.repr 255) tulong) tulong) tuchar)))
|}.

Definition f_get_opcode_alu64 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 240) tint) tint) tuchar)))
|}.

Definition f_get_opcode_alu32 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 240) tint) tint) tuchar)))
|}.

Definition f_get_opcode_branch := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 240) tint) tint) tuchar)))
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

Definition f_get_opcode_mem_ld_reg := {|
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

Definition f_get_opcode_mem_st_imm := {|
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

Definition f_get_opcode_mem_st_reg := {|
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

Definition f_get_opcode := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 7) tint) tint) tuchar)))
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
  fn_params := ((_x, tulong) :: (_y, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Osub (Etempvar _x tulong) (Etempvar _y tulong) tulong)))
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

Definition f_check_mem_aux2 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_mr, (tptr (Tstruct _memory_region noattr))) ::
                (_addr, tulong) :: (_chunk, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_well_chunk, tbool) :: (_lo_ofs, tulong) ::
               (_hi_ofs, tulong) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_well_chunk_bool (Tfunction (Tcons tuint Tnil) tbool
                                  cc_default))
      ((Etempvar _chunk tuint) :: nil))
    (Sset _well_chunk (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _well_chunk tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_subl (Tfunction (Tcons tulong (Tcons tulong Tnil))
                            tulong cc_default))
          ((Etempvar _addr tulong) ::
           (Efield
             (Ederef (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
               (Tstruct _memory_region noattr)) _start_addr tulong) :: nil))
        (Sset _lo_ofs (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _get_addl (Tfunction (Tcons tulong (Tcons tulong Tnil))
                              tulong cc_default))
            ((Etempvar _lo_ofs tulong) ::
             (Ecast (Etempvar _chunk tuint) tulong) :: nil))
          (Sset _hi_ofs (Etempvar _t'3 tulong)))
        (Ssequence
          (Sifthenelse (Ebinop Ole (Econst_long (Int64.repr 0) tulong)
                         (Etempvar _lo_ofs tulong) tint)
            (Sset _t'5
              (Ecast
                (Ebinop Olt (Etempvar _hi_ofs tulong)
                  (Efield
                    (Ederef
                      (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
                      (Tstruct _memory_region noattr)) _block_size tuint)
                  tint) tbool))
            (Sset _t'5 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'5 tint)
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _lo_ofs tulong)
                             (Ebinop Osub
                               (Econst_long (Int64.repr (-1)) tulong)
                               (Ecast (Etempvar _chunk tuint) tulong) tulong)
                             tint)
                (Sset _t'4
                  (Ecast
                    (Ebinop Oeq (Econst_long (Int64.repr 0) tulong)
                      (Ebinop Omod (Etempvar _lo_ofs tulong)
                        (Ecast (Etempvar _chunk tuint) tulong) tulong) tint)
                    tbool))
                (Sset _t'4 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'4 tint)
                (Sreturn (Some (Ebinop Oadd
                                 (Econst_long (Int64.repr 1) tulong)
                                 (Etempvar _lo_ofs tulong) tulong)))
                (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))
            (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))))
    (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))
|}.

Definition f_check_mem_aux := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_num, tuint) ::
                (_perm, tuint) :: (_chunk, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) ::
               (_cur_mr, (tptr (Tstruct _memory_region noattr))) ::
               (_check_mem__1, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) ::
               (_t'1, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _num tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))
  (Ssequence
    (Sset _n
      (Ebinop Osub (Etempvar _num tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_mem_region (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tuint Tnil))
                                  (tptr (Tstruct _memory_region noattr))
                                  cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
           (Etempvar _n tuint) :: nil))
        (Sset _cur_mr (Etempvar _t'1 (tptr (Tstruct _memory_region noattr)))))
      (Sifthenelse (Ebinop Oge
                     (Efield
                       (Ederef
                         (Etempvar _cur_mr (tptr (Tstruct _memory_region noattr)))
                         (Tstruct _memory_region noattr)) _block_perm tuint)
                     (Etempvar _perm tuint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _check_mem_aux2 (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _memory_region noattr))
                                        (Tcons tulong (Tcons tuint Tnil)))
                                      tulong cc_default))
              ((Etempvar _cur_mr (tptr (Tstruct _memory_region noattr))) ::
               (Etempvar _addr tulong) :: (Etempvar _chunk tuint) :: nil))
            (Sset _check_mem__1 (Etempvar _t'2 tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _check_mem__1 tulong)
                         (Econst_long (Int64.repr 0) tulong) tint)
            (Ssequence
              (Scall (Some _t'3)
                (Evar _check_mem_aux (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _bpf_state noattr))
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons tulong Tnil))))) tulong
                                       cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Etempvar _n tuint) :: (Etempvar _perm tuint) ::
                 (Etempvar _chunk tuint) :: (Etempvar _addr tulong) :: nil))
              (Sreturn (Some (Etempvar _t'3 tulong))))
            (Sreturn (Some (Etempvar _check_mem__1 tulong)))))
        (Ssequence
          (Scall (Some _t'4)
            (Evar _check_mem_aux (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil)))))
                                   tulong cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Etempvar _n tuint) :: (Etempvar _perm tuint) ::
             (Etempvar _chunk tuint) :: (Etempvar _addr tulong) :: nil))
          (Sreturn (Some (Etempvar _t'4 tulong))))))))
|}.

Definition f_check_mem := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) ::
                (_perm, tuint) :: (_chunk, tuint) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_well_chunk, tbool) :: (_mem_reg_num, tuint) ::
               (_check_mem__1, tulong) :: (_t'3, tulong) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_well_chunk_bool (Tfunction (Tcons tuint Tnil) tbool
                                  cc_default))
      ((Etempvar _chunk tuint) :: nil))
    (Sset _well_chunk (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _well_chunk tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _eval_mem_num (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  Tnil) tuint cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
        (Sset _mem_reg_num (Etempvar _t'2 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _check_mem_aux (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil)))))
                                   tulong cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Etempvar _mem_reg_num tuint) :: (Etempvar _perm tuint) ::
             (Etempvar _chunk tuint) :: (Etempvar _addr tulong) :: nil))
          (Sset _check_mem__1 (Etempvar _t'3 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _check_mem__1 tulong)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))
          (Sreturn (Some (Etempvar _check_mem__1 tulong))))))
    (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))
|}.

Definition f_comp_and_0x08_byte := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_x, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq (Econst_int (Int.repr 0) tint)
                 (Ebinop Oand (Etempvar _x tuchar)
                   (Econst_int (Int.repr 8) tint) tint) tint)))
|}.

Definition f_step_opcode_alu64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_dst, tuint) ::
                (_dst64, tulong) :: (_src64, tulong) :: (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_alu64, tuchar) :: (_src32, tuint) :: (_t'5, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_alu64 (Tfunction (Tcons tuchar Tnil) tuchar
                                cc_default)) ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_alu64 (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_alu64 tuchar)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _upd_reg (Tfunction
                           (Tcons (tptr (Tstruct _bpf_state noattr))
                             (Tcons tuint (Tcons tulong Tnil))) tvoid
                           cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
           (Etempvar _dst tuint) ::
           (Ebinop Oadd (Etempvar _dst64 tulong) (Etempvar _src64 tulong)
             tulong) :: nil))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Sreturn None)))
      (LScons (Some 16)
        (Ssequence
          (Scall None
            (Evar _upd_reg (Tfunction
                             (Tcons (tptr (Tstruct _bpf_state noattr))
                               (Tcons tuint (Tcons tulong Tnil))) tvoid
                             cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Etempvar _dst tuint) ::
             (Ebinop Osub (Etempvar _dst64 tulong) (Etempvar _src64 tulong)
               tulong) :: nil))
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sreturn None)))
        (LScons (Some 32)
          (Ssequence
            (Scall None
              (Evar _upd_reg (Tfunction
                               (Tcons (tptr (Tstruct _bpf_state noattr))
                                 (Tcons tuint (Tcons tulong Tnil))) tvoid
                               cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Etempvar _dst tuint) ::
               (Ebinop Omul (Etempvar _dst64 tulong) (Etempvar _src64 tulong)
                 tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sreturn None)))
          (LScons (Some 48)
            (Sifthenelse (Ebinop One (Etempvar _src64 tulong)
                           (Econst_long (Int64.repr 0) tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_reg (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Etempvar _dst tuint) ::
                   (Ebinop Odiv (Etempvar _dst64 tulong)
                     (Etempvar _src64 tulong) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 9) tint) tint) :: nil))
                (Sreturn None)))
            (LScons (Some 64)
              (Ssequence
                (Scall None
                  (Evar _upd_reg (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Etempvar _dst tuint) ::
                   (Ebinop Oor (Etempvar _dst64 tulong)
                     (Etempvar _src64 tulong) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))
              (LScons (Some 80)
                (Ssequence
                  (Scall None
                    (Evar _upd_reg (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint (Tcons tulong Tnil)))
                                     tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Etempvar _dst tuint) ::
                     (Ebinop Oand (Etempvar _dst64 tulong)
                       (Etempvar _src64 tulong) tulong) :: nil))
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
                (LScons (Some 96)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _reg64_to_reg32 (Tfunction (Tcons tulong Tnil)
                                                tuint cc_default))
                        ((Etempvar _src64 tulong) :: nil))
                      (Sset _src32 (Etempvar _t'2 tuint)))
                    (Sifthenelse (Ebinop Olt (Etempvar _src64 tulong)
                                   (Econst_long (Int64.repr 64) tulong) tint)
                      (Ssequence
                        (Scall None
                          (Evar _upd_reg (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _bpf_state noattr))
                                             (Tcons tuint
                                               (Tcons tulong Tnil))) tvoid
                                           cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Etempvar _dst tuint) ::
                           (Ebinop Oshl (Etempvar _dst64 tulong)
                             (Etempvar _src32 tuint) tulong) :: nil))
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
                      (Ssequence
                        (Scall None
                          (Evar _upd_flag (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _bpf_state noattr))
                                              (Tcons tint Tnil)) tvoid
                                            cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Eunop Oneg (Econst_int (Int.repr 10) tint) tint) ::
                           nil))
                        (Sreturn None))))
                  (LScons (Some 112)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _reg64_to_reg32 (Tfunction
                                                  (Tcons tulong Tnil) tuint
                                                  cc_default))
                          ((Etempvar _src64 tulong) :: nil))
                        (Sset _src32 (Etempvar _t'3 tuint)))
                      (Sifthenelse (Ebinop Olt (Etempvar _src64 tulong)
                                     (Econst_long (Int64.repr 64) tulong)
                                     tint)
                        (Ssequence
                          (Scall None
                            (Evar _upd_reg (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _bpf_state noattr))
                                               (Tcons tuint
                                                 (Tcons tulong Tnil))) tvoid
                                             cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Etempvar _dst tuint) ::
                             (Ebinop Oshr (Etempvar _dst64 tulong)
                               (Etempvar _src32 tuint) tulong) :: nil))
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
                        (Ssequence
                          (Scall None
                            (Evar _upd_flag (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _bpf_state noattr))
                                                (Tcons tint Tnil)) tvoid
                                              cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Eunop Oneg (Econst_int (Int.repr 10) tint)
                               tint) :: nil))
                          (Sreturn None))))
                    (LScons (Some 128)
                      (Ssequence
                        (Scall None
                          (Evar _upd_reg (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _bpf_state noattr))
                                             (Tcons tuint
                                               (Tcons tulong Tnil))) tvoid
                                           cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Etempvar _dst tuint) ::
                           (Eunop Oneg (Etempvar _dst64 tulong) tulong) ::
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
                      (LScons (Some 144)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _reg64_to_reg32 (Tfunction
                                                      (Tcons tulong Tnil)
                                                      tuint cc_default))
                              ((Etempvar _src64 tulong) :: nil))
                            (Sset _src32 (Etempvar _t'4 tuint)))
                          (Sifthenelse (Ebinop One (Etempvar _src64 tulong)
                                         (Econst_long (Int64.repr 0) tulong)
                                         tint)
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
                                 (Ebinop Omod (Etempvar _dst64 tulong)
                                   (Etempvar _src32 tuint) tulong) :: nil))
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
                            (Ssequence
                              (Scall None
                                (Evar _upd_flag (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _bpf_state noattr))
                                                    (Tcons tint Tnil)) tvoid
                                                  cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Eunop Oneg (Econst_int (Int.repr 9) tint)
                                   tint) :: nil))
                              (Sreturn None))))
                        (LScons (Some 160)
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
                               (Ebinop Oxor (Etempvar _dst64 tulong)
                                 (Etempvar _src64 tulong) tulong) :: nil))
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
                          (LScons (Some 176)
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
                                 (Etempvar _src64 tulong) :: nil))
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
                            (LScons (Some 192)
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _reg64_to_reg32 (Tfunction
                                                            (Tcons tulong
                                                              Tnil) tuint
                                                            cc_default))
                                    ((Etempvar _src64 tulong) :: nil))
                                  (Sset _src32 (Etempvar _t'5 tuint)))
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _src64 tulong)
                                               (Econst_long (Int64.repr 64) tulong)
                                               tint)
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
                                       (Ebinop Oshr
                                         (Ecast (Etempvar _dst64 tulong)
                                           tlong) (Etempvar _src32 tuint)
                                         tlong) :: nil))
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
                                  (Ssequence
                                    (Scall None
                                      (Evar _upd_flag (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _bpf_state noattr))
                                                          (Tcons tint Tnil))
                                                        tvoid cc_default))
                                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                       (Eunop Oneg
                                         (Econst_int (Int.repr 10) tint)
                                         tint) :: nil))
                                    (Sreturn None))))
                              (LScons None
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_flag (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 1) tint) tint) ::
                                     nil))
                                  (Sreturn None))
                                LSnil))))))))))))))))
|}.

Definition f_step_opcode_alu32 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_dst, tuint) ::
                (_dst32, tuint) :: (_src32, tuint) :: (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_alu32, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_alu32 (Tfunction (Tcons tuchar Tnil) tuchar
                                cc_default)) ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_alu32 (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_alu32 tuchar)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _upd_reg (Tfunction
                           (Tcons (tptr (Tstruct _bpf_state noattr))
                             (Tcons tuint (Tcons tulong Tnil))) tvoid
                           cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
           (Etempvar _dst tuint) ::
           (Ecast
             (Ebinop Oadd (Etempvar _dst32 tuint) (Etempvar _src32 tuint)
               tuint) tulong) :: nil))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Sreturn None)))
      (LScons (Some 16)
        (Ssequence
          (Scall None
            (Evar _upd_reg (Tfunction
                             (Tcons (tptr (Tstruct _bpf_state noattr))
                               (Tcons tuint (Tcons tulong Tnil))) tvoid
                             cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Etempvar _dst tuint) ::
             (Ecast
               (Ebinop Osub (Etempvar _dst32 tuint) (Etempvar _src32 tuint)
                 tuint) tulong) :: nil))
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sreturn None)))
        (LScons (Some 32)
          (Ssequence
            (Scall None
              (Evar _upd_reg (Tfunction
                               (Tcons (tptr (Tstruct _bpf_state noattr))
                                 (Tcons tuint (Tcons tulong Tnil))) tvoid
                               cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Etempvar _dst tuint) ::
               (Ecast
                 (Ebinop Omul (Etempvar _dst32 tuint) (Etempvar _src32 tuint)
                   tuint) tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sreturn None)))
          (LScons (Some 48)
            (Sifthenelse (Ebinop One (Etempvar _src32 tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_reg (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Etempvar _dst tuint) ::
                   (Ecast
                     (Ebinop Odiv (Etempvar _dst32 tuint)
                       (Etempvar _src32 tuint) tuint) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 9) tint) tint) :: nil))
                (Sreturn None)))
            (LScons (Some 64)
              (Ssequence
                (Scall None
                  (Evar _upd_reg (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Etempvar _dst tuint) ::
                   (Ecast
                     (Ebinop Oor (Etempvar _dst32 tuint)
                       (Etempvar _src32 tuint) tuint) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))
              (LScons (Some 80)
                (Ssequence
                  (Scall None
                    (Evar _upd_reg (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint (Tcons tulong Tnil)))
                                     tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Etempvar _dst tuint) ::
                     (Ecast
                       (Ebinop Oand (Etempvar _dst32 tuint)
                         (Etempvar _src32 tuint) tuint) tulong) :: nil))
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
                (LScons (Some 96)
                  (Sifthenelse (Ebinop Olt (Etempvar _src32 tuint)
                                 (Econst_int (Int.repr 32) tuint) tint)
                    (Ssequence
                      (Scall None
                        (Evar _upd_reg (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _bpf_state noattr))
                                           (Tcons tuint (Tcons tulong Tnil)))
                                         tvoid cc_default))
                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                         (Etempvar _dst tuint) ::
                         (Ecast
                           (Ebinop Oshl (Etempvar _dst32 tuint)
                             (Etempvar _src32 tuint) tuint) tulong) :: nil))
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
                    (Ssequence
                      (Scall None
                        (Evar _upd_flag (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _bpf_state noattr))
                                            (Tcons tint Tnil)) tvoid
                                          cc_default))
                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                         (Eunop Oneg (Econst_int (Int.repr 10) tint) tint) ::
                         nil))
                      (Sreturn None)))
                  (LScons (Some 112)
                    (Sifthenelse (Ebinop Olt (Etempvar _src32 tuint)
                                   (Econst_int (Int.repr 32) tuint) tint)
                      (Ssequence
                        (Scall None
                          (Evar _upd_reg (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _bpf_state noattr))
                                             (Tcons tuint
                                               (Tcons tulong Tnil))) tvoid
                                           cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Etempvar _dst tuint) ::
                           (Ecast
                             (Ebinop Oshr (Etempvar _dst32 tuint)
                               (Etempvar _src32 tuint) tuint) tulong) :: nil))
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
                      (Ssequence
                        (Scall None
                          (Evar _upd_flag (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _bpf_state noattr))
                                              (Tcons tint Tnil)) tvoid
                                            cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Eunop Oneg (Econst_int (Int.repr 10) tint) tint) ::
                           nil))
                        (Sreturn None)))
                    (LScons (Some 128)
                      (Ssequence
                        (Scall None
                          (Evar _upd_reg (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _bpf_state noattr))
                                             (Tcons tuint
                                               (Tcons tulong Tnil))) tvoid
                                           cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Etempvar _dst tuint) ::
                           (Ecast (Eunop Oneg (Etempvar _dst32 tuint) tuint)
                             tulong) :: nil))
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
                      (LScons (Some 144)
                        (Sifthenelse (Ebinop One (Etempvar _src32 tuint)
                                       (Econst_int (Int.repr 0) tuint) tint)
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
                               (Ecast
                                 (Ebinop Omod (Etempvar _dst32 tuint)
                                   (Etempvar _src32 tuint) tuint) tulong) ::
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
                          (Ssequence
                            (Scall None
                              (Evar _upd_flag (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _bpf_state noattr))
                                                  (Tcons tint Tnil)) tvoid
                                                cc_default))
                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                               (Eunop Oneg (Econst_int (Int.repr 9) tint)
                                 tint) :: nil))
                            (Sreturn None)))
                        (LScons (Some 160)
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
                               (Ecast
                                 (Ebinop Oxor (Etempvar _dst32 tuint)
                                   (Etempvar _src32 tuint) tuint) tulong) ::
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
                          (LScons (Some 176)
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
                                 (Etempvar _src32 tuint) :: nil))
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
                            (LScons (Some 192)
                              (Sifthenelse (Ebinop Olt
                                             (Etempvar _src32 tuint)
                                             (Econst_int (Int.repr 32) tuint)
                                             tint)
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
                                     (Ecast
                                       (Ebinop Oshr
                                         (Ecast (Etempvar _dst32 tuint) tint)
                                         (Etempvar _src32 tuint) tint)
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
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_flag (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 10) tint) tint) ::
                                     nil))
                                  (Sreturn None)))
                              (LScons None
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_flag (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 1) tint) tint) ::
                                     nil))
                                  (Sreturn None))
                                LSnil))))))))))))))))
|}.

Definition f_step_opcode_branch := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_pc, tint) ::
                (_ofs, tint) :: (_dst64, tulong) :: (_src64, tulong) ::
                (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_jmp, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_branch (Tfunction (Tcons tuchar Tnil) tuchar
                                 cc_default)) ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_jmp (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_jmp tuchar)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _upd_pc (Tfunction
                          (Tcons (tptr (Tstruct _bpf_state noattr))
                            (Tcons tulong Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
           (Ebinop Oadd (Etempvar _pc tint) (Etempvar _ofs tint) tint) ::
           nil))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 0) tint) :: nil))
          (Sreturn None)))
      (LScons (Some 16)
        (Sifthenelse (Ebinop Oeq (Etempvar _dst64 tulong)
                       (Etempvar _src64 tulong) tint)
          (Ssequence
            (Scall None
              (Evar _upd_pc (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tulong Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Ebinop Oadd (Etempvar _pc tint) (Etempvar _ofs tint) tint) ::
               nil))
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sreturn None)))
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            (Sreturn None)))
        (LScons (Some 32)
          (Sifthenelse (Ebinop Ogt (Etempvar _dst64 tulong)
                         (Etempvar _src64 tulong) tint)
            (Ssequence
              (Scall None
                (Evar _upd_pc (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tulong Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Ebinop Oadd (Etempvar _pc tint) (Etempvar _ofs tint) tint) ::
                 nil))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Sreturn None)))
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sreturn None)))
          (LScons (Some 48)
            (Sifthenelse (Ebinop Oge (Etempvar _dst64 tulong)
                           (Etempvar _src64 tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_pc (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tulong Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Ebinop Oadd (Etempvar _pc tint) (Etempvar _ofs tint)
                     tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Sreturn None)))
            (LScons (Some 160)
              (Sifthenelse (Ebinop Olt (Etempvar _dst64 tulong)
                             (Etempvar _src64 tulong) tint)
                (Ssequence
                  (Scall None
                    (Evar _upd_pc (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tulong Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Ebinop Oadd (Etempvar _pc tint) (Etempvar _ofs tint)
                       tint) :: nil))
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
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))
              (LScons (Some 176)
                (Sifthenelse (Ebinop Ole (Etempvar _dst64 tulong)
                               (Etempvar _src64 tulong) tint)
                  (Ssequence
                    (Scall None
                      (Evar _upd_pc (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tulong Tnil)) tvoid
                                      cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Ebinop Oadd (Etempvar _pc tint) (Etempvar _ofs tint)
                         tint) :: nil))
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
                (LScons (Some 64)
                  (Sifthenelse (Ebinop One
                                 (Ebinop Oand (Etempvar _dst64 tulong)
                                   (Etempvar _src64 tulong) tulong)
                                 (Econst_long (Int64.repr 0) tulong) tint)
                    (Ssequence
                      (Scall None
                        (Evar _upd_pc (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _bpf_state noattr))
                                          (Tcons tulong Tnil)) tvoid
                                        cc_default))
                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                         (Ebinop Oadd (Etempvar _pc tint)
                           (Etempvar _ofs tint) tint) :: nil))
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
                  (LScons (Some 80)
                    (Sifthenelse (Ebinop One (Etempvar _dst64 tulong)
                                   (Etempvar _src64 tulong) tint)
                      (Ssequence
                        (Scall None
                          (Evar _upd_pc (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _bpf_state noattr))
                                            (Tcons tulong Tnil)) tvoid
                                          cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Ebinop Oadd (Etempvar _pc tint)
                             (Etempvar _ofs tint) tint) :: nil))
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
                    (LScons (Some 96)
                      (Sifthenelse (Ebinop Ogt
                                     (Ecast (Etempvar _dst64 tulong) tlong)
                                     (Ecast (Etempvar _src64 tulong) tlong)
                                     tint)
                        (Ssequence
                          (Scall None
                            (Evar _upd_pc (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _bpf_state noattr))
                                              (Tcons tulong Tnil)) tvoid
                                            cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Ebinop Oadd (Etempvar _pc tint)
                               (Etempvar _ofs tint) tint) :: nil))
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
                      (LScons (Some 112)
                        (Sifthenelse (Ebinop Oge
                                       (Ecast (Etempvar _dst64 tulong) tlong)
                                       (Ecast (Etempvar _src64 tulong) tlong)
                                       tint)
                          (Ssequence
                            (Scall None
                              (Evar _upd_pc (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _bpf_state noattr))
                                                (Tcons tulong Tnil)) tvoid
                                              cc_default))
                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                               (Ebinop Oadd (Etempvar _pc tint)
                                 (Etempvar _ofs tint) tint) :: nil))
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
                        (LScons (Some 192)
                          (Sifthenelse (Ebinop Olt
                                         (Ecast (Etempvar _dst64 tulong)
                                           tlong)
                                         (Ecast (Etempvar _src64 tulong)
                                           tlong) tint)
                            (Ssequence
                              (Scall None
                                (Evar _upd_pc (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _bpf_state noattr))
                                                  (Tcons tulong Tnil)) tvoid
                                                cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Ebinop Oadd (Etempvar _pc tint)
                                   (Etempvar _ofs tint) tint) :: nil))
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
                          (LScons (Some 208)
                            (Sifthenelse (Ebinop Ole
                                           (Ecast (Etempvar _dst64 tulong)
                                             tlong)
                                           (Ecast (Etempvar _src64 tulong)
                                             tlong) tint)
                              (Ssequence
                                (Scall None
                                  (Evar _upd_pc (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _bpf_state noattr))
                                                    (Tcons tulong Tnil))
                                                  tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Ebinop Oadd (Etempvar _pc tint)
                                     (Etempvar _ofs tint) tint) :: nil))
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
                            (LScons (Some 144)
                              (Ssequence
                                (Scall None
                                  (Evar _upd_flag (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _bpf_state noattr))
                                                      (Tcons tint Tnil))
                                                    tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Econst_int (Int.repr 1) tint) :: nil))
                                (Sreturn None))
                              (LScons None
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_flag (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 1) tint) tint) ::
                                     nil))
                                  (Sreturn None))
                                LSnil))))))))))))))))
|}.

Definition f_step_opcode_mem_ld_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_pc, tint) ::
                (_len, tint) :: (_dst, tuint) :: (_dst64, tulong) ::
                (_imm, tint) :: (_op, tuchar) :: (_l, (tptr tulong)) :: nil);
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

Definition f_step_opcode_mem_ld_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_pc, tint) ::
                (_dst, tuint) :: (_dst64, tulong) :: (_src64, tulong) ::
                (_op, tuchar) :: (_ofs64, tulong) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_ld, tuchar) :: (_check_ld, tulong) :: (_v, tulong) ::
               (_t'9, tulong) :: (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_ld_reg (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_ld (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_ld tuchar)
    (LScons (Some 97)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem (Tfunction
                               (Tcons (tptr (Tstruct _bpf_state noattr))
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tulong Tnil)))) tulong
                               cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 1) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: (Etempvar _addr tulong) ::
             nil))
          (Sset _check_ld (Etempvar _t'2 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _check_ld tulong)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
            (Sreturn None))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _load_mem (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tuint (Tcons tulong Tnil))) tulong
                                  cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 4) tuint) ::
                 (Ebinop Oadd (Etempvar _src64 tulong)
                   (Etempvar _ofs64 tulong) tulong) :: nil))
              (Sset _v (Etempvar _t'3 tulong)))
            (Ssequence
              (Scall None
                (Evar _upd_reg (Tfunction
                                 (Tcons (tptr (Tstruct _bpf_state noattr))
                                   (Tcons tuint (Tcons tulong Tnil))) tvoid
                                 cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Etempvar _dst tuint) :: (Etempvar _v tulong) :: nil))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Sreturn None))))))
      (LScons (Some 105)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _check_mem (Tfunction
                                 (Tcons (tptr (Tstruct _bpf_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tulong Tnil))))
                                 tulong cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 1) tuint) ::
               (Econst_int (Int.repr 2) tuint) :: (Etempvar _addr tulong) ::
               nil))
            (Sset _check_ld (Etempvar _t'4 tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _check_ld tulong)
                         (Econst_long (Int64.repr 0) tulong) tint)
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
              (Sreturn None))
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _load_mem (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tuint (Tcons tulong Tnil)))
                                    tulong cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 2) tuint) ::
                   (Ebinop Oadd (Etempvar _src64 tulong)
                     (Etempvar _ofs64 tulong) tulong) :: nil))
                (Sset _v (Etempvar _t'5 tulong)))
              (Ssequence
                (Scall None
                  (Evar _upd_reg (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Etempvar _dst tuint) :: (Etempvar _v tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None))))))
        (LScons (Some 113)
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _check_mem (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tulong Tnil))))
                                   tulong cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 1) tuint) ::
                 (Econst_int (Int.repr 1) tuint) ::
                 (Etempvar _addr tulong) :: nil))
              (Sset _check_ld (Etempvar _t'6 tulong)))
            (Sifthenelse (Ebinop Oeq (Etempvar _check_ld tulong)
                           (Econst_long (Int64.repr 0) tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
                (Sreturn None))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _load_mem (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tulong cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 1) tuint) ::
                     (Ebinop Oadd (Etempvar _src64 tulong)
                       (Etempvar _ofs64 tulong) tulong) :: nil))
                  (Sset _v (Etempvar _t'7 tulong)))
                (Ssequence
                  (Scall None
                    (Evar _upd_reg (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint (Tcons tulong Tnil)))
                                     tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Etempvar _dst tuint) :: (Etempvar _v tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _upd_flag (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _bpf_state noattr))
                                          (Tcons tint Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Econst_int (Int.repr 0) tint) :: nil))
                    (Sreturn None))))))
          (LScons (Some 121)
            (Ssequence
              (Ssequence
                (Scall (Some _t'8)
                  (Evar _check_mem (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil))))
                                     tulong cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 1) tuint) ::
                   (Econst_int (Int.repr 8) tuint) ::
                   (Etempvar _addr tulong) :: nil))
                (Sset _check_ld (Etempvar _t'8 tulong)))
              (Sifthenelse (Ebinop Oeq (Etempvar _check_ld tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'9)
                      (Evar _load_mem (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _bpf_state noattr))
                                          (Tcons tuint (Tcons tulong Tnil)))
                                        tulong cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Econst_int (Int.repr 8) tuint) ::
                       (Ebinop Oadd (Etempvar _src64 tulong)
                         (Etempvar _ofs64 tulong) tulong) :: nil))
                    (Sset _v (Etempvar _t'9 tulong)))
                  (Ssequence
                    (Scall None
                      (Evar _upd_reg (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _bpf_state noattr))
                                         (Tcons tuint (Tcons tulong Tnil)))
                                       tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Etempvar _dst tuint) :: (Etempvar _v tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _upd_flag (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _bpf_state noattr))
                                            (Tcons tint Tnil)) tvoid
                                          cc_default))
                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                         (Econst_int (Int.repr 0) tint) :: nil))
                      (Sreturn None))))))
            (LScons None
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
                (Sreturn None))
              LSnil)))))))
|}.

Definition f_step_opcode_mem_st_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_pc, tint) ::
                (_dst, tuint) :: (_dst64, tulong) :: (_imm, tint) ::
                (_op, tuchar) :: (_ofs64, tulong) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_st, tuchar) :: (_check_st, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_st_imm (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_st (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_st tuchar)
    (LScons (Some 98)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem (Tfunction
                               (Tcons (tptr (Tstruct _bpf_state noattr))
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tulong Tnil)))) tulong
                               cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 2) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: (Etempvar _addr tulong) ::
             nil))
          (Sset _check_st (Etempvar _t'2 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
            (Sreturn None))
          (Ssequence
            (Scall None
              (Evar _store_mem_imm (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint
                                         (Tcons tulong (Tcons tint Tnil))))
                                     tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 4) tuint) ::
               (Ebinop Oadd (Etempvar _dst64 tulong) (Etempvar _ofs64 tulong)
                 tulong) :: (Etempvar _imm tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sreturn None)))))
      (LScons (Some 106)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _check_mem (Tfunction
                                 (Tcons (tptr (Tstruct _bpf_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tulong Tnil))))
                                 tulong cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 2) tuint) ::
               (Econst_int (Int.repr 2) tuint) :: (Etempvar _addr tulong) ::
               nil))
            (Sset _check_st (Etempvar _t'3 tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                         (Econst_long (Int64.repr 0) tulong) tint)
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
              (Sreturn None))
            (Ssequence
              (Scall None
                (Evar _store_mem_imm (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _bpf_state noattr))
                                         (Tcons tuint
                                           (Tcons tulong (Tcons tint Tnil))))
                                       tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) ::
                 (Ebinop Oadd (Etempvar _dst64 tulong)
                   (Etempvar _ofs64 tulong) tulong) ::
                 (Etempvar _imm tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Sreturn None)))))
        (LScons (Some 114)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _check_mem (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tulong Tnil))))
                                   tulong cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) ::
                 (Econst_int (Int.repr 1) tuint) ::
                 (Etempvar _addr tulong) :: nil))
              (Sset _check_st (Etempvar _t'4 tulong)))
            (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                           (Econst_long (Int64.repr 0) tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
                (Sreturn None))
              (Ssequence
                (Scall None
                  (Evar _store_mem_imm (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _bpf_state noattr))
                                           (Tcons tuint
                                             (Tcons tulong (Tcons tint Tnil))))
                                         tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 1) tuint) ::
                   (Ebinop Oadd (Etempvar _dst64 tulong)
                     (Etempvar _ofs64 tulong) tulong) ::
                   (Etempvar _imm tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))))
          (LScons (Some 122)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _check_mem (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil))))
                                     tulong cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 2) tuint) ::
                   (Econst_int (Int.repr 8) tuint) ::
                   (Etempvar _addr tulong) :: nil))
                (Sset _check_st (Etempvar _t'5 tulong)))
              (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Scall None
                    (Evar _store_mem_imm (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _bpf_state noattr))
                                             (Tcons tuint
                                               (Tcons tulong
                                                 (Tcons tint Tnil)))) tvoid
                                           cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 8) tuint) ::
                     (Ebinop Oadd (Etempvar _dst64 tulong)
                       (Etempvar _ofs64 tulong) tulong) ::
                     (Etempvar _imm tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _upd_flag (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _bpf_state noattr))
                                          (Tcons tint Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Econst_int (Int.repr 0) tint) :: nil))
                    (Sreturn None)))))
            (LScons None
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
                (Sreturn None))
              LSnil)))))))
|}.

Definition f_step_opcode_mem_st_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_pc, tint) ::
                (_dst, tuint) :: (_dst64, tulong) :: (_src64, tulong) ::
                (_op, tuchar) :: (_ofs64, tulong) :: (_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_st, tuchar) :: (_check_st, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_st_reg (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_st (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_st tuchar)
    (LScons (Some 99)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem (Tfunction
                               (Tcons (tptr (Tstruct _bpf_state noattr))
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tulong Tnil)))) tulong
                               cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
             (Econst_int (Int.repr 2) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: (Etempvar _addr tulong) ::
             nil))
          (Sset _check_st (Etempvar _t'2 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
            (Sreturn None))
          (Ssequence
            (Scall None
              (Evar _store_mem_reg (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint
                                         (Tcons tulong (Tcons tulong Tnil))))
                                     tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 4) tuint) ::
               (Ebinop Oadd (Etempvar _dst64 tulong) (Etempvar _ofs64 tulong)
                 tulong) :: (Etempvar _src64 tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 0) tint) :: nil))
              (Sreturn None)))))
      (LScons (Some 107)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _check_mem (Tfunction
                                 (Tcons (tptr (Tstruct _bpf_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tulong Tnil))))
                                 tulong cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 2) tuint) ::
               (Econst_int (Int.repr 2) tuint) :: (Etempvar _addr tulong) ::
               nil))
            (Sset _check_st (Etempvar _t'3 tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                         (Econst_long (Int64.repr 0) tulong) tint)
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _bpf_state noattr))
                                    (Tcons tint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
              (Sreturn None))
            (Ssequence
              (Scall None
                (Evar _store_mem_reg (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _bpf_state noattr))
                                         (Tcons tuint
                                           (Tcons tulong (Tcons tulong Tnil))))
                                       tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) ::
                 (Ebinop Oadd (Etempvar _dst64 tulong)
                   (Etempvar _ofs64 tulong) tulong) ::
                 (Etempvar _src64 tulong) :: nil))
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Sreturn None)))))
        (LScons (Some 115)
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _check_mem (Tfunction
                                   (Tcons (tptr (Tstruct _bpf_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tulong Tnil))))
                                   tulong cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) ::
                 (Econst_int (Int.repr 1) tuint) ::
                 (Etempvar _addr tulong) :: nil))
              (Sset _check_st (Etempvar _t'4 tulong)))
            (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                           (Econst_long (Int64.repr 0) tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
                (Sreturn None))
              (Ssequence
                (Scall None
                  (Evar _store_mem_reg (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _bpf_state noattr))
                                           (Tcons tuint
                                             (Tcons tulong
                                               (Tcons tulong Tnil)))) tvoid
                                         cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 1) tuint) ::
                   (Ebinop Oadd (Etempvar _dst64 tulong)
                     (Etempvar _ofs64 tulong) tulong) ::
                   (Etempvar _src64 tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sreturn None)))))
          (LScons (Some 123)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _check_mem (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tuint
                                         (Tcons tuint (Tcons tulong Tnil))))
                                     tulong cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Econst_int (Int.repr 2) tuint) ::
                   (Econst_int (Int.repr 8) tuint) ::
                   (Etempvar _addr tulong) :: nil))
                (Sset _check_st (Etempvar _t'5 tulong)))
              (Sifthenelse (Ebinop Oeq (Etempvar _check_st tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Eunop Oneg (Econst_int (Int.repr 2) tint) tint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Scall None
                    (Evar _store_mem_reg (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _bpf_state noattr))
                                             (Tcons tuint
                                               (Tcons tulong
                                                 (Tcons tulong Tnil)))) tvoid
                                           cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Econst_int (Int.repr 8) tuint) ::
                     (Ebinop Oadd (Etempvar _dst64 tulong)
                       (Etempvar _ofs64 tulong) tulong) ::
                     (Etempvar _src64 tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _upd_flag (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _bpf_state noattr))
                                          (Tcons tint Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Econst_int (Int.repr 0) tint) :: nil))
                    (Sreturn None)))))
            (LScons None
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons (tptr (Tstruct _bpf_state noattr))
                                      (Tcons tint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                   (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
                (Sreturn None))
              LSnil)))))))
|}.

Definition f_step := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_len, tint) ::
                (_l, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_pc, tint) :: (_ins, tulong) :: (_op, tuchar) ::
               (_opc, tuchar) :: (_dst, tuint) :: (_dst64, tulong) ::
               (_is_imm, tbool) :: (_imm, tint) :: (_imm64, tulong) ::
               (_src, tuint) :: (_src64, tulong) :: (_dst32, tuint) ::
               (_src32, tuint) :: (_ofs, tint) :: (_ofs64, tulong) ::
               (_addr, tulong) :: (_t'50, tulong) :: (_t'49, tulong) ::
               (_t'48, tint) :: (_t'47, tulong) :: (_t'46, tuint) ::
               (_t'45, tulong) :: (_t'44, tuint) :: (_t'43, tulong) ::
               (_t'42, tint) :: (_t'41, tulong) :: (_t'40, tint) ::
               (_t'39, tulong) :: (_t'38, tuint) :: (_t'37, tulong) ::
               (_t'36, tulong) :: (_t'35, tint) :: (_t'34, tulong) ::
               (_t'33, tuint) :: (_t'32, tulong) :: (_t'31, tuint) ::
               (_t'30, tint) :: (_t'29, tulong) :: (_t'28, tuint) ::
               (_t'27, tulong) :: (_t'26, tuint) :: (_t'25, tulong) ::
               (_t'24, tint) :: (_t'23, tbool) :: (_t'22, tint) ::
               (_t'21, tulong) :: (_t'20, tuint) :: (_t'19, tuint) ::
               (_t'18, tulong) :: (_t'17, tuint) :: (_t'16, tint) ::
               (_t'15, tbool) :: (_t'14, tuint) :: (_t'13, tulong) ::
               (_t'12, tuint) :: (_t'11, tulong) :: (_t'10, tuint) ::
               (_t'9, tulong) :: (_t'8, tint) :: (_t'7, tbool) ::
               (_t'6, tulong) :: (_t'5, tuint) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_pc (Tfunction
                       (Tcons (tptr (Tstruct _bpf_state noattr)) Tnil) tulong
                       cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
    (Sset _pc (Ecast (Etempvar _t'1 tulong) tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _list_get (Tfunction (Tcons (tptr tulong) (Tcons tint Tnil))
                          tulong cc_default))
        ((Etempvar _l (tptr tulong)) :: (Etempvar _pc tint) :: nil))
      (Sset _ins (Etempvar _t'2 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_opcode_ins (Tfunction (Tcons tulong Tnil) tuchar
                                  cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _op (Ecast (Etempvar _t'3 tuchar) tuchar)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_opcode (Tfunction (Tcons tuchar Tnil) tuchar
                                cc_default)) ((Etempvar _op tuchar) :: nil))
          (Sset _opc (Ecast (Etempvar _t'4 tuchar) tuchar)))
        (Sswitch (Etempvar _opc tuchar)
          (LScons (Some 7)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
                  ((Etempvar _ins tulong) :: nil))
                (Sset _dst (Etempvar _t'5 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _eval_reg (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _bpf_state noattr))
                                        (Tcons tuint Tnil)) tulong
                                      cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     (Etempvar _dst tuint) :: nil))
                  (Sset _dst64 (Etempvar _t'6 tulong)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _comp_and_0x08_byte (Tfunction
                                                  (Tcons tuchar Tnil) tbool
                                                  cc_default))
                      ((Etempvar _op tuchar) :: nil))
                    (Sset _is_imm (Ecast (Etempvar _t'7 tbool) tbool)))
                  (Sifthenelse (Etempvar _is_imm tbool)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'8)
                          (Evar _get_immediate (Tfunction (Tcons tulong Tnil)
                                                 tint cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _imm (Etempvar _t'8 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'9)
                            (Evar _eval_immediate (Tfunction
                                                    (Tcons tint Tnil) tulong
                                                    cc_default))
                            ((Etempvar _imm tint) :: nil))
                          (Sset _imm64 (Etempvar _t'9 tulong)))
                        (Ssequence
                          (Scall None
                            (Evar _step_opcode_alu64 (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _bpf_state noattr))
                                                         (Tcons tuint
                                                           (Tcons tulong
                                                             (Tcons tulong
                                                               (Tcons tuchar
                                                                 Tnil)))))
                                                       tvoid cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Etempvar _dst tuint) ::
                             (Etempvar _dst64 tulong) ::
                             (Etempvar _imm64 tulong) ::
                             (Etempvar _op tuchar) :: nil))
                          (Sreturn None))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'10)
                          (Evar _get_src (Tfunction (Tcons tulong Tnil) tuint
                                           cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _src (Etempvar _t'10 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'11)
                            (Evar _eval_reg (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _bpf_state noattr))
                                                (Tcons tuint Tnil)) tulong
                                              cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Etempvar _src tuint) :: nil))
                          (Sset _src64 (Etempvar _t'11 tulong)))
                        (Ssequence
                          (Scall None
                            (Evar _step_opcode_alu64 (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _bpf_state noattr))
                                                         (Tcons tuint
                                                           (Tcons tulong
                                                             (Tcons tulong
                                                               (Tcons tuchar
                                                                 Tnil)))))
                                                       tvoid cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Etempvar _dst tuint) ::
                             (Etempvar _dst64 tulong) ::
                             (Etempvar _src64 tulong) ::
                             (Etempvar _op tuchar) :: nil))
                          (Sreturn None))))))))
            (LScons (Some 4)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'12)
                    (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _dst (Etempvar _t'12 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'13)
                      (Evar _eval_reg (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _bpf_state noattr))
                                          (Tcons tuint Tnil)) tulong
                                        cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Etempvar _dst tuint) :: nil))
                    (Sset _dst64 (Etempvar _t'13 tulong)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'14)
                        (Evar _reg64_to_reg32 (Tfunction (Tcons tulong Tnil)
                                                tuint cc_default))
                        ((Etempvar _dst64 tulong) :: nil))
                      (Sset _dst32 (Etempvar _t'14 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'15)
                          (Evar _comp_and_0x08_byte (Tfunction
                                                      (Tcons tuchar Tnil)
                                                      tbool cc_default))
                          ((Etempvar _op tuchar) :: nil))
                        (Sset _is_imm (Ecast (Etempvar _t'15 tbool) tbool)))
                      (Sifthenelse (Etempvar _is_imm tbool)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'16)
                              (Evar _get_immediate (Tfunction
                                                     (Tcons tulong Tnil) tint
                                                     cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _imm (Etempvar _t'16 tint)))
                          (Ssequence
                            (Scall None
                              (Evar _step_opcode_alu32 (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _bpf_state noattr))
                                                           (Tcons tuint
                                                             (Tcons tuint
                                                               (Tcons tuint
                                                                 (Tcons
                                                                   tuchar
                                                                   Tnil)))))
                                                         tvoid cc_default))
                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                               (Etempvar _pc tint) ::
                               (Etempvar _dst32 tuint) ::
                               (Etempvar _imm tint) ::
                               (Etempvar _op tuchar) :: nil))
                            (Sreturn None)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'17)
                              (Evar _get_src (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _src (Etempvar _t'17 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'18)
                                (Evar _eval_reg (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _bpf_state noattr))
                                                    (Tcons tuint Tnil))
                                                  tulong cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Etempvar _src tuint) :: nil))
                              (Sset _src64 (Etempvar _t'18 tulong)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'19)
                                  (Evar _reg64_to_reg32 (Tfunction
                                                          (Tcons tulong Tnil)
                                                          tuint cc_default))
                                  ((Etempvar _src64 tulong) :: nil))
                                (Sset _src32 (Etempvar _t'19 tuint)))
                              (Ssequence
                                (Scall None
                                  (Evar _step_opcode_alu32 (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _bpf_state noattr))
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil)))))
                                                             tvoid
                                                             cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Etempvar _pc tint) ::
                                   (Etempvar _dst32 tuint) ::
                                   (Etempvar _src32 tuint) ::
                                   (Etempvar _op tuchar) :: nil))
                                (Sreturn None))))))))))
              (LScons (Some 5)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'20)
                      (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _dst (Etempvar _t'20 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'21)
                        (Evar _eval_reg (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _bpf_state noattr))
                                            (Tcons tuint Tnil)) tulong
                                          cc_default))
                        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                         (Etempvar _dst tuint) :: nil))
                      (Sset _dst64 (Etempvar _t'21 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'22)
                          (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                              tint cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _ofs (Etempvar _t'22 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'23)
                            (Evar _comp_and_0x08_byte (Tfunction
                                                        (Tcons tuchar Tnil)
                                                        tbool cc_default))
                            ((Etempvar _op tuchar) :: nil))
                          (Sset _is_imm (Ecast (Etempvar _t'23 tbool) tbool)))
                        (Sifthenelse (Etempvar _is_imm tbool)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'24)
                                (Evar _get_immediate (Tfunction
                                                       (Tcons tulong Tnil)
                                                       tint cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _imm (Etempvar _t'24 tint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'25)
                                  (Evar _eval_immediate (Tfunction
                                                          (Tcons tint Tnil)
                                                          tulong cc_default))
                                  ((Etempvar _imm tint) :: nil))
                                (Sset _imm64 (Etempvar _t'25 tulong)))
                              (Ssequence
                                (Scall None
                                  (Evar _step_opcode_branch (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _bpf_state noattr))
                                                                (Tcons tint
                                                                  (Tcons tint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))))))
                                                              tvoid
                                                              cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Etempvar _pc tint) ::
                                   (Etempvar _ofs tint) ::
                                   (Etempvar _dst64 tulong) ::
                                   (Etempvar _imm64 tulong) ::
                                   (Etempvar _op tuchar) :: nil))
                                (Sreturn None))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'26)
                                (Evar _get_src (Tfunction (Tcons tulong Tnil)
                                                 tuint cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _src (Etempvar _t'26 tuint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'27)
                                  (Evar _eval_reg (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _bpf_state noattr))
                                                      (Tcons tuint Tnil))
                                                    tulong cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Etempvar _src tuint) :: nil))
                                (Sset _src64 (Etempvar _t'27 tulong)))
                              (Ssequence
                                (Scall None
                                  (Evar _step_opcode_branch (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _bpf_state noattr))
                                                                (Tcons tint
                                                                  (Tcons tint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))))))
                                                              tvoid
                                                              cc_default))
                                  ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                   (Etempvar _pc tint) ::
                                   (Etempvar _ofs tint) ::
                                   (Etempvar _dst64 tulong) ::
                                   (Etempvar _src64 tulong) ::
                                   (Etempvar _op tuchar) :: nil))
                                (Sreturn None)))))))))
                (LScons (Some 0)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'28)
                        (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint
                                         cc_default))
                        ((Etempvar _ins tulong) :: nil))
                      (Sset _dst (Etempvar _t'28 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'29)
                          (Evar _eval_reg (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _bpf_state noattr))
                                              (Tcons tuint Tnil)) tulong
                                            cc_default))
                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                           (Etempvar _dst tuint) :: nil))
                        (Sset _dst64 (Etempvar _t'29 tulong)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'30)
                            (Evar _get_immediate (Tfunction
                                                   (Tcons tulong Tnil) tint
                                                   cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _imm (Etempvar _t'30 tint)))
                        (Ssequence
                          (Scall None
                            (Evar _step_opcode_mem_ld_imm (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _bpf_state noattr))
                                                              (Tcons tint
                                                                (Tcons tint
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    (tptr tulong)
                                                                    Tnil))))))))
                                                            tvoid cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Etempvar _pc tint) :: (Etempvar _len tint) ::
                             (Etempvar _dst tuint) ::
                             (Etempvar _dst64 tulong) ::
                             (Etempvar _imm tint) :: (Etempvar _op tuchar) ::
                             (Etempvar _l (tptr tulong)) :: nil))
                          (Sreturn None)))))
                  (LScons (Some 1)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'31)
                          (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint
                                           cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _dst (Etempvar _t'31 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'32)
                            (Evar _eval_reg (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _bpf_state noattr))
                                                (Tcons tuint Tnil)) tulong
                                              cc_default))
                            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                             (Etempvar _dst tuint) :: nil))
                          (Sset _dst64 (Etempvar _t'32 tulong)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'33)
                              (Evar _get_src (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _src (Etempvar _t'33 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'34)
                                (Evar _eval_reg (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _bpf_state noattr))
                                                    (Tcons tuint Tnil))
                                                  tulong cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Etempvar _src tuint) :: nil))
                              (Sset _src64 (Etempvar _t'34 tulong)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'35)
                                  (Evar _get_offset (Tfunction
                                                      (Tcons tulong Tnil)
                                                      tint cc_default))
                                  ((Etempvar _ins tulong) :: nil))
                                (Sset _ofs (Etempvar _t'35 tint)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'36)
                                    (Evar _eval_immediate (Tfunction
                                                            (Tcons tint Tnil)
                                                            tulong
                                                            cc_default))
                                    ((Etempvar _ofs tint) :: nil))
                                  (Sset _ofs64 (Etempvar _t'36 tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'37)
                                      (Evar _get_addl (Tfunction
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil))
                                                        tulong cc_default))
                                      ((Etempvar _src64 tulong) ::
                                       (Etempvar _ofs64 tulong) :: nil))
                                    (Sset _addr (Etempvar _t'37 tulong)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _step_opcode_mem_ld_reg (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    cc_default))
                                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                       (Etempvar _pc tint) ::
                                       (Etempvar _dst tuint) ::
                                       (Etempvar _dst64 tulong) ::
                                       (Etempvar _src64 tulong) ::
                                       (Etempvar _op tuchar) ::
                                       (Etempvar _ofs64 tulong) ::
                                       (Etempvar _addr tulong) :: nil))
                                    (Sreturn None)))))))))
                    (LScons (Some 2)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'38)
                            (Evar _get_dst (Tfunction (Tcons tulong Tnil)
                                             tuint cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _dst (Etempvar _t'38 tuint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'39)
                              (Evar _eval_reg (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _bpf_state noattr))
                                                  (Tcons tuint Tnil)) tulong
                                                cc_default))
                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                               (Etempvar _dst tuint) :: nil))
                            (Sset _dst64 (Etempvar _t'39 tulong)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'40)
                                (Evar _get_offset (Tfunction
                                                    (Tcons tulong Tnil) tint
                                                    cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _ofs (Etempvar _t'40 tint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'41)
                                  (Evar _eval_immediate (Tfunction
                                                          (Tcons tint Tnil)
                                                          tulong cc_default))
                                  ((Etempvar _ofs tint) :: nil))
                                (Sset _ofs64 (Etempvar _t'41 tulong)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'42)
                                    (Evar _get_immediate (Tfunction
                                                           (Tcons tulong
                                                             Tnil) tint
                                                           cc_default))
                                    ((Etempvar _ins tulong) :: nil))
                                  (Sset _imm (Etempvar _t'42 tint)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'43)
                                      (Evar _get_addl (Tfunction
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil))
                                                        tulong cc_default))
                                      ((Etempvar _dst64 tulong) ::
                                       (Etempvar _ofs64 tulong) :: nil))
                                    (Sset _addr (Etempvar _t'43 tulong)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _step_opcode_mem_st_imm (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _bpf_state noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tulong
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil))))))))
                                                                    tvoid
                                                                    cc_default))
                                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                       (Etempvar _pc tint) ::
                                       (Etempvar _dst tuint) ::
                                       (Etempvar _dst64 tulong) ::
                                       (Etempvar _imm tint) ::
                                       (Etempvar _op tuchar) ::
                                       (Etempvar _ofs64 tulong) ::
                                       (Etempvar _addr tulong) :: nil))
                                    (Sreturn None))))))))
                      (LScons (Some 3)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'44)
                              (Evar _get_dst (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
                              ((Etempvar _ins tulong) :: nil))
                            (Sset _dst (Etempvar _t'44 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'45)
                                (Evar _eval_reg (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _bpf_state noattr))
                                                    (Tcons tuint Tnil))
                                                  tulong cc_default))
                                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                 (Etempvar _dst tuint) :: nil))
                              (Sset _dst64 (Etempvar _t'45 tulong)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'46)
                                  (Evar _get_src (Tfunction
                                                   (Tcons tulong Tnil) tuint
                                                   cc_default))
                                  ((Etempvar _ins tulong) :: nil))
                                (Sset _src (Etempvar _t'46 tuint)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'47)
                                    (Evar _eval_reg (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        (Tcons tuint Tnil))
                                                      tulong cc_default))
                                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                     (Etempvar _src tuint) :: nil))
                                  (Sset _src64 (Etempvar _t'47 tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'48)
                                      (Evar _get_offset (Tfunction
                                                          (Tcons tulong Tnil)
                                                          tint cc_default))
                                      ((Etempvar _ins tulong) :: nil))
                                    (Sset _ofs (Etempvar _t'48 tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'49)
                                        (Evar _eval_immediate (Tfunction
                                                                (Tcons tint
                                                                  Tnil)
                                                                tulong
                                                                cc_default))
                                        ((Etempvar _ofs tint) :: nil))
                                      (Sset _ofs64 (Etempvar _t'49 tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'50)
                                          (Evar _get_addl (Tfunction
                                                            (Tcons tulong
                                                              (Tcons tulong
                                                                Tnil)) tulong
                                                            cc_default))
                                          ((Etempvar _dst64 tulong) ::
                                           (Etempvar _ofs64 tulong) :: nil))
                                        (Sset _addr (Etempvar _t'50 tulong)))
                                      (Ssequence
                                        (Scall None
                                          (Evar _step_opcode_mem_st_reg 
                                          (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _bpf_state noattr))
                                              (Tcons tint
                                                (Tcons tuint
                                                  (Tcons tulong
                                                    (Tcons tulong
                                                      (Tcons tuchar
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil))))))))
                                            tvoid cc_default))
                                          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                                           (Etempvar _pc tint) ::
                                           (Etempvar _dst tuint) ::
                                           (Etempvar _dst64 tulong) ::
                                           (Etempvar _src64 tulong) ::
                                           (Etempvar _op tuchar) ::
                                           (Etempvar _ofs64 tulong) ::
                                           (Etempvar _addr tulong) :: nil))
                                        (Sreturn None)))))))))
                        (LScons None
                          (Ssequence
                            (Scall None
                              (Evar _upd_flag (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _bpf_state noattr))
                                                  (Tcons tint Tnil)) tvoid
                                                cc_default))
                              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                               (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint) :: nil))
                            (Sreturn None))
                          LSnil)))))))))))))
|}.

Definition f_bpf_interpreter_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_len, tint) ::
                (_fuel, tuint) :: (_l, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_fuel0, tuint) :: (_pc, tint) :: (_f, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _fuel tuint)
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
      (Ebinop Osub (Etempvar _fuel tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_pc (Tfunction
                           (Tcons (tptr (Tstruct _bpf_state noattr)) Tnil)
                           tulong cc_default))
          ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
        (Sset _pc (Ecast (Etempvar _t'1 tulong) tint)))
      (Ssequence
        (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tuint)
                       (Etempvar _pc tint) tint)
          (Sset _t'3
            (Ecast (Ebinop Olt (Etempvar _pc tint) (Etempvar _len tint) tint)
              tbool))
          (Sset _t'3 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'3 tint)
          (Ssequence
            (Scall None
              (Evar _step (Tfunction
                            (Tcons (tptr (Tstruct _bpf_state noattr))
                              (Tcons tint (Tcons (tptr tulong) Tnil))) tvoid
                            cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Etempvar _len tint) :: (Etempvar _l (tptr tulong)) :: nil))
            (Ssequence
              (Scall None
                (Evar _upd_pc_incr (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       Tnil) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _eval_flag (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _bpf_state noattr))
                                         Tnil) tint cc_default))
                    ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                     nil))
                  (Sset _f (Etempvar _t'2 tint)))
                (Sifthenelse (Ebinop Oeq (Etempvar _f tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Scall None
                      (Evar _bpf_interpreter_aux (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _bpf_state noattr))
                                                     (Tcons tint
                                                       (Tcons tuint
                                                         (Tcons (tptr tulong)
                                                           Tnil)))) tvoid
                                                   cc_default))
                      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
                       (Etempvar _len tint) :: (Etempvar _fuel0 tuint) ::
                       (Etempvar _l (tptr tulong)) :: nil))
                    (Sreturn None))
                  (Sreturn None)))))
          (Ssequence
            (Scall None
              (Evar _upd_flag (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Eunop Oneg (Econst_int (Int.repr 5) tint) tint) :: nil))
            (Sreturn None)))))))
|}.

Definition f_bpf_interpreter := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: (_len, tint) ::
                (_fuel, tuint) :: (_l, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_bpf_ctx, (tptr (Tstruct _memory_region noattr))) ::
               (_f, tint) :: (_t'3, tulong) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_mem_region (Tfunction
                              (Tcons (tptr (Tstruct _bpf_state noattr))
                                (Tcons tuint Tnil))
                              (tptr (Tstruct _memory_region noattr))
                              cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
       (Econst_int (Int.repr 0) tuint) :: nil))
    (Sset _bpf_ctx (Etempvar _t'1 (tptr (Tstruct _memory_region noattr)))))
  (Ssequence
    (Scall None
      (Evar _upd_reg (Tfunction
                       (Tcons (tptr (Tstruct _bpf_state noattr))
                         (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
       (Econst_int (Int.repr 1) tuint) ::
       (Efield
         (Ederef (Etempvar _bpf_ctx (tptr (Tstruct _memory_region noattr)))
           (Tstruct _memory_region noattr)) _start_addr tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _bpf_interpreter_aux (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _bpf_state noattr))
                                       (Tcons tint
                                         (Tcons tuint
                                           (Tcons (tptr tulong) Tnil))))
                                     tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
         (Etempvar _len tint) :: (Etempvar _fuel tuint) ::
         (Etempvar _l (tptr tulong)) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _eval_flag (Tfunction
                               (Tcons (tptr (Tstruct _bpf_state noattr))
                                 Tnil) tint cc_default))
            ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) :: nil))
          (Sset _f (Etempvar _t'2 tint)))
        (Sifthenelse (Ebinop Oeq (Etempvar _f tint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Scall (Some _t'3)
              (Evar _eval_reg (Tfunction
                                (Tcons (tptr (Tstruct _bpf_state noattr))
                                  (Tcons tuint Tnil)) tulong cc_default))
              ((Etempvar _st (tptr (Tstruct _bpf_state noattr))) ::
               (Econst_int (Int.repr 0) tuint) :: nil))
            (Sreturn (Some (Etempvar _t'3 tulong))))
          (Sreturn (Some (Econst_long (Int64.repr 0) tulong))))))))
|}.

Definition composites : list composite_definition :=
(Composite _memory_region Struct
   ((_start_addr, tulong) :: (_block_size, tuint) :: (_block_perm, tuint) ::
    (_block_ptr, tulong) :: nil)
   noattr ::
 Composite _bpf_state Struct
   ((_state_pc, tuint) :: (_bpf_flag, tint) :: (_mem_num, tuint) ::
    (_regsmap, (tarray tulong 11)) ::
    (_mrs, (tptr (Tstruct _memory_region noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_print_bpf_state, Gfun(Internal f_print_bpf_state)) ::
 (_eval_pc, Gfun(Internal f_eval_pc)) ::
 (_upd_pc, Gfun(Internal f_upd_pc)) ::
 (_upd_pc_incr, Gfun(Internal f_upd_pc_incr)) ::
 (_eval_reg, Gfun(Internal f_eval_reg)) ::
 (_upd_reg, Gfun(Internal f_upd_reg)) ::
 (_eval_flag, Gfun(Internal f_eval_flag)) ::
 (_upd_flag, Gfun(Internal f_upd_flag)) ::
 (_eval_mem_num, Gfun(Internal f_eval_mem_num)) ::
 (_eval_mem_regions, Gfun(Internal f_eval_mem_regions)) ::
 (_add_mem_region, Gfun(Internal f_add_mem_region)) ::
 (_add_mem_region_ctx, Gfun(Internal f_add_mem_region_ctx)) ::
 (_load_mem, Gfun(Internal f_load_mem)) ::
 (_store_mem_reg, Gfun(Internal f_store_mem_reg)) ::
 (_store_mem_imm, Gfun(Internal f_store_mem_imm)) ::
 (_list_get, Gfun(Internal f_list_get)) ::
 (_get_mem_region, Gfun(Internal f_get_mem_region)) ::
 (_get_dst, Gfun(Internal f_get_dst)) ::
 (_reg64_to_reg32, Gfun(Internal f_reg64_to_reg32)) ::
 (_get_src, Gfun(Internal f_get_src)) ::
 (_get_offset, Gfun(Internal f_get_offset)) ::
 (_get_immediate, Gfun(Internal f_get_immediate)) ::
 (_eval_immediate, Gfun(Internal f_eval_immediate)) ::
 (_get_opcode_ins, Gfun(Internal f_get_opcode_ins)) ::
 (_get_opcode_alu64, Gfun(Internal f_get_opcode_alu64)) ::
 (_get_opcode_alu32, Gfun(Internal f_get_opcode_alu32)) ::
 (_get_opcode_branch, Gfun(Internal f_get_opcode_branch)) ::
 (_get_opcode_mem_ld_imm, Gfun(Internal f_get_opcode_mem_ld_imm)) ::
 (_get_opcode_mem_ld_reg, Gfun(Internal f_get_opcode_mem_ld_reg)) ::
 (_get_opcode_mem_st_imm, Gfun(Internal f_get_opcode_mem_st_imm)) ::
 (_get_opcode_mem_st_reg, Gfun(Internal f_get_opcode_mem_st_reg)) ::
 (_get_opcode, Gfun(Internal f_get_opcode)) ::
 (_get_addl, Gfun(Internal f_get_addl)) ::
 (_get_subl, Gfun(Internal f_get_subl)) ::
 (_is_well_chunk_bool, Gfun(Internal f_is_well_chunk_bool)) ::
 (_check_mem_aux2, Gfun(Internal f_check_mem_aux2)) ::
 (_check_mem_aux, Gfun(Internal f_check_mem_aux)) ::
 (_check_mem, Gfun(Internal f_check_mem)) ::
 (_comp_and_0x08_byte, Gfun(Internal f_comp_and_0x08_byte)) ::
 (_step_opcode_alu64, Gfun(Internal f_step_opcode_alu64)) ::
 (_step_opcode_alu32, Gfun(Internal f_step_opcode_alu32)) ::
 (_step_opcode_branch, Gfun(Internal f_step_opcode_branch)) ::
 (_step_opcode_mem_ld_imm, Gfun(Internal f_step_opcode_mem_ld_imm)) ::
 (_step_opcode_mem_ld_reg, Gfun(Internal f_step_opcode_mem_ld_reg)) ::
 (_step_opcode_mem_st_imm, Gfun(Internal f_step_opcode_mem_st_imm)) ::
 (_step_opcode_mem_st_reg, Gfun(Internal f_step_opcode_mem_st_reg)) ::
 (_step, Gfun(Internal f_step)) ::
 (_bpf_interpreter_aux, Gfun(Internal f_bpf_interpreter_aux)) ::
 (_bpf_interpreter, Gfun(Internal f_bpf_interpreter)) :: nil).

Definition public_idents : list ident :=
(_bpf_interpreter :: _bpf_interpreter_aux :: _step ::
 _step_opcode_mem_st_reg :: _step_opcode_mem_st_imm ::
 _step_opcode_mem_ld_reg :: _step_opcode_mem_ld_imm :: _step_opcode_branch ::
 _step_opcode_alu32 :: _step_opcode_alu64 :: _check_mem :: _check_mem_aux ::
 _add_mem_region_ctx :: _add_mem_region :: _print_bpf_state :: _printf ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


