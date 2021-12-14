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
  Definition source_file := "fletcher32_bpf_test.c".
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
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition _addr : ident := $"addr".
Definition _addr0 : ident := $"addr0".
Definition _addr1 : ident := $"addr1".
Definition _addr_dst : ident := $"addr_dst".
Definition _addr_src : ident := $"addr_src".
Definition _begin0 : ident := $"begin0".
Definition _begin1 : ident := $"begin1".
Definition _block_size : ident := $"block_size".
Definition _bpf_add_region_content : ident := $"bpf_add_region_content".
Definition _bpf_add_region_ctx : ident := $"bpf_add_region_ctx".
Definition _bpf_ctx : ident := $"bpf_ctx".
Definition _bpf_flag : ident := $"bpf_flag".
Definition _bpf_fletcher32_bpf_bin : ident := $"bpf_fletcher32_bpf_bin".
Definition _bpf_fletcher32_bpf_bin_len : ident := $"bpf_fletcher32_bpf_bin_len".
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
Definition _clock : ident := $"clock".
Definition _content : ident := $"content".
Definition _data : ident := $"data".
Definition _dst : ident := $"dst".
Definition _dst64 : ident := $"dst64".
Definition _end0 : ident := $"end0".
Definition _end1 : ident := $"end1".
Definition _eval_flag : ident := $"eval_flag".
Definition _eval_pc : ident := $"eval_pc".
Definition _eval_reg : ident := $"eval_reg".
Definition _f : ident := $"f".
Definition _f1 : ident := $"f1".
Definition _f2 : ident := $"f2".
Definition _f32_ctx : ident := $"f32_ctx".
Definition _fletcher32 : ident := $"fletcher32".
Definition _fletcher32_ctx : ident := $"fletcher32_ctx".
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
Definition _init_memory_region0 : ident := $"init_memory_region0".
Definition _init_memory_region1 : ident := $"init_memory_region1".
Definition _init_memory_region2 : ident := $"init_memory_region2".
Definition _init_memory_regions : ident := $"init_memory_regions".
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
Definition _printf : ident := $"printf".
Definition _ptr : ident := $"ptr".
Definition _regsmap : ident := $"regsmap".
Definition _res0 : ident := $"res0".
Definition _result : ident := $"result".
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
Definition _sum1 : ident := $"sum1".
Definition _sum2 : ident := $"sum2".
Definition _sumt : ident := $"sumt".
Definition _tlen : ident := $"tlen".
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
Definition _words : ident := $"words".
Definition _wrap_around_data : ident := $"wrap_around_data".
Definition _x : ident := $"x".
Definition _x1 : ident := $"x1".
Definition _y : ident := $"y".
Definition _y1 : ident := $"y1".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 34);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_bpf_fletcher32_bpf_bin := {|
  gvar_info := (tarray tuchar 520);
  gvar_init := (Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 183) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 183) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 183) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 183) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 183) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 31) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 128) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 137) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 144) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 242) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 211) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 39) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 191) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 255) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 149) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_bpf_fletcher32_bpf_bin_len := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 520) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_fletcher32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr tushort)) :: (_words, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_sum1, tuint) :: (_sum2, tuint) :: (_sumt, tuint) ::
               (_tlen, tuint) :: (_t'4, tuint) :: (_t'3, (tptr tushort)) ::
               (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _sum1 (Econst_int (Int.repr 65535) tint))
  (Ssequence
    (Sset _sum2 (Econst_int (Int.repr 65535) tint))
    (Ssequence
      (Sset _sumt (Econst_int (Int.repr 65535) tint))
      (Ssequence
        (Swhile
          (Etempvar _words tulong)
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Ogt (Etempvar _words tulong)
                             (Econst_int (Int.repr 359) tint) tint)
                (Sset _t'1 (Ecast (Econst_int (Int.repr 359) tint) tulong))
                (Sset _t'1 (Ecast (Etempvar _words tulong) tulong)))
              (Sset _tlen (Ecast (Etempvar _t'1 tulong) tuint)))
            (Ssequence
              (Sset _words
                (Ebinop Osub (Etempvar _words tulong) (Etempvar _tlen tuint)
                  tulong))
              (Ssequence
                (Sloop
                  (Ssequence
                    (Sset _sumt (Etempvar _sum1 tuint))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'3 (Etempvar _data (tptr tushort)))
                            (Sset _data
                              (Ebinop Oadd (Etempvar _t'3 (tptr tushort))
                                (Econst_int (Int.repr 1) tint)
                                (tptr tushort))))
                          (Sset _t'4
                            (Ecast
                              (Ebinop Oadd (Etempvar _sum1 tuint)
                                (Ederef (Etempvar _t'3 (tptr tushort))
                                  tushort) tuint) tuint)))
                        (Sset _sum1 (Etempvar _t'4 tuint)))
                      (Sset _sum2
                        (Ebinop Oadd (Etempvar _sum2 tuint)
                          (Etempvar _t'4 tuint) tuint))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'2
                        (Ecast
                          (Ebinop Osub (Etempvar _tlen tuint)
                            (Econst_int (Int.repr 1) tint) tuint) tuint))
                      (Sset _tlen (Etempvar _t'2 tuint)))
                    (Sifthenelse (Etempvar _t'2 tuint) Sskip Sbreak)))
                (Ssequence
                  (Sset _sum1
                    (Ebinop Oadd
                      (Ebinop Oand (Etempvar _sum1 tuint)
                        (Econst_int (Int.repr 65535) tint) tuint)
                      (Ebinop Oshr (Etempvar _sum1 tuint)
                        (Econst_int (Int.repr 16) tint) tuint) tuint))
                  (Sset _sum2
                    (Ebinop Oadd
                      (Ebinop Oand (Etempvar _sum2 tuint)
                        (Econst_int (Int.repr 65535) tint) tuint)
                      (Ebinop Oshr (Etempvar _sum2 tuint)
                        (Econst_int (Int.repr 16) tint) tuint) tuint)))))))
        (Ssequence
          (Sset _sum1
            (Ebinop Oadd
              (Ebinop Oand (Etempvar _sum1 tuint)
                (Econst_int (Int.repr 65535) tint) tuint)
              (Ebinop Oshr (Etempvar _sum1 tuint)
                (Econst_int (Int.repr 16) tint) tuint) tuint))
          (Ssequence
            (Sset _sum2
              (Ebinop Oadd
                (Ebinop Oand (Etempvar _sum2 tuint)
                  (Econst_int (Int.repr 65535) tint) tuint)
                (Ebinop Oshr (Etempvar _sum2 tuint)
                  (Econst_int (Int.repr 16) tint) tuint) tuint))
            (Sreturn (Some (Ebinop Oor
                             (Ebinop Oshl (Etempvar _sum2 tuint)
                               (Econst_int (Int.repr 16) tint) tuint)
                             (Etempvar _sum1 tuint) tuint)))))))))
|}.

Definition v_wrap_around_data := {|
  gvar_info := (tarray tuchar 361);
  gvar_init := (Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 70) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 89) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 74) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 89) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 88) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 55) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 74) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 74) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 89) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 70) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 66) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 77) :: Init_int8 (Int.repr 113) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 74) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 56) ::
                Init_int8 (Int.repr 74) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 85) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 89) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 89) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 52) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 55) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_f32_ctx := {|
  gvar_info := (Tstruct _fletcher32_ctx noattr);
  gvar_init := (Init_addrof _wrap_around_data (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 180) :: Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_bpf_add_region_ctx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
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
        (Tstruct _memory_region noattr)) _start_addr tulong)
    (Ecast
      (Eaddrof (Evar _f32_ctx (Tstruct _fletcher32_ctx noattr))
        (tptr (Tstruct _fletcher32_ctx noattr))) tulong))
  (Sassign
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
        (Tstruct _memory_region noattr)) _block_size tulong)
    (Esizeof (Tstruct _fletcher32_ctx noattr) tulong)))
|}.

Definition f_bpf_add_region_content := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _bpf_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef
        (Efield
          (Ederef
            (Efield
              (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                (Tstruct _bpf_state noattr)) _mrs
              (tptr (Tstruct _memory_regions noattr)))
            (Tstruct _memory_regions noattr)) _content
          (tptr (Tstruct _memory_region noattr)))
        (Tstruct _memory_region noattr)) _start_addr tulong)
    (Ecast
      (Ecast (Evar _wrap_around_data (tarray tuchar 361)) (tptr tushort))
      tulong))
  (Sassign
    (Efield
      (Ederef
        (Efield
          (Ederef
            (Efield
              (Ederef (Etempvar _st (tptr (Tstruct _bpf_state noattr)))
                (Tstruct _bpf_state noattr)) _mrs
              (tptr (Tstruct _memory_regions noattr)))
            (Tstruct _memory_regions noattr)) _content
          (tptr (Tstruct _memory_region noattr)))
        (Tstruct _memory_region noattr)) _block_size tulong)
    (Esizeof (tarray tuchar 361) tulong)))
|}.

Definition v_init_memory_region0 := {|
  gvar_info := (Tstruct _memory_region noattr);
  gvar_init := (Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_init_memory_region1 := {|
  gvar_info := (Tstruct _memory_region noattr);
  gvar_init := (Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_init_memory_region2 := {|
  gvar_info := (Tstruct _memory_region noattr);
  gvar_init := (Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_init_memory_regions := {|
  gvar_info := (Tstruct _memory_regions noattr);
  gvar_init := (Init_addrof _init_memory_region0 (Ptrofs.repr 0) ::
                Init_addrof _init_memory_region1 (Ptrofs.repr 0) ::
                Init_addrof _init_memory_region2 (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_st, (Tstruct _bpf_state noattr)) :: nil);
  fn_temps := ((_res0, tuint) :: (_begin0, tulong) :: (_end0, tulong) ::
               (_result, tulong) :: (_begin1, tulong) :: (_end1, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_1 (tarray tschar 39)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1) (Evar _clock (Tfunction Tnil tulong cc_default))
          nil)
        (Sset _begin0 (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _fletcher32 (Tfunction
                                (Tcons (tptr tushort) (Tcons tulong Tnil))
                                tuint cc_default))
            ((Ecast (Evar _wrap_around_data (tarray tuchar 361))
               (tptr tushort)) ::
             (Ebinop Odiv (Esizeof (tarray tuchar 361) tulong)
               (Econst_int (Int.repr 2) tint) tulong) :: nil))
          (Sset _res0 (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _clock (Tfunction Tnil tulong cc_default)) nil)
            (Sset _end0 (Etempvar _t'3 tulong)))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_2 (tarray tschar 19)) ::
               (Ebinop Odiv
                 (Ecast
                   (Ebinop Osub (Etempvar _end0 tulong)
                     (Etempvar _begin0 tulong) tulong) tdouble)
                 (Econst_int (Int.repr 1000000) tint) tdouble) :: nil))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar ___stringlit_3 (tarray tschar 34)) ::
                 (Etempvar _res0 tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stringlit_4 (tarray tschar 30)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_5 (tarray tschar 22)) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _st (Tstruct _bpf_state noattr))
                        _state_pc tulong)
                      (Econst_long (Int64.repr 0) tulong))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield (Evar _st (Tstruct _bpf_state noattr))
                              _regsmap (tarray tulong 11))
                            (Econst_int (Int.repr 0) tint) (tptr tulong))
                          tulong) (Econst_long (Int64.repr 0) tulong))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield (Evar _st (Tstruct _bpf_state noattr))
                                _regsmap (tarray tulong 11))
                              (Econst_int (Int.repr 1) tint) (tptr tulong))
                            tulong) (Econst_long (Int64.repr 0) tulong))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Evar _st (Tstruct _bpf_state noattr))
                                  _regsmap (tarray tulong 11))
                                (Econst_int (Int.repr 2) tint) (tptr tulong))
                              tulong) (Econst_long (Int64.repr 0) tulong))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Evar _st (Tstruct _bpf_state noattr))
                                    _regsmap (tarray tulong 11))
                                  (Econst_int (Int.repr 3) tint)
                                  (tptr tulong)) tulong)
                              (Econst_long (Int64.repr 0) tulong))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Evar _st (Tstruct _bpf_state noattr))
                                      _regsmap (tarray tulong 11))
                                    (Econst_int (Int.repr 4) tint)
                                    (tptr tulong)) tulong)
                                (Econst_long (Int64.repr 0) tulong))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Evar _st (Tstruct _bpf_state noattr))
                                        _regsmap (tarray tulong 11))
                                      (Econst_int (Int.repr 5) tint)
                                      (tptr tulong)) tulong)
                                  (Econst_long (Int64.repr 0) tulong))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Evar _st (Tstruct _bpf_state noattr))
                                          _regsmap (tarray tulong 11))
                                        (Econst_int (Int.repr 6) tint)
                                        (tptr tulong)) tulong)
                                    (Econst_long (Int64.repr 0) tulong))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _st (Tstruct _bpf_state noattr))
                                            _regsmap (tarray tulong 11))
                                          (Econst_int (Int.repr 7) tint)
                                          (tptr tulong)) tulong)
                                      (Econst_long (Int64.repr 0) tulong))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _st (Tstruct _bpf_state noattr))
                                              _regsmap (tarray tulong 11))
                                            (Econst_int (Int.repr 8) tint)
                                            (tptr tulong)) tulong)
                                        (Econst_long (Int64.repr 0) tulong))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _st (Tstruct _bpf_state noattr))
                                                _regsmap (tarray tulong 11))
                                              (Econst_int (Int.repr 9) tint)
                                              (tptr tulong)) tulong)
                                          (Econst_long (Int64.repr 0) tulong))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _st (Tstruct _bpf_state noattr))
                                                  _regsmap
                                                  (tarray tulong 11))
                                                (Econst_int (Int.repr 10) tint)
                                                (tptr tulong)) tulong)
                                            (Econst_long (Int64.repr 0) tulong))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Evar _st (Tstruct _bpf_state noattr))
                                                _bpf_flag tint)
                                              (Econst_int (Int.repr 0) tint))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Evar _st (Tstruct _bpf_state noattr))
                                                  _mrs
                                                  (tptr (Tstruct _memory_regions noattr)))
                                                (Eaddrof
                                                  (Evar _init_memory_regions (Tstruct _memory_regions noattr))
                                                  (tptr (Tstruct _memory_regions noattr))))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _bpf_add_region_ctx 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _bpf_state noattr))
                                                      Tnil) tvoid cc_default))
                                                  ((Eaddrof
                                                     (Evar _st (Tstruct _bpf_state noattr))
                                                     (tptr (Tstruct _bpf_state noattr))) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _bpf_add_region_content 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _bpf_state noattr))
                                                        Tnil) tvoid
                                                      cc_default))
                                                    ((Eaddrof
                                                       (Evar _st (Tstruct _bpf_state noattr))
                                                       (tptr (Tstruct _bpf_state noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'4)
                                                        (Evar _clock 
                                                        (Tfunction Tnil
                                                          tulong cc_default))
                                                        nil)
                                                      (Sset _begin1
                                                        (Etempvar _t'4 tulong)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'5)
                                                          (Evar _bpf_interpreter 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _bpf_state noattr))
                                                              (Tcons
                                                                (tptr tulong)
                                                                (Tcons tulong
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil))))
                                                            tulong
                                                            cc_default))
                                                          ((Eaddrof
                                                             (Evar _st (Tstruct _bpf_state noattr))
                                                             (tptr (Tstruct _bpf_state noattr))) ::
                                                           (Ecast
                                                             (Evar _bpf_fletcher32_bpf_bin (tarray tuchar 520))
                                                             (tptr tulong)) ::
                                                           (Esizeof (tarray tuchar 520) tulong) ::
                                                           (Econst_int (Int.repr 10000) tint) ::
                                                           nil))
                                                        (Sset _result
                                                          (Etempvar _t'5 tulong)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'6)
                                                            (Evar _clock 
                                                            (Tfunction Tnil
                                                              tulong
                                                              cc_default))
                                                            nil)
                                                          (Sset _end1
                                                            (Etempvar _t'6 tulong)))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _printf 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr tschar)
                                                                Tnil) tint
                                                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                            ((Evar ___stringlit_2 (tarray tschar 19)) ::
                                                             (Ebinop Odiv
                                                               (Ecast
                                                                 (Ebinop Osub
                                                                   (Etempvar _end1 tulong)
                                                                   (Etempvar _begin1 tulong)
                                                                   tulong)
                                                                 tdouble)
                                                               (Econst_int (Int.repr 1000000) tint)
                                                               tdouble) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _printf 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr tschar)
                                                                  Tnil) tint
                                                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                              ((Evar ___stringlit_6 (tarray tschar 39)) ::
                                                               (Ecast
                                                                 (Etempvar _result tulong)
                                                                 tuint) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _printf 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr tschar)
                                                                    Tnil)
                                                                  tint
                                                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                                                                ((Evar ___stringlit_7 (tarray tschar 20)) ::
                                                                 nil))
                                                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
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
   noattr ::
 Composite _fletcher32_ctx Struct
   ((_data, (tptr tushort)) :: (_words, tuint) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
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
 (_bpf_interpreter,
   Gfun(External (EF_external "bpf_interpreter"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _bpf_state noattr))
       (Tcons (tptr tulong) (Tcons tulong (Tcons tuint Tnil)))) tulong
     cc_default)) ::
 (_bpf_fletcher32_bpf_bin, Gvar v_bpf_fletcher32_bpf_bin) ::
 (_bpf_fletcher32_bpf_bin_len, Gvar v_bpf_fletcher32_bpf_bin_len) ::
 (_clock,
   Gfun(External (EF_external "clock" (mksignature nil AST.Tlong cc_default))
     Tnil tulong cc_default)) ::
 (_fletcher32, Gfun(Internal f_fletcher32)) ::
 (_wrap_around_data, Gvar v_wrap_around_data) ::
 (_f32_ctx, Gvar v_f32_ctx) ::
 (_bpf_add_region_ctx, Gfun(Internal f_bpf_add_region_ctx)) ::
 (_bpf_add_region_content, Gfun(Internal f_bpf_add_region_content)) ::
 (_init_memory_region0, Gvar v_init_memory_region0) ::
 (_init_memory_region1, Gvar v_init_memory_region1) ::
 (_init_memory_region2, Gvar v_init_memory_region2) ::
 (_init_memory_regions, Gvar v_init_memory_regions) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _bpf_add_region_content :: _f32_ctx :: _fletcher32 :: _clock ::
 _bpf_fletcher32_bpf_bin_len :: _bpf_fletcher32_bpf_bin ::
 _bpf_interpreter :: _printf :: ___builtin_debug ::
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


