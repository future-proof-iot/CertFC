From compcert.cfrontend Require Csyntax Ctypes.
From compcert.lib Require Integers.

Definition C_U8  := Ctypes.Tint Ctypes.I8  Ctypes.Unsigned Ctypes.noattr.

Definition C_U16 := Ctypes.Tint Ctypes.I16 Ctypes.Unsigned Ctypes.noattr.

Definition C_U32 := Ctypes.Tint Ctypes.I32 Ctypes.Unsigned Ctypes.noattr.

Definition C_U64 := Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition C_S8  := Ctypes.Tint Ctypes.I8  Ctypes.Signed Ctypes.noattr.

Definition C_S16 := Ctypes.Tint Ctypes.I16 Ctypes.Signed Ctypes.noattr.

Definition C_S32 := Ctypes.Tint Ctypes.I32 Ctypes.Signed Ctypes.noattr.

Definition C_S64 := Ctypes.Tlong Ctypes.Signed Ctypes.noattr.

Definition C_U8_pointer  := Ctypes.Tpointer C_U8  Ctypes.noattr.

Definition C_U16_pointer := Ctypes.Tpointer C_U16 Ctypes.noattr.

Definition C_U32_pointer := Ctypes.Tpointer C_U32 Ctypes.noattr.

Definition C_U64_pointer := Ctypes.Tpointer C_U64 Ctypes.noattr.

Definition C_S8_pointer  := Ctypes.Tpointer C_S8  Ctypes.noattr.

Definition C_S16_pointer := Ctypes.Tpointer C_S16 Ctypes.noattr.

Definition C_S32_pointer := Ctypes.Tpointer C_S32 Ctypes.noattr.

Definition C_S64_pointer := Ctypes.Tpointer C_S64 Ctypes.noattr.

(******************** C_U64 operations *******************)

Definition C_U64_neg (x: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Eunop Cop.Oneg x C_U64.

Definition C_U64_add (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oadd x y C_U64.

Definition C_U64_sub (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Osub x y C_U64.

Definition C_U64_mul (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Omul x y C_U64.

Definition C_U64_div (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Odiv x y C_U64.

Definition C_U64_mod (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Omod x y C_U64.

Definition C_U64_and (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oand x y C_U64.

Definition C_U64_or (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oor x y C_U64.

Definition C_U64_shl (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oshl x y C_U64.

Definition C_U64_shr (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oshr x y C_U64.

Definition C_U64_eq (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oeq x y C_U64.

Definition C_U64_ne (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.One x y C_U64.

Definition C_U64_lt (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Olt x y C_U64.

Definition C_U64_gt (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Ogt x y C_U64.

Definition C_U64_le (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Ole x y C_U64.

Definition C_U64_ge (x y: Csyntax.expr) : Csyntax.expr :=
  Csyntax.Ebinop Cop.Oge x y C_U64.