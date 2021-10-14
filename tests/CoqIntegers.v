From compcert.cfrontend Require Csyntax Ctypes.
From compcert.lib Require Integers.

Definition C_U8  := Ctypes.Tint Ctypes.I8  Ctypes.Unsigned Ctypes.noattr.

Definition C_U16 := Ctypes.Tint Ctypes.I16 Ctypes.Unsigned Ctypes.noattr.

Definition C_U32 := Ctypes.Tint Ctypes.I32 Ctypes.Unsigned Ctypes.noattr.

Definition C_U64 := Ctypes.Tlong Ctypes.Unsigned Ctypes.noattr.

Definition C_U8_pointer  := Ctypes.Tpointer C_U8  Ctypes.noattr.

Definition C_U16_pointer := Ctypes.Tpointer C_U16 Ctypes.noattr.

Definition C_U32_pointer := Ctypes.Tpointer C_U32 Ctypes.noattr.

Definition C_U64_pointer := Ctypes.Tpointer C_U64 Ctypes.noattr.