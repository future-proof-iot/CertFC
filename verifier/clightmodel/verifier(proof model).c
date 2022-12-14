#include "verifier.h"
#include <stdint.h> /* for uintptr_t */

static __attribute__((always_inline)) inline int eval_ins_len(struct verifier_state* st)
{
  return (*st).ins_len;
}

static __attribute__((always_inline)) inline unsigned long long eval_ins(struct verifier_state* st, unsigned int idx)
{
  return *((*st).ins + idx);
}

/*******************below code are automatically generated by dx (after repatch) ***************************/

_Bool is_well_dst(unsigned long long i)
{
  return (unsigned int) ((i & 4095LLU) >> 8LLU) <= 10U;
}

_Bool is_well_src(unsigned long long i)
{
  return (unsigned int) ((i & 65535LLU) >> 12LLU) <= 10U;
}

_Bool is_well_jump(unsigned int pc, unsigned int len, int ofs)
{
  return pc + ofs <= len - 2U;
}

_Bool is_not_div_by_zero(unsigned long long i)
{
  return (int) (i >> 32LLU) != 0U;
}

_Bool is_shift_range(unsigned long long i, unsigned int upper)
{
  return 0U <= (int) (i >> 32LLU) & (int) (i >> 32LLU) <= upper;
}

unsigned int get_opcode(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

int get_offset(unsigned long long i)
{
  return (int) (short) (i << 32LLU >> 48LLU);
}

static __attribute__((always_inline)) inline unsigned char nat2opcode(unsigned int n)
{
  return n;
}

static __attribute__((always_inline)) inline _Bool bpf_verifier_aux(struct verifier_state * st, unsigned int pc)
{
  unsigned int len;
  unsigned long long ins64;
  unsigned int op;
  unsigned int n;
  unsigned char opc;
  _Bool b;
  _Bool b0;
  int ofs;
  len = eval_ins_len(st);
  ins64 = eval_ins(st, pc - 1U - len);
  op = get_opcode(ins64);
  if (pc == 0U) {
    return op == 149;
  } else {
    n = pc - 1U;
    opc = nat2opcode(op);
    switch (opc) {
      case 7:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 23:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 39:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 55:
        b = is_not_div_by_zero(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 71:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 87:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 103:
        b = is_shift_range(ins64, 64U);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 119:
        b = is_shift_range(ins64, 64U);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 135:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 151:
        b = is_not_div_by_zero(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 167:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 183:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 199:
        b = is_shift_range(ins64, 64U);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 15:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 31:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 47:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 63:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 79:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 95:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 111:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 127:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 159:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 175:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 191:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 207:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 4:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 20:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 36:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 52:
        b = is_not_div_by_zero(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 68:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 84:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 100:
        b = is_shift_range(ins64, 32U);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 116:
        b = is_shift_range(ins64, 32U);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 132:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 148:
        b = is_not_div_by_zero(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 164:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 180:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 196:
        b = is_shift_range(ins64, 32U);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 12:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 28:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 44:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 60:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 76:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 92:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 108:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 124:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 156:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 172:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 188:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 204:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 24:
        b = is_well_jump(pc, len, 2);
        if (b) {
          return bpf_verifier_aux(st, n - 1);
        } else {
          return 0;
        }
      case 97:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 105:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 113:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 121:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 98:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 106:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 114:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 122:
        b = is_well_dst(ins64);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 99:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 107:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 115:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 123:
        b = is_well_dst(ins64);
        if (b) {
          b0 = is_well_src(ins64);
          if (b0) {
            return bpf_verifier_aux(st, n);
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      case 5:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 21:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 37:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 53:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 165:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 181:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 69:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 85:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 101:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 117:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 197:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 213:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 29:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 45:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 61:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 173:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 189:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 77:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 93:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 109:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 125:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 205:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 221:
        ofs = get_offset(ins64);
        b = is_well_jump(pc, len, ofs);
        if (b) {
          return bpf_verifier_aux(st, n);
        } else {
          return 0;
        }
      case 133:
        return bpf_verifier_aux(st, n);
      case 149:
        return bpf_verifier_aux(st, n);
      default:
        return 0;
      
    }
  }
}

_Bool bpf_verifier(struct verifier_state * st)
{
  unsigned int len;
  len = eval_ins_len(st);
  if (1U <= len) {
    if (len <= 4294967295U / 8) {
      return bpf_verifier_aux(st, len - 1);
    } else {
      return 0;
    }
  } else {
    return 0;
  }
}

