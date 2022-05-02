#include "bpf/bpfapi/helpers.h"

static const char print_str[] = "Test Call\n";
static const char print_str2[] = "Other Call\n";
static char print_str3[] = "From the memory\n";
char print_str4[] = "And here one\n";
char print_str5[] = "This is global\n";

typedef int (*bpf_call_jmp_t)(unsigned long result, unsigned long context);

int _sum(unsigned long result, unsigned long context)
{
    return result + context;
}

int _recurse(unsigned long result, unsigned long context)
{
    while (result < context) {
        return _recurse(result * 2, context);
    }
    return result;
}

int increment(unsigned long context)
{
    bpf_printf(print_str);
    bpf_printf(print_str2);
    bpf_printf(print_str3);
    bpf_printf(print_str4);
    bpf_printf(print_str5);
    char tst[] = "that";
    __builtin_memcpy(print_str5, tst, 4);
    bpf_printf(print_str5);
    //return jmptable[context](5, context);
    return 0;
}
