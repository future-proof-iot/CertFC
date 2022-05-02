# BPF example application for RIOT

This application provides a very minimal demonstrator for the rBPF virtual
machine implementation. The example includes a tiny (3 instruction) BPF
application that increments and returns the context value. This application is
executed in the rBPF VM when running the example. The example provides a
integer value to the bpf snippet and prints the returned value after running the
bpf code.

## Example use

First compile the rBPF application, then compile the RIOT example here.

### Compiling the rBPF program

The example rBPF snippet called `increment.c` in the bpf directory can be
compiled with make. It requires LLVM for compiling:

```
make -C examples/bpf_minimal/bpf
```

The resulting `increment.bin` contains the raw bpf code.

### Running the example

The bpf example itself is also compiled with make:

```
make -C examples/bpf_minimal
```

It will compile in the binary bpf increment application.

Run the example with:

```
make -C examples/bpf_minimal term
```

The output it shows should be like:

```
RIOT native interrupts/signals initialized.
LED_RED_OFF
LED_GREEN_ON
RIOT native board initialized.
RIOT native hardware initialization complete.

main(): This is RIOT! (Version: 2020.10)
All up, running the rBPF VM now
Return code: 0
Result: 5
```
