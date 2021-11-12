CC=gcc
OFLAGS=-Os

test: fletcher32_bpf_test.c interpreter.c
	$(CC) -o $@ $(OFLAGS) $^
