CC=gcc
OFLAGS=-Os
CLIGHTGEN=clightgen


test: fletcher32_bpf_test.c interpreter.c
	$(CC) -o $@ $(OFLAGS) $^
	
coq: interpreter.c
	$(CLIGHTGEN) $^
