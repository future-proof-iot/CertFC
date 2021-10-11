# Overview

This folder is used to test how dx works, each subfolder may include two subsubfolders (see `test_template`):
- (optional) src/Type/ : some self-defined libraries
- tests/Tests.v: the testing example

So, just copy all `* .v` file to corresponding folders of dx.

BTW, just commit the L157 line of makefile of dx for testing.

# testInt64
- src/Type/MyInt64.v: define the mapping relation (from Coq to C): 
    - `Integers.int64 -> uint64_t`; 
    - `Integer.Int64.zero/one -> 0/1`;
    - `Integer.Int64.add/sub -> +/-`.
- tests/Tests.v:
The Coq code:
```
Definition testincr (a: Integers.int64): M Integers.int64 :=
  returnM (Integers.Int64.add a Integers.Int64.one).
```
The generated C:

```C
extern unsigned long long testincr(unsigned long long);

unsigned long long testincr(unsigned long long a)
{
  return a + 1LLU;
}
```
# testListGet
- src/Type/MyInt64.v & MyList.v: `int64_t -> uint64_t` and `MyList -> Cpointer`
- tests/Tests.v: testing the `get` function!

The Coq code:
```
Definition testget (fuel: nat) (init idx: state) (l: MyList.MyListType): M state :=
  returnM (MyList.MyListGet l idx).
```

The generated C code:
```C
extern unsigned long long testget(unsigned int, unsigned long long, unsigned long long, unsigned long long *);

unsigned long long testget(unsigned int fuel, unsigned long long init, unsigned long long idx, unsigned long long *l)
{
  return *(l + idx);
}
```

# testList
- tests/Tests.v:
The Coq code:
```
Fixpoint interpreter1 (fuel: nat) (init idx: state) (l: MyListType){struct fuel}: M unit :=
  match fuel with
  | O => emptyUnitM
  | S fuel' =>
    do i <- returnM (MyListGet l idx);
    do s <- sum init i;
      interpreter1 fuel' s (Integers.Int64.sub idx Integers.Int64.one) l
  end.
```
The expected C:
```
uint64_t interpreter1 (unsigned int fuel, uint64_t init, uint64_t idx, uint64_t *l){
  unsigned int b_i;
  uint64_t b_j, b_k, b_r;
  if (fuel == 0U) {
    emptyUnitM();
    return;
  }
  else {
    b_i = fuel - 1U;
    b_j = get(l, idx);
    b_k = sum(init, b_j);
    b_r = interpreter1 (b_i, b_k, (idx-1) l);
    return b_r;
  }
}
```

