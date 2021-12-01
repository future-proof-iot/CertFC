# rbpf-dx

A testing project for using dx to transform exam_rbpf in Coq to C

# rbpf-dx Overview

The toy project is to use [dx](https://gitlab.univ-lille.fr/samuel.hym/dx) to generate C code from our toy rBPF interpreter (in Coq).

The toy Coq interpreter consists of:
- lib/\*.v: some libraries we may use.
- tests/
    - Asm.v: the syntax of rBPF instruciton set, this toy includes NEG, ADD and EXIT.
    - Monad.v: our monad information
    - Sem.v: the semantics part.
    - Interp.v: the rBPF interpreter in Coq.
    - ListOp.v, Int16.v: some necessary libraries.
    - TestMain.v, ExtraMain.v: the existing files of dx
    - Tests.v: we will reuse this file and add our interpreter information!

Before installing this repo, making sure that you have installed necessary libs of dx (see below: the description of dx)!!!

_NB: we modify the makefile of the source project_, to run this repo:
```shell
$ git clone https://gitlab.univ-lille.fr/samuel.hym/dx
$ cd dx
$ ./configure ...
$ ./configure --install-compcert-printer
$ make
$ make test
```
```shell
$ git clone https://gitlab.inria.fr/syuan/rbpf-dx.git
$ cd rbpf-dx
$ make compile
$ make clight
$ make proof
```
Remember:
1. we must config the compcert-printer function!!!
2. be careful to use positive as variables' id, because dx/compcert also uses postive numbers to represent variables: there will be a conflict if your positive number is too small and it overlaps with existing variables.
3. we must run `make test` once, because it will compile some files from `extr` (it should be fixed soon).

#   dx

dx is a tool to _derive_ (hence the name) C code from a monadic
Gallina code that looks very much like the final C code. To be more
precise, the end result is the abstract syntax tree for C as defined
by the module [`Csyntax`] of the [CompCert compiler].

[`Csyntax`]: https://compcert.org/doc/html/compcert.cfrontend.Csyntax.html
[CompCert compiler]: https://compcert.org/

Note that this is a _work-in-progress_!
1. It will probably fail on your example, but you are most welcome to
send bug reports.
2. When you use positive to represent a id of some variables, you must be careful: if the positive number is too small, dx will generate a type conflict!!! because dx also uses positive numbers to represent variabls!!!

##  Overview

This derivation is performed in two steps, with an _Intermediate
Representation_. That representation is defined in [`IR.v`]. In
particular a Gallina `Definition` that is to be converted will be
represented as an `IRSymbol` at that stage.

[`IR.v`]: src/IR.v

Gallina does not have any introspection mechanism built-in. It is
obviously possible to write an `IRSymbol` by hand but we provide an
[elpi] program using the [Coq-elpi] plugin to generate automatically
the corresponding `IRSymbol`.
The module [`CoqIR.v`] provides to that end a
`GenerateIntermediateRepresentation` Coq command.

[elpi]: https://github.com/LPCIC/elpi
[coq-elpi]: https://github.com/LPCIC/coq-elpi
[`CoqIR.v`]: src/CoqIR.v

The second step is to go from that intermediate representation to a
`dxModule` (defined in [`DXModule`]) that packs together a CompCert C
module along with names, to associate strings to the numeric
identifiers used in the CompCert C AST.
[`IRtoC.v`] provides various functions, `makeDXModule` and its
specialisations, to turn a list of `IRSymbol`s into a `dxModule`.

[`DXModule`]: src/DXModule.v
[`IRtoC.v`]: src/IRtoC.v

Once you have some `dxModule`s, you would probably want to finish the
trip to actual runnable code. One way to proceed is to use the C
pretty-printer from CompCert. To make this easier, the [`DumpAsC.v`]
module defines, as an axiom, a `print_dx_modules` function.
This function is a simple way to define a `main` to be extracted into
an OCaml (using the standard Coq extraction) module, ready to be
linked with a few modules provided by dx and, above all, with modules,
such as `PrintCsyntax` from the CompCert compiler.
You obtain then an OCaml program that generates the C source files for
all your `dxModule`s.

In order to use that last step, you must have all the compiled sources
for CompCert, not only an installation of CompCert.

[`DumpAsC.v`]: src/DumpAsC.v


### Overview by example

To understand better how all these parts work together, have a look at
the `tests/` directory:

-   `Tests.v` defines a few example functions and then uses the
    `GenerateIntermediateRepresentation` command to define `SymbolIRs`
    and `makeDXModuleWithoutMain` to generate the corresponding
    dxModule,
-   `TestMain.v` only defines a `main` that will call
    `print_dx_modules` on the dxModule defined in `Tests.v`; what is
    particularly important to note there is the fact that we use an
    `ltac:` trick to ensure that the dxModule is fully evaluated by
    Coq: we don’t want to extract the whole machinery that converts
    from the intermediate representation into C,
-   `ExtrMain.v` is only to trigger the extraction from `TestMain.v`
    to a `TestMain.ml` module.

The `Makefile` provides a `tests/main-after-install` target that
generates a binary after you have installed, using `make install`.
That will show how to compile your own extracted code.


##  Installation

### Dependencies

To install dx, you will require:

-   `make` (and standard tools: `sed`, `awk`, `cat`);
    dx is tested only with GNU Make (which is required by CompCert),
    preferably at least version 4.3 for its “grouped targets” feature
    (required to use parallelism reliably),
-   Coq
-   [coq-elpi]
-   CompCert (version 3.9)
-   OCaml compiler; currently the `Makefile` assumes you use the
    native compiler, no recipe is written for bytecode compilation.

[CompCert]: https://compcert.org/

dx is currently developed with the following versions of these
dependencies:

```
$ opam list ocaml coq coq-elpi coq-compcert
# Name       # Installed # Synopsis
coq          8.13.2      Formal proof management system
coq-compcert 3.9         The CompCert C compiler (64 bit)
coq-elpi     1.11.0      Elpi extension language for Coq
ocaml        4.11.1      The OCaml compiler (virtual package)
```

Note that if you want to be able to generate C source code, you will
need not only an _installation_ of CompCert but also its _compiled
source code_, since it will use CompCert’s module to pretty-print a C
AST.

You can use [opam] to install these dependencies: it provides the `-b`
option to keep the build directory. If you do not mind using disk
space, you can then install dependencies with:

[opam]: https://coq.inria.fr/opam-using.html

```
# if opam is not yet configured to get Coq packages
opam repository add coq-released https://coq.inria.fr/opam/released

# and then
opam install -b coq coq-elpi coq-compcert
```

If you’d rather spare some disk, you can set `-b` only for CompCert:

```
opam install coq coq-elpi
opam install --deps-only coq-compcert
opam install -b coq-compcert
```

### Building dx

Use the standard path:

```
$ ./configure ...
$ make
```

Use `./configure --help` to list the available options. In particular
you need to specify explicitly an option if you want to be able to
generate C source code.

Or you can use [opam] if you’ve installed the dependencies with opam
already.
In the directory containing sources, simply run:

```
$ opam pin .
```


##  How to use dx on your project

Here is a short step-by-step mini guide on how to use dx on your
project.

### Configure type mappings

The first step to use dx on your code is to configure how your Coq
inductive types should be mapped to C types by defining a
`CompilableType` record (see [`IR.v`]).
Such a record packs together a Coq type and a C type.
This is necessary in order to know which C types to use in function
signatures and variable declarations.

If you want to be able to convert a `match`, you should also define a
`MatchableType` record (again see [`IR.v`]).

[`Type.Bool`] gives simple examples of `CompilableType` and
`MatchableType`.
[`Type.Nat`] gives a more elaborate example, valid only for natural
numbers less than 2³².

[`Type.Bool`]: src/Type/Bool.v
[`Type.Nat`]: src/Type/Nat.v


### Configure primitives

We call _primitives_ the Coq functions that have a specific
translation into C. This is specifically suited for C operators, so
that the boolean equality in Coq can be translated into the actual
`==` when applicable (for types where `==` is indeed the proper
equality test, obviously). Primitives are also designed to cover use
cases such as constants.

[`Type.Bool`] thus defines primitives for `false`, `true`, `negb`,
etc.


### Generate intermediate representation

[`CoqIR`] defines the `GenerateIntermediateRepresentation` command to
automatically convert Coq functions to their intermediate
representation.

`GenerateIntermediateRepresentation` takes the following arguments, in
that order:

-   a name, that will be defined to the result of the generation,
    namely a list of `IRSymbol`s,
-   the name of your monad,
-   the name of your `bind`,
-   the name of your `return`,
-   a sequence (0, 1 or more) of names of:
    -   modules, which are recursively opened and dealt with as the
        sequence of all their content,
    -   `CompilableType`, `MatchableType`, `Primitive` or
        `DerivableSymbol` records,
    -   Coq `Definition`s, for constants or functions that will
        derived as `extern` in C (so that only their _signature_ will
        in fact be derived),
-   the special separator “`__`” (think of the standard command-line
    separator `--`),
-   a sequence (0, 1 or more) of names of:
    -   modules, which are recursively opened and dealt with as the
        sequence of all their content,
    -   `CompilableType`, `MatchableType`, `Primitive` or
        `DerivableSymbol` records,
    -   Coq `Definition`s, for constants or functions that will
        be fully derived (body included) in C.

See [`Tests.v`] for an example of this.

[`CoqIR`]: src/CoqIR.v
[`Tests.v`]: tests/Tests.v


### Derive `dxModule`s (and code) from the intermediate representation

Once you have a list of `IRSymbol`s generated by
`GenerateIntermediateRepresentation` (or written by hand, if you
really want), [`IRtoC`] provides the `makeDXModuleWithMain` and
`makeDXModuleWithoutMain` functions to get a `dxModule` that packs
together the content of a C source file.

As stated in the overview above, if you have built and installed the
C printer, you can:

-   extract a simple OCaml module containing the fully evaluated
    dxModules you want to print as C source code,
-   compile it,
-   and link it with a few helpers from dx and the `printCsyntax`
    CompCert module

to get an executable that will generate the C files corresponding to
those dxModules.

Have a look at [`tests`], in particular at [`TestMain`] that contain
the main module of the C source code generator we will extract, and at
[`ExtrMain`] that actually extracts `TestMain` to OCaml.

`make test` will show you how the C printer is actually compiled and
run. It is also interesting to see how `make tests/main-after-install`
compiles the executable `tests/main-after-install` (which is
equivalent to `tests/main`) using the _installed_ version of dx, so
you’ll probably be using a very similar compilation line on your
project.

[`IRtoC`]: src/IRtoC.v
[`tests`]: tests/
[`TestMain`]: tests/TestMain.v
[`ExtrMain`]: tests/ExtrMain.v
