# Formalism and Verified Compilation for PLC Structured Text Language
This repository contains the proof process for the conclusions in the paper.
## 1. Requirements
* 4.03 ≤ [OCaml] ≤ 4.07.1
* [Coq] = 8.9.0
* 20161201 ≤ [Menhir] ≤ 20181113
* [OCamlbuild] ≥ 0.14.0

## 2. Compile Velus and Compcert
Firstly, `cd velus`,
Then Type `./configure [options] <target>` where `<target>` is one of the list given
in the [CompCert manual](http://compcert.inria.fr/man/manual002.html#sec21),
e.g., `./configure x86_64-linux -no-runtime-lib`.
Next,`make proof` to compile coq file in these project.

## 3. Our proof
You can simply run
```c
  make all
```
to see the proof result.