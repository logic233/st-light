# Formalism and Verified Compilation for PLC Structured Text Language

by Yifan Wu, Yanhong Huang, Jianqi Shi

## 1. Requirements
K-framework version 5.1.11 

Java 8.*

## 2. Compile Velus and Compcert
Firstly, `cd velus`,Then Type `./configure [options] <target>` where `<target>` is one of the list given
in the [CompCert manual](http://compcert.inria.fr/man/manual002.html#sec21),
e.g., `x86_64-linux`.
Next,`make proof` to compile coq file in these project.

## 2. Our proof
You can simply run
```c
  make all
```
to see the proof result.

## 4. Detailed information
Some content is still being organized.