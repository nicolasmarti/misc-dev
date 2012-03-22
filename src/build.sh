#!/bin/sh

set -e

CORE=core.otarget
TESTS=tests.otarget
FLAGS=""
OCAMLBUILD=ocamlbuild

ocb()
{
  $OCAMLBUILD $FLAGS $*
}

rule() {
  case $1 in
    clean)  ocb -clean;;
    all)    ocb $CORE; ocb $TESTS;;
    core)  ocb $CORE;;
    tests) ocb $TESTS;;
    gc)    clang -DWITHMAIN -o _build/gc ./lib/llvm/runtime/gc.c;;
    *)      echo "Unknown action $1";;
  esac;
}

if [ $# -eq 0 ]; then
  rule all
else
  while [ $# -gt 0 ]; do
    rule $1;
    shift
  done
fi

