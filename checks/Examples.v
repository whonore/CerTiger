Require Import List.
Require Import String.

Require Import Absyn.
Require Import Env.
Require Import Symbol.

Local Open Scope string.

Definition syms := Symbol.make_syms
  ("a" :: "b" :: "c" :: "x" :: "y" :: "z" :: nil).

Definition a := Symbol.symbol' "a" syms.
Definition b := Symbol.symbol' "b" syms.
Definition c := Symbol.symbol' "c" syms.
Definition x := Symbol.symbol' "x" syms.
Definition y := Symbol.symbol' "y" syms.
Definition z := Symbol.symbol' "z" syms.

Definition int := Symbol.symbol' "int" Env.tsyms.
Definition string := Symbol.symbol' "string" Env.tsyms.

Section VALID.

End VALID.

Section INVALID.

End INVALID.