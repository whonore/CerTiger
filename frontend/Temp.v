(*
 * Temp.v
 * Wolf Honore
 *
 * Defines the type of temporary registers and label.
 *)

Require Import String.

Require Import Symbol.
Require Import Unique.

Module Type TEMP (U : UNIQUE).

  Definition temp := U.t.
  Definition eq := U.eq.

  Definition newTemp := U.new.

  Definition label := Symbol.t.
  Definition newLabel := SymUnique.new.
  Parameter namedLabel : nat -> label.

End TEMP.

Module Temp <: TEMP NatUnique.

  Definition temp := NatUnique.t.
  Definition eq := NatUnique.eq.

  Definition newTemp := NatUnique.new.

  Definition label := Symbol.t.
  Definition newLabel := SymUnique.new.
  Definition namedLabel n := Symbol.symbol' n Symbol.sym_empty.

End Temp.
