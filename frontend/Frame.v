(*
 * Frame.v
 * Wolf Honore
 *
 * Defines the abstract interface for stack frames.
 *)

Require Import String.

Require Import Temp.
Require Import Tree.

Module Type FRAME.

  Definition offset := nat.
  Parameter frame : Set.

  Parameter newFrame : nat -> list (frame * offset).
  Parameter allocInFrame : frame -> offset.

  Inductive frag : Set :=
    | PROC : Temp.label -> Tree.stm -> frame -> frag
    | DATA : Temp.label -> string -> frag.

End FRAME.

Module Frame <: FRAME.

  Definition offset := nat.

  Record frame' : Set := {
    formals : nat;
    offlst : list offset;
    locals : nat;
    maxargs : nat
  }.
  Definition frame := frame'.

  Parameter newFrame : nat -> list (frame * offset).
  Parameter allocInFrame : frame -> offset.

  Inductive frag : Set :=
    | PROC : Temp.label -> Tree.stm -> frame -> frag
    | DATA : Temp.label -> string -> frag.

End Frame.
