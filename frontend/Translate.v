(*
 * Translate.v
 * Wolf Honore
 *
 * Defines an interface for handling nested scope through
 * static links.
 *)

Require Import Frame.
Require Import Temp.
Require Import Tree.
Require Import Unique.

Module Type TRANSLATE.

  Parameter level : Set.
  Parameter access : Set.
  Parameter frag : Set.
  Parameter gexp : Set.

  Parameter outermost : level.
  Parameter newLevel : forall A, level -> list A -> (level * list (A * access)).

  Parameter allocInFrame : level -> access.
  Parameter allocInRegister : access.

  Parameter getResult : list frag.

End TRANSLATE.

Module Translate' (U : UNIQUE) <: TRANSLATE.

  Inductive level' : Set :=
    | TOP : level'
    | LEVEL : Frame.frame -> nat -> level' -> U.t -> level'.
  Definition level := level'.

  Definition access := (level * nat)%type.

  Definition frag := Frame.frag.

  Inductive gexp' : Set :=
    | Ex : Tree.exp -> gexp'
    | Nx : Tree.stm -> gexp'
    | Cx : Temp.label -> Temp.label -> Tree.stm -> gexp'.
  Definition gexp := gexp'.

  Definition outermost := TOP.
  Definition newLevel {A} (par : level) (forms : list A) :=
    (par, @nil (A * access)).

  Definition allocInFrame (lvl : level) := (lvl, 0).
  Definition allocInRegister := (outermost, 0).

  Definition getResult := @nil frag.

End Translate'.

Module Translate := Translate' NatUnique.
