Require Import Absyn.
Require Import Examples.
Require Import Semant.
Require Import Types.

Section TypeDec_CHECKS.

  Definition td_check (td : dec) :=
    exists ce us, wt_dec base_cenv Types.uinit td ce us.

End TypeDec_CHECKS.
