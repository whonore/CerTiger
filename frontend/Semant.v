(*
 * Semant.v
 * Wolf Honore
 *
 * Defines functions to translate Tiger to IR.
 *)

Require Import Arith.
Require Import List.

Require Import Absyn.
Require Import DecEqFacts.
Require Import Env.
Require Import Errors.
Require Import Symbol.
Require Import Translate.
Require Import Tree.
Require Import Types.

Definition tmp := Translate.Ex (Tree.CONST 0).

Definition tenv := @Symbol.table Types.ty.
Definition venv := @Symbol.table Env.enventry.

Record composite_env := {
  te : tenv;
  ve : venv;
  ll : nat (* loop-level *)
}.

Definition base_cenv : composite_env :=
  {| ve := Env.base_venv; te := Env.base_tenv; ll := 0 |}.

Definition update_te (ce : composite_env) (te : tenv) :=
  {| te := te; ve := ve ce; ll := ll ce |}.

Definition update_ve (ce : composite_env) (ve : venv) :=
  {| te := te ce; ve := ve; ll := ll ce |}.

Definition incr_ll (ce : composite_env) :=
  {| te := te ce; ve := ve ce; ll := S (ll ce) |}.

Definition reset_ll (ce : composite_env) :=
  {| te := te ce; ve := ve ce; ll := 0 |}.

Section TRANSLATE.

  Fixpoint transExp (ce : composite_env) (exp : Absyn.exp) : Translate.gexp :=
    match exp with
    | VarExp v => transVar ce v
    | NilExp => tmp
    | IntExp _ => tmp
    | StringExp _ => tmp
    | AppExp f args => tmp
    | OpExp l f r => tmp
    | RecordExp fvals fnames rty => tmp
    | SeqExp es => tmp
    | AssignExp l r => tmp
    | IfExp p t (Some e) => tmp
    | IfExp p t None => tmp
    | WhileExp g b => tmp
    | ForExp v lo hi b => tmp
    | BreakExp => tmp
    | LetExp decs b => tmp
    | ArrayExp aty sz init => tmp
    end
  with transExplist (ce : composite_env) (exps : Absyn.explist) : list Translate.gexp :=
    match exps with
    | ENil => nil
    | ECons e es => nil
    end
  with transVar (ce : composite_env) (var : Absyn.var) : Translate.gexp :=
    match var with
    | SimpleVar name => tmp
    | FieldVar v field => tmp
    | SubscriptVar v idx => tmp
    end
  with transDec (ce : composite_env) (dec : Absyn.dec) : composite_env :=
    match dec with
    | FunctionDec decs bodies => ce
    | VarDec v None val => ce
    | VarDec v (Some tyname) val => ce
    | TypeDec decs => ce
    end
  with transDeclist (ce : composite_env) (decs : declist) : composite_env :=
    match decs with
    | DNil => ce
    | DCons d ds => ce
    end.

  Definition transProg (tree : Absyn.exp) := transExp base_cenv tree.

End TRANSLATE.
