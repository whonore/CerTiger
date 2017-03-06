(*
 * Absyn.v
 * Wolf Honore
 *
 * Defines the abstract syntax of the Tiger language.
 *)

Require Import String.

Require Import Symbol.

Definition symbol := Symbol.t.

Inductive oper : Set :=
  | PlusOp : oper
  | MinusOp : oper
  | TimesOp : oper
  | DivideOp : oper
  | EqOp : oper
  | NeqOp : oper
  | LtOp : oper
  | LeOp : oper
  | GtOp : oper
  | GeOp : oper.

Record tfield := { tf_name : symbol; tf_typ : symbol }.
Inductive ty : Set :=
  | NameTy : symbol -> ty
  | RecordTy : list tfield -> ty
  | ArrayTy : symbol -> ty.

(* In order to satisfy Coq's termination checker later on, explist must be used instead of list exp
   in some places. Same with declist. *)

Record vardec := { vd_name : symbol; vd_escape : bool }.
Record formals := { frm_var : vardec; frm_typ : symbol }.
Record fundec := { fd_name : symbol; fd_params : list formals; fd_result : option symbol }.
Record tydec := { td_name : symbol; td_ty : ty }.
Inductive var : Set :=
  | SimpleVar : symbol -> var
  | FieldVar : var -> symbol -> var
  | SubscriptVar : var -> exp -> var
with exp : Set :=
  | VarExp : var -> exp
  | NilExp : exp
  | IntExp : nat -> exp
  | StringExp : string -> exp
  | AppExp : symbol -> explist -> exp
  | OpExp : exp -> oper -> exp -> exp
  | RecordExp : explist -> list symbol -> symbol -> exp (* assume 1st and 2nd args have same length *)
  | SeqExp : explist -> exp
  | AssignExp : var -> exp -> exp
  | IfExp : exp -> exp -> option exp -> exp
  | WhileExp : exp -> exp -> exp
  | ForExp : vardec -> exp -> exp -> exp -> exp
  | BreakExp : exp
  | LetExp : declist -> exp -> exp
  | ArrayExp : symbol -> exp -> exp -> exp
with explist : Set :=
  | ENil : explist
  | ECons : exp -> explist -> explist
with dec : Set :=
  | FunctionDec : list fundec -> explist -> dec (* assume 1st and 2nd args have same length *)
  | VarDec : vardec -> option symbol -> exp -> dec
  | TypeDec : list tydec -> dec
with declist : Set :=
  | DNil : declist
  | DCons : dec -> declist -> declist.
