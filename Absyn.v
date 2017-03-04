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

Inductive ty : Set :=
  | NameTy : symbol -> ty
  | RecordTy : list tfield -> ty
  | ArrayTy : symbol -> ty
with tfield : Set :=
  | mk_tfield : symbol -> symbol -> tfield.

Definition tf_name (tf : tfield) := let (name, _) := tf in name.
Definition tf_typ (tf : tfield) := let (_, typ) := tf in typ.

(* In order to satisfy Coq's termination checker later on, explist must be used instead of list exp
   in some places. Same with declist *)

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
  | DCons : dec -> declist -> declist
with vardec : Set :=
  | mk_vardec : symbol -> bool -> vardec
with formals : Set :=
  | mk_formals : vardec -> symbol -> formals
with fundec : Set :=
  | mk_fundec : symbol -> list formals -> option symbol -> fundec
with tydec : Set :=
  | mk_tydec : symbol -> ty -> tydec.

Definition vd_name (vd : vardec) := let (name, _) := vd in name.
Definition vd_escape (vd : vardec) := let (_, escape) := vd in escape.

Definition form_var (form : formals) := let (var, _) := form in var.
Definition form_typ (form : formals) := let (_, typ) := form in typ.

Definition fd_name (fd : fundec) := let (name, _, _) := fd in name.
Definition fd_params (fd : fundec) := let (_, params, _) := fd in params.
Definition fd_result (fd : fundec) := let (_, _, result) := fd in result.

Definition td_name (td : tydec) := let (name, _) := td in name.
Definition td_ty (td : tydec) := let (_, ty) := td in ty.
