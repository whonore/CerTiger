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

Inductive var : Set :=
  | SimpleVar : symbol -> var
  | FieldVar : var -> symbol -> var
  | SubscriptVar : var -> exp -> var
with exp : Set :=
  | VarExp : var -> exp
  | NilExp : exp
  | IntExp : nat -> exp
  | StringExp : string -> exp
  | AppExp : symbol -> list exp -> exp
  | OpExp : exp -> oper -> exp -> exp
  | RecordExp : list efield -> symbol -> exp
  | SeqExp : list exp -> exp
  | AssignExp : var -> exp -> exp
  | IfExp : exp -> exp -> option exp -> exp
  | WhileExp : exp -> exp -> exp
  | ForExp : vardec -> exp -> exp -> exp -> exp
  | BreakExp : exp
  | LetExp : list dec -> exp -> exp
  | ArrayExp : symbol -> exp -> exp -> exp
with dec : Set :=
  | FunctionDec : list fundec -> dec
  | VarDec : vardec -> option symbol -> exp -> dec
  | TypeDec : list tydec -> dec
with efield : Set :=
  | mk_efield : symbol -> exp -> efield
with vardec : Set :=
  | mk_vardec : symbol -> bool -> vardec
with formals : Set :=
  | mk_formals : vardec -> symbol -> formals
with fundec : Set :=
  | mk_fundec : symbol -> list formals -> option symbol -> exp -> fundec
with tydec : Set :=
  | mk_tydec : symbol -> ty -> tydec.

Definition vd_name (vd : vardec) := let (name, _) := vd in name.
Definition vd_escape (vd : vardec) := let (_, escape) := vd in escape.

Definition form_var (form : formals) := let (var, _) := form in var.
Definition form_typ (form : formals) := let (_, typ) := form in typ.

Definition fd_name (fd : fundec) := let (name, _, _, _) := fd in name.
Definition fd_params (fd : fundec) := let (_, params, _, _) := fd in params.
Definition fd_result (fd : fundec) := let (_, _, result, _) := fd in result.
Definition fd_body (fd : fundec) := let (_, _, _, body) := fd in body.

Definition td_name (td : tydec) := let (name, _) := td in name.
Definition td_ty (td : tydec) := let (_, ty) := td in ty.
