Require Import List.
Require Import String.

Require Import Symbol.
Require Import Types.

Module Type ENV.

  Parameter access : Type.
  Parameter ty : Set.

  Inductive enventry : Set :=
    | VarEntry : ty -> enventry
    | FunEntry : list ty -> ty -> enventry.

  Parameter base_tenv : @Symbol.table ty.
  Parameter base_venv : @Symbol.table enventry.

End ENV.

Module Env <: ENV.

  Parameter access : Type.
  Definition ty := Types.ty.

  Inductive enventry : Set :=
    | VarEntry : ty -> enventry
    | FunEntry : list ty -> ty -> enventry.

  Definition enter {A : Set} stbl entry (tbl : @Symbol.table A) :=
    Symbol.enter tbl (Symbol.symbol' (fst entry) stbl) (snd entry).

  Definition tsyms : Symbol.sym_tbl := fold_right Symbol.symbolT Symbol.sym_empty
    ("int" :: "string" :: nil)%string.

  Definition vsyms : Symbol.sym_tbl := fold_right Symbol.symbolT Symbol.sym_empty
    ("print" :: "flush" :: "getchar" :: "ord" :: "chr" :: "size" :: "substring"
     :: "concat" :: "not" :: "exit" :: nil)%string.

  Definition base_tenv := fold_right (enter tsyms) Symbol.empty
    (("int", Types.INT) :: ("string", Types.STRING) :: nil)%string.

  Definition base_venv := fold_right (enter vsyms) Symbol.empty
    (("print", FunEntry (Types.STRING :: nil) Types.UNIT)
     :: ("flush", FunEntry nil Types.UNIT)
     :: ("getchar", FunEntry nil Types.STRING)
     :: ("ord", FunEntry (Types.STRING :: nil) Types.INT)
     :: ("chr", FunEntry (Types.INT :: nil) Types.STRING)
     :: ("size", FunEntry (Types.STRING :: nil) Types.INT)
     :: ("substring", FunEntry (Types.STRING :: Types.INT :: Types.INT :: nil) Types.STRING)
     :: ("concat", FunEntry (Types.STRING :: Types.STRING :: nil) Types.STRING)
     :: ("not", FunEntry (Types.INT :: nil) Types.INT)
     :: ("exit", FunEntry (Types.INT :: nil) Types.UNIT)
     :: nil)%string.

End Env.
