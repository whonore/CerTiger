(*
 * Env.v
 * Wolf Honore
 *
 * Defines type and variable namespaces.
 *)

Require Import List.

Require Import Symbol.
Require Import Types.

Module Type ENV.

  Parameter access : Type.
  Parameter ty : Set.

  Inductive rw : Set :=
    | RO : rw
    | RW : rw.

  Inductive enventry : Set :=
    | VarEntry : ty -> rw -> enventry
    | FunEntry : list ty -> ty -> enventry.

  Parameter base_tenv : @Symbol.table ty.
  Parameter base_venv : @Symbol.table enventry.

End ENV.

Module Env <: ENV.

  Parameter access : Type.
  Definition ty := Types.ty.

  Inductive rw : Set :=
    | RO : rw
    | RW : rw.

  Inductive enventry : Set :=
    | VarEntry : ty -> rw -> enventry
    | FunEntry : list ty -> ty -> enventry.

  (* Define the built-in names. It's ok to reuse symbols between types and vars
     since they'll be in different tables. *)

  Definition tsyms : Symbol.sym_tbl := Symbol.make_syms
    (0 :: 1 :: nil).
  Definition s_int := Symbol.symbol' 0 tsyms.
  Definition s_string := Symbol.symbol' 1 tsyms.

  Definition vsyms : Symbol.sym_tbl := Symbol.make_syms
    (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil).
  Definition s_print := Symbol.symbol' 0 vsyms.
  Definition s_flush := Symbol.symbol' 1 vsyms.
  Definition s_getchar := Symbol.symbol' 2 vsyms.
  Definition s_ord := Symbol.symbol' 3 vsyms.
  Definition s_chr := Symbol.symbol' 4 vsyms.
  Definition s_size := Symbol.symbol' 5 vsyms.
  Definition s_substring := Symbol.symbol' 6 vsyms.
  Definition s_concat := Symbol.symbol' 7 vsyms.
  Definition s_not := Symbol.symbol' 8 vsyms.
  Definition s_exit := Symbol.symbol' 9 vsyms.

  (* Create the inital namespaces. *)

  Definition enter {A : Set} stbl entry (tbl : @Symbol.table A) :=
    Symbol.enter tbl (Symbol.symbol' (fst entry) stbl) (snd entry).

  Definition base_tenv := fold_right (enter tsyms) Symbol.empty
    ((s_int, Types.INT) :: (s_string, Types.STRING) :: nil).

  Definition base_venv := fold_right (enter vsyms) Symbol.empty
    ((s_print, FunEntry (Types.STRING :: nil) Types.UNIT)
     :: (s_flush, FunEntry nil Types.UNIT)
     :: (s_getchar, FunEntry nil Types.STRING)
     :: (s_ord, FunEntry (Types.STRING :: nil) Types.INT)
     :: (s_chr, FunEntry (Types.INT :: nil) Types.STRING)
     :: (s_size, FunEntry (Types.STRING :: nil) Types.INT)
     :: (s_substring, FunEntry (Types.STRING :: Types.INT :: Types.INT :: nil) Types.STRING)
     :: (s_concat, FunEntry (Types.STRING :: Types.STRING :: nil) Types.STRING)
     :: (s_not, FunEntry (Types.INT :: nil) Types.INT)
     :: (s_exit, FunEntry (Types.INT :: nil) Types.UNIT)
     :: nil).

End Env.
