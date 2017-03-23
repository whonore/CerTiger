(*
 * Tree.v
 * Wolf Honore
 *
 * Defines the intermediate representation of Tiger code in
 * the form of a tree. The instructions are meant to be closer
 * to assembly instructions.
 *)

Require Import QArith.

Require Import Temp.

Module Type TREE.

  Parameter size : Set.

  Inductive binop : Set :=
    | FPLUS | FMINUS | FDIV | FMUL
    | PLUS | MINUS | MUL | DIV
    | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR.

  Inductive relop : Set :=
    | EQ | NE | LT | GT | LE | GE
    | ULT | ULE | UGT | UGE
    | FEQ | FNE | FLT | FLE | FGT | FGE.

  Inductive cvtop : Set :=
    | CVTSU | CVTSS | CVTSF | CVTUU
    | CVTUS | CVTFS | CVTFF.

  Inductive stm : Set :=
    | SEQ : stm -> stm -> stm
    | LABEL : Temp.label -> stm
    | JUMP : exp -> list Temp.label -> stm
    | CJUMP : test -> Temp.label -> Temp.label -> stm
    | MOVE : exp -> exp -> stm
    | EXP : exp -> stm
  with exp : Set :=
    | BINOP : binop -> exp -> exp -> exp
    | CVTOP : cvtop -> exp -> size -> size -> exp
    | MEM : exp -> size -> exp
    | TEMP : Temp.temp -> exp
    | ESEQ : stm -> exp -> exp
    | NAME : Temp.label -> exp
    | CONST : nat -> exp
    | CONSTF : Q -> exp
    | CALL : exp -> list exp -> exp
  with test : Set :=
    | TEST : relop -> exp -> exp -> test.

  Parameter notRel : relop -> relop.
  Parameter commute : relop -> relop.

End TREE.

Module Tree <: TREE.

  Definition label := Temp.label.
  Definition temp := Temp.temp.
  Definition size := nat.

  Inductive binop : Set :=
    | FPLUS | FMINUS | FDIV | FMUL
    | PLUS | MINUS | MUL | DIV
    | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR.

  Inductive relop : Set :=
    | EQ | NE | LT | GT | LE | GE
    | ULT | ULE | UGT | UGE
    | FEQ | FNE | FLT | FLE | FGT | FGE.

  Inductive cvtop : Set :=
    | CVTSU | CVTSS | CVTSF | CVTUU
    | CVTUS | CVTFS | CVTFF.

  Inductive stm : Set :=
    | SEQ : stm -> stm -> stm
    | LABEL : Temp.label -> stm
    | JUMP : exp -> list Temp.label -> stm
    | CJUMP : test -> Temp.label -> Temp.label -> stm
    | MOVE : exp -> exp -> stm
    | EXP : exp -> stm
  with exp : Set :=
    | BINOP : binop -> exp -> exp -> exp
    | CVTOP : cvtop -> exp -> size -> size -> exp
    | MEM : exp -> size -> exp
    | TEMP : Temp.temp -> exp
    | ESEQ : stm -> exp -> exp
    | NAME : Temp.label -> exp
    | CONST : nat -> exp
    | CONSTF : Q -> exp
    | CALL : exp -> list exp -> exp
  with test : Set :=
    | TEST : relop -> exp -> exp -> test.

  Definition notRel (f : relop) : relop :=
    match f with
    | EQ => NE
    | NE => EQ
    | LT => GE
    | GE => LT
    | GT => LE
    | LE => GT
    | ULT => UGE
    | UGE => ULT
    | ULE => UGT
    | UGT => ULE
    | FEQ => FNE
    | FNE => FEQ
    | FLT => FGE
    | FGE => FLT
    | FGT => FLE
    | FLE => FGT
    end.

  Definition commute (f : relop) : relop :=
    match f with
    | EQ => EQ
    | NE => NE
    | LT => GT
    | GE => LE
    | GT => LT
    | LE => GE
    | ULT => UGT
    | UGE => ULE
    | ULE => UGE
    | UGT => ULT
    | FEQ => FEQ
    | FNE => FNE
    | FLT => FGT
    | FGE => FLE
    | FGT => FLT
    | FLE => FGE
    end.

End Tree.
