(** This file contains some example programs that I can verify
 **)
Require Import Coq.Strings.String.
Require Import MirrorCharge.Imp.Imp.

Local Notation "x ;; y" := (Seq x y) (at level 30, y at next level).
Local Notation "x <- y" := (Assign x%string y) (at level 20).
Local Notation "$ x" := (iVar x%string) (at level 5).
Let iConst' : nat -> iexpr := iConst.
Local Coercion iConst' : nat >-> iexpr.

Local Open Scope string_scope.

Definition Add1 : icmd :=
  "x"    <- (iPlus $"x" 1).

Definition Swap : icmd :=
  "temp" <- $"x" ;;
  "x"    <- $"y" ;;
  "y"    <- $"temp".

Definition IfZero : icmd :=
  If $"x"
     ("y" <- 1)
     ("y" <- 0).

Definition While : icmd :=
  While (iLt $"x" 10)
        ("x" <- iPlus $"x" 1).