Require Import MirrorCore.Ext.Expr.
(** Charge **)
Require Import ILogic BILogic ILEmbed.
(** MirrorCharge **)
Require Import ILogicFunc.
Require Import OrderedCanceller.

Add ML Path "../plugins".
Add ML Path "plugins".
Declare ML Module "reify_ILogicFunc_plugin".

Require Import Reify. (** Note: this is from MirrorCharge **)

Set Implicit Arguments.
Set Strict Implicit.

(** Test cases for the core of separation logic **)
Section SepTests.
  Variable SL : Type.
  Context `{ILogic_SL : ILogic SL}.
  Context `{BILogic_SL : BILogic SL}.
  Context `{Embed_SL : EmbedOp Prop SL}.

  Ltac prep := intros;
    repeat match goal with
             | |- exists x , _ => eexists
           end.

  (** Propositional **)
  Variables P Q R S T : SL.

  Goal P |-- P.
  Proof.
    prep.
  Abort.

  Goal P ** Q |-- Q ** P.
  Proof.
    prep.
  Abort.

  Goal P ** Q ** R ** S ** T |-- T ** S ** R ** Q ** P.
  Proof.
    prep.
  Abort.

  (** Predicate **)
  Variable PT : nat -> nat -> SL.

  Goal PT 1 1 |-- PT 1 1.
  Proof.
    prep.
  Abort.

  Goal forall w x y z,
         PT w x ** PT x y ** PT y z |-- PT y z ** PT x y ** PT w x.
  Proof.
    prep.
  Abort.

  (** With Meta-variables **)
  Goal forall w x, exists x',
         PT w x |-- PT w x'.
  Proof.
    prep.
  Abort.

  Goal forall w x y z, exists x' y' z',
         PT w x ** PT x y ** PT y z |-- PT y' z' ** PT x' y' ** PT w x'.
  Proof.
    prep.
  Abort.

  (** With premises **)
  Goal forall w x y, x = y ->
                     PT w x |-- PT w y.
  Proof.
    prep.
  Abort.

  (** With pure predicates **)
  Goal forall w x y,
         PT w x //\\ embed (x = y) |-- PT w y.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x //\\ embed (x = y) |-- PT w y //\\ embed (x = y).
  Proof.
    prep.
  Abort.

  Goal forall w x y z, exists z',
         (PT w x ** PT x z) //\\ embed (x = y) |-- (PT y z' ** PT w y) //\\ embed (x = y).
  Proof.
    prep.
  Abort.

  (** With existentials **)
  Goal forall w x,
         PT w x |-- lexists (fun y : nat => PT w y).
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- Exists x : nat, PT w x ** Exists y : nat, PT x y.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- Exists x, Exists y, PT x y ** PT w x.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- Exists x, x.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- (Exists x, x) ** PT x y.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- (Exists x, x) ** PT w x.
  Proof.
    prep.
  Abort.

  (** With existentials & pure premises **)
  Goal forall w x y,
         PT w x ** PT x y |--
         Exists w', Exists x', Exists y', Exists z',
           PT w' x' ** PT y' z' //\\ embed (w = w') //\\ embed (y' = x).
  Proof.
    (** This is potentially very difficult because you have to propagate information
     ** from the right-hand-side pure facts before solving the unification problem.
     **)
    prep.
  Abort.

End SepTests.