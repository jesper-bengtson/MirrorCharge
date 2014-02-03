Require Import MirrorCore.Ext.Expr.
Require Import ILogicFunc.
Require Import Tauto.

(**
Add ML Path "../plugins".
Add ML Path "plugins".
Declare ML Module "reify_ILogicFunc_plugin".

Require Import Reify.
**)

Set Implicit Arguments.
Set Strict Implicit.

Require Import ILogic.
Require Import BILogic.
Require Import ILEmbed.

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
  Admitted.

  Goal P ** Q |-- Q ** P.
  Proof.
    prep.
  Admitted.

  Goal P ** Q ** R ** S ** T |-- T ** S ** R ** Q ** P.
  Proof.
    prep.
  Admitted.

  (** Predicate **)
  Variable PT : nat -> nat -> SL.

  Goal PT 1 1 |-- PT 1 1.
  Proof.
    prep.
  Admitted.

  Goal forall w x y z,
         PT w x ** PT x y ** PT y z |-- PT y z ** PT x y ** PT w x.
  Proof.
    prep.
  Admitted.

  (** With Meta-variables **)
  Goal forall w x, exists x',
         PT w x |-- PT w x'.
  Proof.
    prep.
  Admitted.

  Goal forall w x y z, exists x' y' z',
         PT w x ** PT x y ** PT y z |-- PT y' z' ** PT x' y' ** PT w x'.
  Proof.
    prep.
  Admitted.

  (** With premises **)
  Goal forall w x y, x = y ->
                     PT w x |-- PT w y.
  Proof.
    prep.
  Admitted.

  (** With pure predicates **)
  Goal forall w x y,
         PT w x //\\ embed (x = y) |-- PT w y.
  Proof.
    prep.
  Admitted.

  Goal forall w x y,
         PT w x //\\ embed (x = y) |-- PT w y //\\ embed (x = y).
  Proof.
    prep.
  Admitted.

  Goal forall w x y z, exists z',
         (PT w x ** PT x z) //\\ embed (x = y) |-- (PT y z' ** PT w y) //\\ embed (x = y).
  Proof.
    prep.
  Admitted.

  (** With existentials **)
  Goal forall w x,
         PT w x |-- lexists (fun y : nat => PT w y).
  Proof.
    prep.
  Admitted.

  Goal forall w x y,
         PT w x ** PT x y |-- lexists (fun x : nat => PT w x ** lexists (fun y : nat => PT x y)).
  Proof.
    prep.
  Admitted.

  Goal forall w x y,
         PT w x ** PT x y |-- lexists (fun x : nat => lexists (fun y : nat => PT x y ** PT w x)).
  Proof.
    prep.
  Admitted.

  Goal forall w x y,
         PT w x ** PT x y |-- lexists (fun x => x).
  Proof.
    prep.
  Admitted.

  Goal forall w x y,
         PT w x ** PT x y |-- lexists (fun x => x) ** PT x y.
  Proof.
    prep.
  Admitted.

  Goal forall w x y,
         PT w x ** PT x y |-- lexists (fun x => x) ** PT w x.
  Proof.
    prep.
  Admitted.


End SepTests.