Require Import MirrorCore.Ext.Expr.
Require Import ILogicFunc.
Require Import ILogic.

Add ML Path "plugins".
Add ML Path "../plugins".
Declare ML Module "reify_ILogicFunc_plugin".

Set Printing All.
Set Implicit Arguments.
Set Strict Implicit.

Definition Provable a b c d e f : Prop :=
  match @exprD a b c d e f tyProp with
    | Some x => x
    | None => False
  end.

Definition foo : list (option Type) := @cons (option Type) (@Some Type nat) nil.
Inductive Dyn : Type :=
| dynamic : forall T, T -> Dyn.
Definition funcs : list (option Dyn) := (Some (dynamic plus)) :: (Some (dynamic mult)) :: nil.
Axiom ILogicOps_ext : forall (A B : Type), ILogicOps B -> ILogicOps (A -> B).

Definition logics : list (@sigT Type ILogicOps) :=
  (@existT _ _ (nat -> Prop) (@ILogicOps_ext nat Prop _)) :: nil.
Ltac reify_goal := idtac ;
  match goal with
    | |- ?X =>
      let k t f l e :=
          let funcs := fresh "funcs" in
          try pose (funcs := @RSym_ilfunc_ctor t f l nil) ;
          (try change (@Provable t ilfunc funcs nil nil e))
      in
      let ts := eval cbv delta [foo] in foo in
      let fs := eval cbv delta [funcs] in funcs in
      let ls := eval cbv delta [logics] in logics in
      reify_expr {types:ts} {funcs:fs} {logics:ls} [X] k
  end.

Goal True.
intros. reify_goal.
exact I.
Qed.

Goal forall a b : Prop, a -> b -> a /\ b.
intros ? ? H H0. reify_goal.
exact (conj H H0).
Qed.

Goal forall a : Prop, a -> a.
intro. reify_goal.
refine (fun x => x).
Qed.

Goal True -> True.
reify_goal.
refine (fun x => x).
Qed.

Goal False -> False.
reify_goal.
(** There seems to be a bug in Coq if you solve this using:
 **   [fun x => match x with end]
 ** or I am constructing a bad term, but I can't tell.
 **)
refine (fun x => x).
Qed.