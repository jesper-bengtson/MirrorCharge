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

Ltac reify_goal :=
  match goal with
    | |- ?X =>
      let k t f l e :=
          idtac e ;
          pose e ;
          let funcs := fresh "funcs" in
          try pose (funcs := @RSym_ilfunc_ctor t f l nil) ;
          (try change (@Provable t ilfunc funcs nil nil e))
      in
      reify_expr X k
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