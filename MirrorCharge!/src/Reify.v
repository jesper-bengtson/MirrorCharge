Require Import ILogicFunc.
Require Import ILogic.

Add ML Path "../plugins/_build".
Declare ML Module "reify_ILogicFunc_plugin".

Set Printing All.
Set Implicit Arguments.
Set Strict Implicit.

Ltac reify_goal :=
  match goal with
    | |- ?X =>
      let k t f e := pose e in
      reify_expr X k
  end.

Goal @ltrue Prop _.
reify_goal.
exact I.
Qed.
