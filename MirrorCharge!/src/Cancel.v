(** This file implements cancellation for separation logic.
 **
 ** Phase 1)
 ** - Support star and emp
 **)
Require Import ExtLib.Data.Positive.
Require Import BILogic.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.
Require Import ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.

Section cancel_state.
  Record conjunctives : Type :=
  { spacial : list (expr ilfunc * list (expr ilfunc)) }.

  Definition empty : conjunctives :=
    {| spacial := nil |}.

  Definition atomic e : conjunctives :=
    {| spacial := (e,nil) :: nil |}.

  Definition atomic_app e es : conjunctives :=
    {| spacial := (e, es) :: nil |}.

  Definition join (l r : conjunctives) : conjunctives :=
    {| spacial := l.(spacial) ++ r.(spacial) |}.

  Definition is_emp (i : ilfunc) : bool :=
    match i with
      | ilf_true _ => true
      | _ => false
    end.
  Definition is_star (e : expr ilfunc) : bool :=
    match e with
      | Inj (fref 1%positive) => true
      | _ => false
    end.

  Definition normalizeArgs : AppFullFoldArgs ilfunc conjunctives :=
  {| do_var := fun v _ _ => atomic (Var v)
   ; do_uvar := fun u _ _ => atomic (UVar u)
   ; do_inj := fun i _ _ => if is_emp i then empty else atomic (Inj i)
   ; do_abs := fun t e _ _ _ => atomic (Abs t e)
   ; do_app := fun f _ args tus tvs =>
                 if is_star f then
                   match args with
                     | (_,l) :: (_,r) :: nil =>
                       join (l tus tvs) (r tus tvs)
                     | _ => empty
                   end
                 else
                   atomic_app f (map fst args)
  |}.

  Section demo.
    Definition inj_emp := Inj (ilf_true (tyType 0)).
    Definition inj_star a b :=
      Eval compute in apps (Inj (fref 1%positive)) (a :: b :: nil).

    Definition test := app_fold_args normalizeArgs.
    Eval compute in  test inj_emp.
    Eval compute in  test (inj_star inj_emp inj_emp).
    Eval compute in  test (inj_star (Var 0) (inj_star inj_emp (inj_and (Var 1) (Var 3)))).
  End demo.
End cancel_state.