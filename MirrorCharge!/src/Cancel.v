(** This file implements cancellation for separation logic.
 **
 ** Phase 1)
 ** - Support star and emp
 **)
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import BILogic.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.
Require Import ILogicFunc SepLogFold.

Set Implicit Arguments.
Set Strict Implicit.

Section cancel_state.
  Record conjunctives : Type :=
  { spacial : list (expr ilfunc * list (expr ilfunc)) }.

  Definition empty : conjunctives :=
    {| spacial := nil |}.

  Definition atomic e : conjunctives :=
    {| spacial := app_full e :: nil |}.

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

    Definition test := fun x => app_fold_args normalizeArgs x nil nil.
    Eval compute in  test inj_emp.
    Eval compute in  test (inj_star inj_emp inj_emp).
    Eval compute in  test (inj_star (Var 0) (inj_star inj_emp (inj_and (Var 1) (Var 3)))).
  End demo.

  Require Import ExtLib.Structures.Monads.
  Require Import ExtLib.Data.Monads.StateMonad.

  Section with_monad.
    Local Open Scope monad_scope.
    Import MonadNotation.

    Definition conjunctives_remove (c : conjunctives) (e : expr ilfunc)
    : option conjunctives:= None.

  Definition cancel_atomic (e : expr ilfunc) : state conjunctives conjunctives :=
    (lhs <- get ;;
     match conjunctives_remove lhs e with
       | None => (** it wasn't found **)
         ret (atomic e)
       | Some r =>
         put r ;;
         ret empty
     end)%monad.

  Definition cancelArgs : AppFullFoldArgs ilfunc (state conjunctives conjunctives) :=
  {| do_var := fun v _ _ => cancel_atomic (Var v)
   ; do_uvar := fun u _ _ => cancel_atomic (UVar u)
   ; do_inj := fun i _ _ => cancel_atomic (Inj i)
   ;


  Definition cancel (rhs : expr ilfunc) : conjunctives -> (conjunctives * conjunctives).


End cancel_state.