Require Import ExtLib.Tactics.
Require Import MapPositive.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprLift.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import MirrorCore.Ext.AppFull.
Require Import MirrorCore.Ext.SetoidFold.
(** Charge **)
Require Import ILogic ILInsts.
(** MirrorCharge **)
Require Import ILogicFunc.
Require Import ILFFold SepLogFold.
Require Import ILPullQuantStar.
Require Import CancellerTac.
Require Import SynSepLog.

Section QuantCancel.
    Context (ts : types) (funcs : fun_map ts).
    Context (gs : logic_ops ts) {gsOk : logic_opsOk gs}.
    Context {es : embed_ops ts} {esOk : embed_opsOk gs es}.

    Variable slspec : SepLogSpec ilfunc.
    Variable synsl : SynSepLog ilfunc.

    Variable ltyp : typ.

    Definition subst := FMapSubst.SUBST.subst ilfunc.

    Local Instance RSym_sym : SymI.RSym (typD ts) ilfunc := RSym_ilfunc funcs gs es.

    Definition lift_uvars {func : Type} : nat -> nat -> expr func -> expr func := fun _ _ p => p.

    Definition pull_exists :=
      @app_fold (option (list typ * expr ilfunc))
                pq_var pq_uvar pq_inj pq_abs (pq_app slspec) pq_exists pq_forall.

    Record CancelResult : Type :=
    { NewExs : tenv typ
    ; Subst  : RawSubst2.list_subst (expr ilfunc)
    ; Lhs    : expr ilfunc
    ; Rhs    : expr ilfunc
    }.

    Definition qcancel (tus tvs : tenv typ) (P Q : expr ilfunc)
    : option CancelResult :=
      match pull_exists Q tus tvs with
	| Some (xs, Q') =>
	  let P' := lift_uvars (length tus) (length xs) P in
	  let Q'' := vars_to_uvars (length tus) 0 (length xs) Q' in
	  let '(lhs, rhs, s') :=
              @the_canceller ts ilfunc _ ltyp synsl slspec (tus++xs) tvs
                             P' Q'' (FMapSubst.SUBST.subst_empty _)
          in Some {| NewExs := xs ; Lhs := lhs ; Rhs := rhs ; Subst := s' |}
	| None => None
      end.

End QuantCancel.

(** TODO: We're shadowing notation somewhere? **)
Require Import ILogic.
Require Import BILogic.

Definition canceller_post
           (ts : types)
           (FM : fun_map ts) (LM : logic_ops ts) (EM : embed_ops ts)
           (tySL : typ)
           (ILogicOps_SL : ILogicOps (typD ts nil tySL))
           us vs lhs rhs : Prop :=
  let rsym := @RSym_ilfunc ts FM LM EM in
  match @exprD typ (typD ts) (expr ilfunc) (Expr_expr rsym) us vs lhs tySL with
    | Some lhs0 =>
      match @exprD typ (typD ts) (expr ilfunc) (Expr_expr rsym) us vs rhs tySL with
        | Some rhs0 => lhs0 |-- rhs0
        | None => True
      end
    | None => True
  end.

Section existsAll.
  Variable ts : types.

  Fixpoint existsAll (tvs : tenv typ) : (HList.hlist (typD ts nil) tvs -> Prop) -> Prop :=
    match tvs as tvs return (HList.hlist (typD ts nil) tvs -> Prop) -> Prop with
      | nil => fun k => k (@HList.Hnil _ _)
      | tv :: tvs => fun k =>
        exists x : typD ts nil tv,
          existsAll tvs (fun g => k (HList.Hcons x g))
    end.
End existsAll.

Check @ExprI.exprD'.

Definition canceller_pre
           (ts : types)
           (FM : fun_map ts) (LM : logic_ops ts) (EM : embed_ops ts)
           (tySL : typ)
           (ILogicOps_SL : ILogicOps (typD ts nil tySL))
           us vs (res : CancelResult) : Prop :=
  let rsym := @RSym_ilfunc ts FM LM EM in
  let E := Expr_expr rsym in
  match res with
    | {| NewExs := texs ; Lhs := lhs' ; Rhs := rhs' ; Subst := sub |} =>
      let (tus,us) := split_env us in
      let (tvs,vs') := split_env vs in
      match
        @ExprI.exprD' _ _ _ E (tus ++ texs) tvs lhs' tySL with
        | Some lhs' =>
          match @ExprI.exprD' _ _ _ E (tus ++ texs) tvs rhs' tySL with
            | Some rhs' =>
              existsAll ts texs (fun us' =>
                let us := HList.hlist_app us us' in
                fold_right and
                           (lhs' us vs' |-- rhs' us vs')
                           (@Subst2.substD
                              (RawSubst2.list_subst (expr ilfunc)) typ (typD ts)
                              (expr ilfunc)
                              (Expr_expr rsym)
                              (RawSubst2.Subst_list_subst _)
                              (RawSubst2.SubstOk_list_subst _) (join_env us) vs sub))
            | None => False
          end
        | None =>
          match @ExprI.exprD' _ _ _ E (tus ++ texs) tvs rhs' tySL with
            | Some _ => False
            | None => True
          end
      end
  end.

Theorem apply_the_canceller
        (ts : types)
        (FM : fun_map ts) (LM : logic_ops ts) (EM : embed_ops ts)
        (LMok : logic_opsOk LM) (EMok : embed_opsOk LM EM)
        (tySL : typ)
        (ILogicOps_SL : ILogicOps (typD ts nil tySL))
        (pf : LM tySL = Some ILogicOps_SL)
        (BILO : BILOperators (typD ts nil tySL))
        (BIL : BILogic (typD ts nil tySL))
        (PureOp : @Pure.PureOp (typD ts nil tySL))
        (PureLaws : @Pure.Pure _ ILogicOps_SL BILO PureOp)
        (Hpuretrue : Pure.pure ltrue)
        (CSL : ConcreteSepLog)
        (CSLok : @ConcreteSepLogOk ts FM LM EM tySL BILO CSL)
: forall (us vs : env (typD ts)) (lhs rhs : expr ilfunc) result,
    @qcancel ts FM LM EM
                  (@SepLogSpec_ConcreteSepLog CSL)
                  (@SynSepLog_ConcreteSepLog_smart tySL CSL)
                  tySL
                  (typeof_env us) (typeof_env vs) lhs rhs =
    Some result ->
    @canceller_pre ts FM LM EM tySL ILogicOps_SL us vs result ->
    @canceller_post ts FM LM EM tySL ILogicOps_SL us vs lhs rhs.
Proof.
(*  intros.
  eapply the_cancellerOk in H; eauto with typeclass_instances.
  { eapply SynSepLogOk_ConcreteSepLog_smart; eauto. }
  { unfold SepLogSpec_ConcreteSepLog.
    instantiate (1 := @SepLogSpecOk_ConcreteSepLog _ _ _ _ _ _ _ _ _ _ _).
    eapply Hpuretrue. }
  Grab Existential Variables.
  eapply CSLok. (** TODO: This is sketchy! **)
Qed.
*)
Admitted.