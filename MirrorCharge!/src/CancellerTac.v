Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprUnifySyntactic.
Require Import MirrorCore.Ext.FMapSubst.
(* Charge *)
Require Import ILogic BILogic.
(* MirrorCharge *)
Require Import BILNormalize OrderedCanceller SynSepLog.
Require Import SepLogFold.

Set Implicit Arguments.
Set Strict Implicit.

Section ordered_cancel_tac.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.
  Variable RSymOk_func : RSymOk RSym_func.
  Variable tySL : typ.

  Let subst := FMapSubst.SUBST.subst func.
  Local Instance Subst_subst : Subst.Subst subst (expr func) :=
    @FMapSubst.SUBST.Subst_subst _.
  Local Instance SubstOk_subst : @Subst.SubstOk subst (expr func) _ (typD ts) _ _ :=
    @FMapSubst.SUBST.SubstOk_subst _ _ _.

  Definition eprovePure : subst -> expr func -> option subst :=
    fun _ _ => None.

  Definition doUnifySepLog (fuel : nat) (tus tvs : EnvI.tenv typ)
  : subst -> expr func -> expr func -> option subst :=
    fun s e e' =>
      @exprUnify subst ts func _ _ fuel tus tvs 0 s e e' tySL.

  Definition order : conjunctives func -> Conjuncts func :=
    @simple_order _.

  Variable ILogicOps_SL : ILogicOps (typD ts nil tySL).
  Variable ILogic_SL : ILogic (typD ts nil tySL).
  Variable BILOperators_SL : BILOperators (typD ts nil tySL).
  Variable BILogic_SL : BILogic (typD ts nil tySL).
  Variable SSL : SynSepLog func.
  Variable SSLO : SynSepLogOk _ _ _ _ SSL.

  Lemma WellTyped_env_join_env
  : forall tus (us : HList.hlist (typD ts nil) tus),
      WellTyped_env tus (EnvI.join_env us).
  Proof.
    induction tus; intros; red.
    { rewrite (HList.hlist_eta us). simpl. constructor. }
    { rewrite (HList.hlist_eta us). simpl; constructor; auto. apply IHtus. }
  Qed.

  Theorem unifySepLogOk tus tvs
  : unifySepLog_spec SubstOk_subst (doUnifySepLog 100 tus tvs) tySL tus tvs.
  Proof.
    specialize exprUnify_sound; intro unifyOk.
    do 2 red in unifyOk.
    red. unfold doUnifySepLog.
    intros.
    specialize (unifyOk subst ts func _ _ _ _ 100 tus tvs e e' s s' tySL nil H0 H1 H2 H).
    destruct unifyOk.
    split; auto.
    intros.
    specialize (H4 (EnvI.join_env us) (EnvI.join_env vs)).
    apply H4 in H5; eauto using WellTyped_env_join_env.
    destruct H5. specialize (H6 nil).
    split; auto.
    apply H6. constructor.
  Qed.

  Theorem eprovePureOk tus tvs
  : eprovePure_spec SubstOk_subst eprovePure tySL ILogicOps_SL tus tvs.
  Proof.
    red. inversion 1.
  Qed.

  Definition the_canceller (sls : SepLogSpec func) tus tvs (lhs rhs : expr func) s :=
    let lhs_norm := normalize sls lhs tus tvs in
    let rhs_norm := normalize sls rhs tus tvs in
    let '(lhs',rhs',s') :=
        ordered_cancel (doUnifySepLog 100 tus tvs) eprovePure
                       (simple_order (func:=func)) lhs_norm rhs_norm s
    in (conjunctives_to_expr SSL lhs', conjunctives_to_expr SSL rhs', s').

  Variable sls : SepLogSpec func.
  Hypothesis slsOk : @SepLogSpecOk ts _ _ tySL sls _ _.

  Require Import ExtLib.Tactics.

  Ltac forward_reason :=
    repeat match goal with
             | H : ?X , H' : ?X -> _ |- _ =>
               match type of X with
                 | Prop => specialize (H' H)
               end
             | H : ?X -> _ |- _ =>
               match type of X with
                 | Prop => let Z := fresh in
                           assert (Z : X) by eauto ;
                             specialize (H Z) ; clear Z
               end
             | H : _ /\ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
           end.

  Local Instance PureOp_pure : @Pure.PureOp (typD ts nil tySL) := slsOk.(_PureOp).
  Local Instance Pure_pure : @Pure.Pure (typD ts nil tySL) _ _ _ := slsOk.(_Pure).

  Theorem the_cancellerOk (Pure_true : Pure.pure ltrue)
  : forall us vs lhs rhs lhs' rhs' sub,
      the_canceller sls (typeof_env us) (typeof_env vs) lhs rhs (@FMapSubst.SUBST.subst_empty _) = (lhs', rhs', sub) ->
      match exprD us vs lhs' tySL
          , exprD us vs rhs' tySL
      with
        | Some lhs , Some rhs =>
          Subst.substD us vs sub /\
            lhs |-- rhs
        | None , None => True
        | _ , _ => False
      end ->
      match exprD us vs lhs tySL
          , exprD us vs rhs tySL
      with
        | Some lhs , Some rhs =>
          lhs |-- rhs
        | _ , _ => True
      end.
  Proof.
    unfold the_canceller. intros.
    consider (split_env us); intros.
    generalize (@normalizeOk ts func _ _ _ _ _ _ sls slsOk SSL SSLO lhs us (typeof_env vs)).
    generalize (@normalizeOk ts func _ _ _ _ _ _ sls slsOk SSL SSLO rhs us (typeof_env vs)).
    consider (split_env vs); intros.
    consider (ordered_cancel
              (doUnifySepLog 100 (typeof_env us) (typeof_env vs)) eprovePure
              (simple_order (func:=func))
              (normalize sls lhs (typeof_env us) (typeof_env vs))
              (normalize sls rhs (typeof_env us) (typeof_env vs))
              (SUBST.subst_empty func)).
    destruct p; intros.
    assert (typeof_env us = x).
    { unfold typeof_env. rewrite <- split_env_projT1.
      rewrite H1. reflexivity. }
    assert (typeof_env vs = x0).
    { unfold typeof_env. rewrite <- split_env_projT1.
      rewrite H2. reflexivity. }
    rewrite H6 in *.
    rewrite H7 in *.
    generalize (@ordered_cancelOk ts func RSym_func subst Subst_subst _
                             (doUnifySepLog 100 x x0)
                             eprovePure tySL ILogicOps_SL BILOperators_SL _ _ x x0
                             (@unifySepLogOk x x0)
                             (@eprovePureOk x x0)
                             SSL SSLO _ _ Pure_true
                             (@simple_order func)
                             (@simple_orderOk ts func _ tySL _ _ _ _ SSL SSLO _)
                             h
                             (normalize sls lhs x x0)
                             (normalize sls rhs x x0)
                             (@FMapSubst.SUBST.subst_empty _)
                             c c0 s H).
    repeat match goal with
             | _ : context [ normalize ?A ?B ?C ?D ] |- _ =>
               generalize dependent (normalize A B C D); intros
           end.
    unfold exprD in *.
    rewrite H2 in *.
    inv_all; subst.
    assert (us = join_env h).
    { apply split_env_projT2_join_env. auto. }
    rewrite <- H5 in *.
    forward.
    assert (Subst.WellTyped_subst (typeof_env us) (typeof_env vs)
          (SUBST.subst_empty func)) by eapply Subst.WellTyped_empty.
    forward_reason.
    specialize (H14 h0).
    specialize (H7 h0).
    specialize (H10 h0).
    assert (vs = join_env h0).
    { apply split_env_projT2_join_env. auto. }
    rewrite <- H16 in *.
    forward_reason.
    rewrite H7. rewrite H10. assumption.
  Qed.
End ordered_cancel_tac.

(* Check the_cancellerOk. *)

(**
 ** The last bits are the following
 **
 ** 1) Build a [SepLogSpec]
 ** 2) Build a [SynSepLog]
 **
 ** Both of these should be doable from a single piece of data that records
 ** where particular features are.
 **)

Section SepLogBuilder.
  Require Import ILogicFunc.

  Variable ts : types.
  Variables (FM : fun_map ts) (LM : logic_ops ts) (EM : embed_ops ts).
  Let func := ilfunc.
  Local Instance RSym_func : RSym (typD ts) func := @RSym_ilfunc ts FM LM EM.

  Record ConcreteSepLog tySL (BILO : BILOperators (typD ts nil tySL)) : Type :=
  { ctor_star : func
  ; ctor_emp : func
  ; starOk : forall us tvs,
    exprD' us tvs (Inj ctor_star) (tyArr tySL (tyArr tySL tySL)) = Some (fun _ => sepSP)
  ; empOk : forall us tvs,
    exprD' us tvs (Inj ctor_emp) tySL = Some (fun _ => empSP)
  }.

  Variable func_eq : func -> func -> bool.
  Hypothesis func_eqOk : forall a b, func_eq a b = true -> a = b.

  (** NOTE: My [ILogic] must come form LM **)
  Variable (tySL : typ).
  Variable (OPS : ILogicOps (typD ts nil tySL)).
  Hypothesis LM_OPS : LM tySL = Some OPS.
  Variable (BILO : BILOperators (typD ts nil tySL)).
  Variable (csl : @ConcreteSepLog tySL BILO).

  Variable PureOp : @Pure.PureOp (typD ts nil tySL).
  Variable PureLaws : @Pure.Pure _ OPS BILO PureOp.

  Definition SepLogSpec_ConcreteSepLog : SepLogSpec func :=
  {| is_pure := fun _ => false
   ; is_emp := func_eq csl.(ctor_emp)
   ; is_star := func_eq csl.(ctor_star)
  |}.

  Theorem SepLogSpecOk_ConcreteSepLog
  : @SepLogSpecOk ts _ RSym_func tySL SepLogSpec_ConcreteSepLog OPS BILO.
  Proof.
    refine (@Build_SepLogSpecOk _ _ _ _ _ _ _ PureOp PureLaws _ _ _).
    { inversion 1. }
    { simpl; intros.
      eapply func_eqOk in H. subst.
      unfold exprD. destruct (split_env vs).
      rewrite (csl.(empOk) us x). reflexivity. }
    { simpl; intros.
      eapply func_eqOk in H. subst.
      unfold exprD. destruct (split_env vs).
      rewrite (csl.(starOk) us x). reflexivity. }
  Qed.

  Definition SynSepLog_ConcreteSepLog : SynSepLog ilfunc :=
  {| e_star := fun (a b : expr ilfunc) => App (App (Inj csl.(ctor_star)) a) b
   ; e_emp := Inj csl.(ctor_emp)
   ; e_true := Inj (ilf_true tySL)
   ; e_and := fun (a b : expr ilfunc) => App (App (Inj (ilf_and tySL)) a) b
   |}.

  Hypothesis LMok : logic_opsOk LM.

  Local Instance ILogic_OPS : @ILogic _ OPS.
  Proof.
    specialize (LMok tySL).
    rewrite LM_OPS in LMok. assumption.
  Defined.

  Lemma typeof_star : typeof_sym (ctor_star csl) = Some (tyArr tySL (tyArr tySL tySL)).
  Proof.
    generalize (csl.(starOk) nil nil).
    red_exprD.
    generalize dependent (symD (ctor_star csl)).
    forward. inv_all; subst. reflexivity.
  Qed.

  Theorem typ_eqb_complete : forall x, typ_eqb x x = true.
  Proof.
    clear. induction x; simpl; Cases.rewrite_all_goal; auto.
    { match goal with
        | |- ?X = _ => consider X
      end; auto. }
    { match goal with
        | |- ?X = _ => consider X
      end; auto. }
  Qed.

  Theorem SynSepLogOk_ConcreteSepLog
  : @SynSepLogOk ts ilfunc _ tySL OPS BILO SynSepLog_ConcreteSepLog.
  Proof.
    constructor; simpl; intros.
    { eexists. split. apply (csl.(empOk) us tvs).
      intros. reflexivity. }
    { red_exprD.
      simpl.
      rewrite LM_OPS.
      rewrite typ_cast_typ_refl.
      eexists; split; eauto. simpl. reflexivity. }
    { generalize (csl.(starOk) us tvs).
      red_exprD. intros.
      forward. inv_all; subst.
      exists (fun g => sepSP (valx g) (valy g)).
      split; [ | intros; reflexivity ].
      generalize typeof_star. simpl. intro.
      rewrite H3. simpl.
      rewrite exprD'_type_cast in H.
      rewrite exprD'_type_cast in H0.
      forward.
      repeat match goal with
               | H : ?X = _ |- context [ ?Y ] =>
                 change Y with X ; rewrite H
             end.
      inv_all; subst.
      rewrite typ_eqb_complete.
      red_exprD.
      rewrite H3.
      red_exprD.
      rewrite H1.
      repeat match goal with
               | H : ?X = _ |- context [ ?Y ] =>
                 change Y with X ; rewrite H
             end.
      f_equal.
      change (let K := (fun x g => (x g) (t3 g) (t1 g)) in
              K (fun _ : HList.hlist (typD ts nil) tvs => t) =
              K (fun _ : HList.hlist (typD ts nil) tvs => sepSP)).
      intro. clearbody K. f_equal. auto. }
    { generalize (csl.(starOk) us tvs); intros.
      red_exprD.
      forward. inv_all; subst.
      generalize dependent (symD (ctor_star csl)).
      rewrite typeof_star.
      simpl. rewrite typ_cast_typ_refl.
      intros. inv_all; subst.
      red_exprD.
      forward. inv_all; subst.
      simpl in H8.
      forward. inv_all; subst.
      assert (t6 = tySL /\ t1 = tySL).
      { generalize typeof_star. simpl.
        intro. rewrite H in *.
        inv_all. auto. }
      destruct H; subst.
      do 2 eexists. split; eauto. split; eauto.
      rewrite csl.(starOk) in H3. inv_all. subst.
      reflexivity. }
    { red_exprD.
      rewrite LM_OPS.
      rewrite exprD'_type_cast in H.
      forward. inv_all; subst.
      simpl.
      rewrite typ_eqb_complete.
      red_exprD.
      rewrite LM_OPS.
      red_exprD.
      rewrite LM_OPS.
      rewrite typ_cast_typ_refl.
      rewrite H2. rewrite H0. eexists; split; eauto.
      simpl. reflexivity. }
    { red_exprD.
      rewrite LM_OPS in H.
      forward. inv_all; subst.
      red_exprD.
      rewrite LM_OPS in H1.
      forward. inv_all; subst.
      red_exprD.
      simpl in *; rewrite LM_OPS in H.
      forward. inv_all. subst t4 t0 t t2 p.
      do 2 eexists; split; eauto. split; eauto.
      intros.
      uip_all. reflexivity. }
  Qed.
End SepLogBuilder.