Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.STacSimplify.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.

Definition imp_tac := rtac typ (expr typ func).
Definition imp_tacK := rtacK typ (expr typ func).

Definition EAPPLY lem : imp_tac :=
  THEN (@EAPPLY typ (expr typ func) _ _ _ _ ExprLift.vars_to_uvars
                 (fun subst S_subst SU tus tvs n e1 e2 s t =>
                    @exprUnify subst typ func _ RS _ S_subst SU 3
                               tus tvs n e1 e2 s t)
                 lem)
       (@MINIFY _ _ _).

Theorem EAPPLY_sound
: forall lem,
    Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil lem ->
    rtac_sound (EAPPLY lem).
Proof.
  intros. eapply THEN_sound.
  - eapply EAPPLY_sound; eauto with typeclass_instances.
    admit. admit.
  - eapply MINIFY_sound.
Qed.

Definition APPLY lem : imp_tac :=
  THEN (@APPLY typ (expr typ func) _ _ _ _ ExprLift.vars_to_uvars
                (fun subst S_subst SU tus tvs n e1 e2 s t =>
                   @exprUnify subst typ func _ RS _ S_subst SU 3
                              tus tvs n e1 e2 s t)
                lem)
       (@MINIFY _ _ _).

Theorem APPLY_sound
: forall lem,
    Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil lem ->
    rtac_sound (EAPPLY lem).
Proof.
  intros. eapply THEN_sound.
  - eapply APPLY_sound; eauto with typeclass_instances.
    admit. admit.
  - eapply MINIFY_sound.
Qed.

Definition SIMPLIFY : imp_tac :=
  SIMPLIFY (fun _ _ _ _ => beta_all (idred simplify)).

Theorem SIMPLIFY_sound : rtac_sound SIMPLIFY.
Proof.
  eapply SIMPLIFY_sound. intros.
  unfold Ctx.propD, exprD'_typ0 in *.
  Require Import ExtLib.Tactics.
  forward. inv_all. subst.
Admitted.

Definition runOnGoals (t : imp_tac) : imp_tacK := runOnGoals t.
Coercion runOnGoals : imp_tac >-> imp_tacK.

Definition runImpTac (tus tvs : tenv _) (goal : expr _ _) (tac : imp_tac) :=
  tac tus tvs (length tus) (length tvs) _ (TopSubst _ tus tvs) goal.