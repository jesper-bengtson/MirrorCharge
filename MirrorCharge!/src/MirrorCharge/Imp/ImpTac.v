Require Import MirrorCore.STac.STac.
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
Local Existing Instance Expr_expr.

Definition EAPPLY lem tac : stac typ (expr typ func) subst :=
  @EAPPLY typ (expr typ func) subst _ _ ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func) SS SU
                lem (apply_to_all tac).

Definition APPLY lem tac : stac typ (expr typ func) subst :=
  @APPLY typ (expr typ func) subst _ _ ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func) SS SU
                lem (apply_to_all tac).

Definition SIMPLIFY : stac typ (expr typ func) subst :=
  SIMPLIFY (fun _ _ _ => beta_all simplify nil nil).