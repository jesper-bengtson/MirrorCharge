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
Local Existing Instance Expr_expr.

Definition EAPPLY lem : rtac typ (expr typ func) :=
  THEN (@EAPPLY typ (expr typ func) _ _ _ _ ExprLift.vars_to_uvars
                 (fun subst S_subst SU tus tvs n e1 e2 s t =>
                    @exprUnify subst typ func _ RS _ S_subst SU 3
                               tus tvs n e1 e2 s t)
                 lem)
       (@MINIFY _ _ _).

Definition APPLY lem : rtac typ (expr typ func) :=
  THEN (@APPLY typ (expr typ func) _ _ _ _ ExprLift.vars_to_uvars
                (fun subst S_subst SU tus tvs n e1 e2 s t =>
                   @exprUnify subst typ func _ RS _ S_subst SU 3
                              tus tvs n e1 e2 s t)
                lem)
       (@MINIFY _ _ _).

Definition SIMPLIFY : rtac typ (expr typ func) :=
  SIMPLIFY (fun _ _ _ _ => beta_all (idred simplify)).