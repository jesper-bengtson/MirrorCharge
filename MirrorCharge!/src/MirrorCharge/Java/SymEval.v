Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.provers.DefaultProver.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst3.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Java.Syntax.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Local Notation "a @ b" := (@App typ _ a b) (at level 30).

Let eapply_other :=
  @eapply_other typ (expr typ func) subst tyProp ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3 nil
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func) SS SU.

Definition nin_cons_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyVar :: tyVar :: tyList tyVar :: nil
 ; premises := (*mkeq tyVar (Var 0) (Var 1)::*)
               lnot tyProp (mkIn (Var 0) (Var 2))::           
               nil
 ; concl := lnot tyProp (mkIn (Var 0) (mkCons tyVar (Var 1) (Var 2)))
 |}.

Definition nin_nil_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyVar :: nil
 ; premises := nil      
 ; concl := lnot tyProp (mkIn (Var 0) (fNil tyVar))
 |}.

Definition all_cases : stac typ (expr typ func) subst :=
  REC 5 (fun rec =>
            let rec := rec in
            REPEAT 10
                   (FIRST (   eapply_other nin_cons_lemma rec ::
                              eapply_other nin_nil_lemma rec 
                           :: nil)))
      (@FAIL _ _ _).
      
      
Definition test_nil :=
  let vars := nil in
  let goal := lnot tyProp (mkIn (fVar 0) (fNil tyVar))
  in
  @all_cases nil vars (SubstI3.empty (expr :=expr typ func)) goal.

Time Eval vm_compute in test_nil.

Definition test_cons :=
  let vars := nil in
  let goal := lnot tyProp (mkIn (fVar 0) (mkCons tyVar (fVar 0) (fNil tyVar)))
  in
  @all_cases nil vars (SubstI3.empty (expr :=expr typ func)) goal.

Time Eval vm_compute in test_cons.

