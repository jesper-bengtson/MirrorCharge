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

Definition eq_solve : stac typ (expr typ func) subst :=
  fun tus tvs s e =>
    match e with
      | App (App (Inj (inl (inr (pEq tyVar)))) (Inj (inl (inr (pVar x))))) (Inj (inl (inr (pVar y)))) =>
	        match Peano_dec.eq_nat_dec x y with
	          | left _ => @Solved _ _ _ s
	          | right _ => @Fail _ _ _
			end
      | App (App (Inj (inr (ilf_impl tyProp))) (App (App (Inj (inl (inr (pEq tyVar)))) (Inj (inl (inr (pVar x))))) (Inj (inl (inr (pVar y)))))) (Inj (inr (ilf_false tyProp))) =>
	        match Peano_dec.eq_nat_dec x y with
	          | left _ => @Fail _ _ _
	          | right _ => @Solved _ _ _ s
			end
      | _ => More tus tvs s e
   end.

Definition nin_cons_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyVar :: tyVar :: tyList tyVar :: nil
 ; premises := mkneq tyVar (Var 0) (Var 1)::
               lnot tyProp (mkIn (Var 0) (Var 2))::           
               nil
 ; concl := lnot tyProp (mkIn (Var 0) (mkCons tyVar (Var 1) (Var 2)))
 |}.

Definition nin_nil_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyVar :: nil
 ; premises := nil      
 ; concl := lnot tyProp (mkIn (Var 0) (fNil tyVar))
 |}.
 
Definition nodup_nil_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := nil
 ; premises := nil
 ; concl := mkNoDup (fNil tyVar)
 |}.
 
Definition nodup_cons_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyVar :: tyList tyVar :: nil
 ; premises := lnot tyProp (mkIn (Var 0) (Var 1))::
               mkNoDup (Var 1)::
               nil
 ; concl := mkNoDup (mkCons tyVar (Var 0) (Var 1))
 |}.


Definition all_cases : stac typ (expr typ func) subst :=
  REC 5 (fun rec =>
            let rec := rec in
            REPEAT 10
                   (FIRST (eapply_other nin_cons_lemma (FIRST (eq_solve::rec::nil)) ::
                           eapply_other nin_nil_lemma rec::
                           eapply_other nodup_nil_lemma rec::
                           eapply_other nodup_cons_lemma rec 
                           :: nil)))
      (@FAIL _ _ _).

Definition test_eq :=
	let vars := nil in
	let goal := mkeq tyVar (fVar 0) (fVar 0)
	in
	@eq_solve nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_eq.

Definition test_neq :=
	let vars := nil in
	let goal := mkneq tyVar (fVar 9) (fVar 0)
	in
	@eq_solve nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_neq.

Definition test_nil :=
  let vars := nil in
  let goal := lnot tyProp (mkIn (fVar 0) (fNil tyVar))
  in
  @all_cases nil vars (SubstI3.empty (expr :=expr typ func)) goal.

Time Eval vm_compute in test_nil.

Definition test_cons :=
  let vars := nil in
  let goal := lnot tyProp (mkIn (fVar 0) 
  	(mkCons tyVar (fVar 3) ((mkCons tyVar (fVar 2) ((mkCons tyVar (fVar 1) (fNil tyVar)))))))
  in
  @all_cases nil vars (SubstI3.empty (expr :=expr typ func)) goal.

Time Eval vm_compute in test_cons.

Definition test_nodup :=
  let vars := nil in
  let goal := mkNoDup
  	(mkCons tyVar (fVar 3) ((mkCons tyVar (fVar 2) ((mkCons tyVar (fVar 1) (fNil tyVar))))))
  in
  @all_cases nil vars (SubstI3.empty (expr :=expr typ func)) goal.
  
Time Eval vm_compute in test_nodup.
