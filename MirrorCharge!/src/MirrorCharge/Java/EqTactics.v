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


Definition eq_solve : stac typ (expr typ func) subst :=
  fun tus tvs s e =>
    match e with
      | App (App (Inj (inl (inr (pEq tyVar)))) (Inj (inl (inr (pVar x))))) (Inj (inl (inr (pVar y)))) =>
	        match string_dec x y with
	          | true => @Solved _ _ _ s
	          | false => @Fail _ _ _
			end
      | App (App (Inj (inr (ilf_impl tyProp))) (App (App (Inj (inl (inr (pEq tyVar)))) (Inj (inl (inr (pVar x))))) (Inj (inl (inr (pVar y)))))) (Inj (inr (ilf_false tyProp))) =>
	        match string_dec x y with
	          | true => @Fail _ _ _
	          | false => @Solved _ _ _ s
			end
      | _ => More tus tvs s e
   end.

Open Scope string.

Definition test_eq :=
	let vars := nil in
	let goal := mkeq tyVar (fVar "a") (fVar "a")
	in
	@eq_solve nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_eq.

Definition test_neq :=
	let vars := nil in
	let goal := mkneq tyVar (fVar "a") (fVar "b")
	in
	@eq_solve nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_neq.