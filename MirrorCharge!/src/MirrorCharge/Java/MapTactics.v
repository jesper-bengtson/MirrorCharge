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

Definition mapsto_singleton_lemma (t : typ) : lemma typ (expr typ func) (expr typ func) :=
	{| vars := tyString :: t :: nil
	 ; premises := nil
	 ; concl := mkMapsTo t (Var 0) (Var 1) (mkSingleton t (Var 0) (Var 1))
	|}. 
	
Definition mapsto_add1_lemma (t : typ) : lemma typ (expr typ func) (expr typ func) :=
	{| vars := tyString :: t :: tySMap t :: nil
	 ; premises := nil
	 ; concl := mkMapsTo t (Var 0) (Var 1) (mkAdd t (Var 0) (Var 1) (Var 2))
	|}.
	  
Definition mapsto_add2_lemma (t : typ) : lemma typ (expr typ func) (expr typ func) :=
	{| vars := tyString :: t :: tyString :: t :: tySMap t :: nil
	 ; premises := mkMapsTo t (Var 0) (Var 1) (Var 4) :: nil
	 ; concl := mkMapsTo t (Var 0) (Var 1) (mkAdd t (Var 2) (Var 3) (Var 4))
	|}.
	  
Definition map_cases t : stac typ (expr typ func) subst :=
  REC 5 (fun rec =>
            let rec := rec in
            REPEAT 10
                   (FIRST (eapply_other (mapsto_singleton_lemma t) rec ::
                           eapply_other (mapsto_add1_lemma t) rec ::
                           eapply_other (mapsto_add2_lemma t) rec
                           :: nil)))
      (@FAIL _ _ _).

Open Scope string.

Definition test_singleton :=
	let vars := nil in
	let goal := mkMapsTo tyVar (fString "a") (fVar "b") (mkSingleton tyVar (fString "a") (fVar "b"))
	in
	@map_cases tyVar nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_singleton.

Definition test_add1 :=
	let vars := nil in
	let goal := mkMapsTo tyVar (fString "a") (fVar "b") 
		(mkAdd tyVar (fString "a") (fVar "b") (mkSingleton tyVar (fString "b") (fVar "c")))
	in
	@map_cases tyVar nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_add1.

Definition test_add2 :=
	let vars := nil in
	let goal := mkMapsTo tyVar (fString "b") (fVar "c") 
		(mkAdd tyVar (fString "a") (fVar "b") (mkSingleton tyVar (fString "b") (fVar "c")))
	in
	@map_cases tyVar nil vars (SubstI3.empty (expr := expr typ func)) goal.

Time Eval vm_compute in test_add2.