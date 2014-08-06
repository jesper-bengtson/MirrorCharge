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
Require Import MirrorCore.Subst.FMapSubst.
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
Require Import MirrorCharge.Java.MapTactics.

Require Import Java.Language.Lang.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Definition method_lookup_lemma : lemma typ (expr typ func) (expr typ func) :=
	{| vars := tySMap tyClass :: tyString :: tyString :: tyMethod :: tySSet :: tyClass :: nil
	 ; premises := mkMapsTo tyClass (Var 1) (mkBuildClass (Var 4) (Var 5)) (Var 0) :: nil
	               mkMapsTo tyMethod (Var 2) (Var 3) (Var 5)::nil
	 ; concl := mkMethodLookup (mkBuildProgram (Var 0)) (Var 1) (Var 2) (Var 3)
	|}.

Definition program_cases : stac typ (expr typ func) subst :=
  REC 5 (fun rec =>
            let rec := rec in
            REPEAT 10
                   (FIRST (eapply_other method_lookup_lemma rec::
                           map_cases tyClass ::
                           map_cases tyMethod :: 
                           nil)))
      (@FAIL _ _ _).
      
Open Scope string.      

Definition test_method_lookup :=
	let vars := nil in
	let goal := mkMethodLookup (mkBuildProgram (mkSingleton tyClass (fString "List") 
		(mkBuildClass mkSEmpty (mkSingleton tyMethod (fString "add") 
		             (mkBuildMethod (fNil tyVar) mkSkip (mkValToExpr (mkVal (vint (0%Z)))))))))
	    (fString "List") (fString "add")
		(mkBuildMethod (fNil tyVar) mkSkip (mkValToExpr (mkVal (vint (0%Z)))))
	in
	@program_cases nil vars (SubstI3.empty (expr := expr typ func)) goal.

Eval cbv in test_lemma method_lookup_lemma.

Time Eval cbv in lemmaD' _ _ _ nil nil method_lookup_lemma.
Time Eval cbv in test_method_lookup.
