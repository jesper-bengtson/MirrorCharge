Require Import ILogic ILInsts.
Require Import ILogicFunc.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MapPositive.
Require Import MirrorCore.SymI.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Data.Positive.
Require Import Ext.ExprLift.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import MirrorCore.EnvI.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import Ext.SetoidFold.
Require Import Relation_Definitions.
Require Import MirrorCore.Ext.AppFull.
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

	Definition pull_exists := @app_fold (option (list typ * expr ilfunc)) pq_var pq_uvar pq_inj pq_abs (pq_app slspec) pq_exists pq_forall.

	Definition qcancel (tus tvs : tenv typ) (P Q : expr ilfunc) : option (expr ilfunc * expr ilfunc * subst) :=
	    match pull_exists Q tus tvs with
	    	| Some (xs, Q') => 
	    	    let P' := lift_uvars (length tus) (length xs) P in
	    		let Q'' := vars_to_uvars (length tus) 0 (length xs) Q' in
	    		Some (@the_canceller ts ilfunc _ ltyp synsl slspec (tus++xs) tvs P' Q'' (FMapSubst.SUBST.subst_empty _))
	    	| None => None
	    end.
	    
	   (* 
	    P 5 ** Q |-- Q ** exists y, P y.
	*)
End QuantCancel.
	