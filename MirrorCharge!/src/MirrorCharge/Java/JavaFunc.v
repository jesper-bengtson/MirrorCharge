Require Import Charge.Open.Subst.
Require Import Charge.Open.Open.
Require Import Charge.Open.Stack.
Require Import Charge.Logics.BILogic.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Sum.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Lang.
Require Import Java.Language.Program.
Require Import Java.Semantics.OperationalSemantics.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.LaterFunc.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ListFunc.
Require Import MirrorCharge.ModularFunc.OpenFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Set Implicit Arguments.
Set Strict Implicit.


	Inductive java_func :=
	| pField (_ : field)
	| pClass (_ : class)
	| pVal (_ : val)
	| pVarList (_ : list var) 
	| pProg (_ : Program)
	| pCmd (_ : cmd)
	| pDExpr (_ : dexpr)
	| pFields (_ : list field)
	
	| pMethodSpec
	| pProgEq
	| pTriple
	| pTypeOf
	| pFieldLookup
	
	| pPointsto
	| pNull
	
	| pPlus
	| pMinus
	| pTimes
	| pAnd
	| pOr
	| pNot
	| pLt
	| pValEq.

	Fixpoint beq_list {A} (f : A -> A -> bool) (xs ys : list A) :=
		match xs, ys with
			| nil, nil => true
			| x::xs, y :: ys => andb (f x y) (beq_list f xs ys)
			| _, _ => false
		end.

	Definition typeof_java_func bf :=
		match bf with
		    | pField _ => Some tyField
		    | pClass _ => Some tyClass
		    | pVal _ => Some tyVal
		    | pVarList _ => Some tyVarList
		    | pProg _ => Some tyProg
		    | pCmd _ => Some tyCmd
		    | pDExpr _ => Some tyDExpr
		    | pFields _ => Some tyFields
		
		    | pMethodSpec => Some (tyArr tyClass (tyArr tyString (tyArr tyVarList
		    	 (tyArr tyVar (tyArr tySasn (tyArr tySasn tySpec))))))
		    | pProgEq => Some (tyArr tyProg tySpec)
		    | pTriple => Some (tyArr tySasn (tyArr tySasn (tyArr tyCmd tySpec)))
		    
		    | pTypeOf => Some (tyArr tyClass (tyArr tyVal tyProp))
		    
		    | pFieldLookup => Some (tyArr tyProg (tyArr tyClass (tyArr tyFields tyProp)))
		    
		    | pPointsto => Some (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn)))
		    
		    | pNull => Some tyVal
		    
		    | pPlus => Some (tyArr tyVal (tyArr tyVal tyVal))
		    | pMinus => Some (tyArr tyVal (tyArr tyVal tyVal))
		    | pTimes => Some (tyArr tyVal (tyArr tyVal tyVal))
		    | pAnd => Some (tyArr tyVal (tyArr tyVal tyVal))
		    | pOr => Some (tyArr tyVal (tyArr tyVal tyVal))
		    | pNot => Some (tyArr tyVal tyVal)
		    | pLt => Some (tyArr tyVal (tyArr tyVal tyVal))
		    | pValEq => Some (tyArr tyVal (tyArr tyVal tyVal))
		end.

	Definition java_func_eq (a b : java_func) : option bool :=
	  match a , b with
	    | pField a, pField b => Some (a ?[ eq ] b)
	    | pClass a, pClass b => Some (a ?[ eq ] b)
		| pVal a, pVal b => Some (a ?[ eq ] b)
	    | pVarList a, pVarList b => Some (a ?[ eq ] b)
	    | pProg a, pProg b => Some (a ?[ eq ] b)
	    | pCmd a, pCmd b => Some (a ?[ eq ] b)
	    | pDExpr e1, pDExpr e2 => Some (e1 ?[ eq ] e2)
	    | pFields a, pFields b => Some (a ?[ eq ] b)
	        
	    | pMethodSpec, pMethodSpec => Some true
	    | pProgEq, pProgEq => Some true
		| pTriple, pTriple => Some true
	
	    | pTypeOf, pTypeOf => Some true
	
	    | pPointsto, pPointsto => Some true
	    | pFieldLookup, pFieldLookup => Some true
	
	    | pNull, pNull => Some true
	    | pPlus, pPlus => Some true
	    | pMinus, pMinus => Some true
	    | pTimes, pTimes => Some true
	    | pAnd, pAnd => Some true
	    | pOr, pOr => Some true
	    | pNot, pNot => Some true
	    | pLt, pLt => Some true
	    | pValEq, pValEq => Some true
	    | _, _ => None
	  end.

    Global Instance RelDec_java_func : RelDec (@eq java_func) := {
      rel_dec a b := match java_func_eq a b with 
    	  		       | Some b => b 
    		 	       | None => false 
    			     end
    }.

    Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_java_func.
    Proof.
      constructor.
      destruct x; destruct y; simpl;
      try solve [ try rewrite Bool.andb_true_iff ;
                  repeat rewrite rel_dec_correct; intuition congruence ].                  	
    Qed.

Definition set_fold_fun (x : String.string) (f : field) (P : sasn) :=
	(`pointsto) (x/V) `f `null ** P.
  
  	 Definition java_func_symD bf :=
		match bf as bf return match typeof_java_func bf with
								| Some t => typD t
								| None => unit
							  end with
              | pClass c => c
              | pField f => f
              | pProg p => p
              | pVal v => v
              | pVarList vs => vs
              | pCmd c => c
              | pDExpr e => e
              | pFields fs => fs

              | pMethodSpec => method_spec
              | pProgEq => prog_eq
              | pTriple => triple
              
              | pTypeOf => typeof
                            
              | pFieldLookup => field_lookup
              
              | pPointsto => pointsto
              
              | pNull => null
              
              | pPlus => eplus
              | pMinus => eminus
              | pTimes => etimes
              | pAnd => eand
              | pOr => eor
              | pNot => enot
              | pLt => elt
              | pValEq => eeq
	end.

	Global Instance RSym_JavaFunc : SymI.RSym java_func := {
	  typeof_sym := typeof_java_func;
	  symD := java_func_symD;
	  sym_eqb := java_func_eq
	}.

Print SymI.RSymOk.

	Global Instance RSymOk_JavaFunc : SymI.RSymOk RSym_JavaFunc.
	Proof.
		split; intros.
		destruct a, b; simpl; try apply I; try reflexivity.
		+ consider (f ?[ eq ] f0); intuition congruence.
		+ consider (c ?[ eq ] c0); intuition congruence.
		+ consider (v ?[ eq ] v0); intuition congruence.
		+ consider (l ?[ eq ] l0); intuition congruence.
		+ consider (p ?[ eq ] p0); intuition congruence. 
		+ consider (c ?[ eq ] c0); intuition congruence. 
		+ consider (d ?[ eq ] d0); intuition congruence. 
		+ consider (l ?[ eq ] l0); intuition congruence. 
	Qed.		

Definition func := (SymEnv.func + @ilfunc typ + @bilfunc typ + 
                    @base_func typ + @list_func typ + @open_func typ _ _ + 
                    @embed_func typ + @later_func typ + java_func)%type.

Section MakeJavaFunc.
	Definition mkField f : expr typ func := Inj (inr (pField f)).
	Definition mkClass c : expr typ func := Inj (inr (pClass c)).
	Definition mkVal v : expr typ func := Inj (inr (pVal v)).
	Definition mkVarList vs : expr typ func := Inj (inr (pVarList vs)).
	Definition mkProg P : expr typ func := Inj (inr (pProg P)).
	Definition mkCmd c : expr typ func := Inj (inr (pCmd c)).
	Definition mkDExpr e : expr typ func := Inj (inr (pDExpr e)).
	Definition mkFields fs : expr typ func := Inj (inr (pFields fs)).

	Definition fMethodSpec : expr typ func := Inj (inr pMethodSpec).
	Definition fProgEq : expr typ func := Inj (inr pProgEq).
	Definition fTriple : expr typ func := Inj (inr pTriple).
	Definition fTypeOf : expr typ func := Inj (inr pTypeOf).
	Definition fFieldLookup : expr typ func := Inj (inr pFieldLookup).
	Definition fPointsto : expr typ func := Inj (inr pPointsto).
	Definition mkNull : expr typ func := Inj (inr pNull).

	Definition fPlus : expr typ func := Inj (inr pPlus).
	Definition fMinus : expr typ func := Inj (inr pMinus).
	Definition fTimes : expr typ func := Inj (inr pTimes).
	Definition fAnd : expr typ func := Inj (inr pAnd).
	Definition fOr : expr typ func := Inj (inr pOr).
	Definition fNot : expr typ func := Inj (inr pNot).
	Definition fLt : expr typ func := Inj (inr pLt).
	Definition fValEq : expr typ func := Inj (inr pValEq).

	Definition mkTriple P c Q : expr typ func := App (App (App fTriple P) Q) c.
	Definition mkFieldLookup P C f : expr typ func := App (App (App fFieldLookup P) C) f.
	Definition mkTypeOf C x : expr typ func := App (App fTypeOf C) x.
	Definition mkProgEq P := App fProgEq P.
	
	Definition mkExprList es :=
		(fold_right (fun (e : dexpr) (acc : expr typ func) => 
			mkCons tyExpr (mkDExpr e) acc) (mkNil tyExpr) es).
	

	Fixpoint evalDExpr (e : dexpr) : expr typ func :=
		match e with
			| E_val v => mkConst tyVal (mkVal v)
			| E_var x => App (fStackGet (func := expr typ func)) (mkVar (func := func) x)
			| E_plus e1 e2 => mkAps fPlus ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
			| E_minus e1 e2 => mkAps fMinus ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
			| E_times e1 e2 => mkAps fTimes ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
			| E_and e1 e2 => mkAps fAnd ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
			| E_or e1 e2 => mkAps fOr ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
			| E_not e => mkAps fNot ((evalDExpr e, tyVal)::nil) tyVal
			| E_lt e1 e2 => mkAps fLt ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
			| E_eq e1 e2 => mkAps fValEq ((evalDExpr e2, tyVal)::(evalDExpr e1, tyVal)::nil) tyVal
		end.

End MakeJavaFunc.

Require Import Java.Examples.ListModel.

(* This needs to be parametric. It shouldn't be here *)
Definition fs : @SymEnv.functions typ _ :=
  SymEnv.from_list
  	(@SymEnv.F typ _ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) List::
  	 @SymEnv.F typ _ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) NodeList::nil). 

(*Definition fs : @SymEnv.functions typ _ := SymEnv.from_list nil.
*)
Locate RSym_func.
Instance RSym_env : RSym SymEnv.func := RSym_func fs.

Print RSymOk.

Instance RSym_ilfunc : RSym (@ilfunc typ) := 
	RSym_ilfunc _ _ ilops.
Instance RSym_bilfunc : RSym (@bilfunc typ) := 
	RSym_bilfunc _ bilops.
Instance RSym_embed_func : RSym (@embed_func typ) :=
	RSym_embed_func _ eops.
Instance RSym_later_func : RSym (@later_func typ) :=
	RSym_later_func _ lops.

Instance RSym_open_func : RSym (@open_func typ _ _) :=
	@RSym_OpenFunc _ _ _ RType_typ _ _ _ _ _ _ _ _.

Existing Instance RSym_sum.
Existing Instance RSymOk_sum.

Instance RelDec_expr : RelDec (@eq func) := _.

Instance Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
Instance Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := ExprOk_expr.

Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Lambda.ExprVariables.

Instance ExprVar_expr : ExprVar (expr typ func) := _.
Instance ExprVarOk_expr : ExprVarOk ExprVar_expr := _.

Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
  (*
Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
  FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ _ _ _ func). 
Instance SO : SubstI.SubstOk SS := 
  @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _ _.
*)

Instance MA : MentionsAny (expr typ func) := {
  mentionsAny := ExprCore.mentionsAny
}.

Instance MAOk : MentionsAnyOk MA _ _.
Proof.
  admit.
Qed.

Lemma evalDexpr_wt (e : dexpr) : 
	typeof_expr nil nil (evalDExpr e) = Some tyExpr. 
Proof.
  induction e.
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
  + simpl; rewrite IHe; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
  + simpl; rewrite IHe1, IHe2; reflexivity.
Qed.

Definition is_pure (e : expr typ func) : bool :=
	match e with
		| App f P => match embedS f with
					     | Some (eilf_embed tyPure tySasn) => true
					     | Some (eilf_embed tyProp tySasn) => true
					     | _ => false
					 end 
		| _ => false
	end.

Definition test_lemma :=
  @lemmaD typ (expr typ func) RType_typ Expr_expr (expr typ func)
          (fun tus tvs e => exprD' tus tvs tyProp e)
          _
          nil nil.

(*

Definition myTest : expr typ func := mkStar tySasn (mkEmp tySasn) (mkTrue tySasn).
Check @exprD'.
Check exprD' nil nil tySasn myTest.
Eval cbv [exprD' ExprI.exprT exprT_GetVAs funcAs ExprI.exprT_Inj exprD'_simul
          typ2_match type_cast] in exprD' nil nil tySasn myTest.

Require Import Relations.Relation_Definitions.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.OpenT.

Eval vm_compute in myTest.
Lemma test : exists t, t = exprD' nil nil tySasn 

         (Inj
            (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))).
Proof.
  Print exprD'.
  Print nth_error_get_hlist_nth.
  Print hlist_tl.
  simpl.
Print ilops.
Local Transparent ILInsts.ILFun_Ops.
pose (ilops tySasn).
cbv [ilops] in o.
simpl in o.
Print type_cast_typ.

  cbv [exprD' ExprI.exprT TypesI.typD exprT_GetVAs funcAs ExprI.exprT_Inj exprD'_simul
       typeof_sym RSym_sum RSym_ilfunc Rcast Relim Rsym eq_sym type_cast
       typeof_func ilops RType_typ type_cast type_cast_typ
       (* nth_error_get_hlist_nth Monad.bind OptionMonad.Monad_option type_cast
       hlist_hd eq_sym ExprI.exprT_UseU hlist_hd hlist_tl exprT_App OpenT RType_typ
       func_simul typeof_sym RSym_sum RSym_ilfunc Typ2_Fun
       *)
       ILogicFunc.funcD ILogicFunc.RSym_ilfunc ILogicFunc.typ2_cast_quant ILogicFunc.typ2_cast_bin].
exprD' nil nil tySasn 

         (Inj
            (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))).
    cbv [ilops].
    simpl.
	pose (ilops tySasn).

       simpl.
       
  cbv [exprD' ExprI.exprT exprT_GetVAs funcAs ExprI.exprT_Inj exprD'_simul
       typ2_match type_cast Monad.bind exprT_App Typ2_Fun BILogicFunc.typ2_cast_bin
       TypesI.typD OpenT typD OptionMonad.Monad_option nth_error_get_hlist_nth
       typeof_sym Monad.ret RSym_sum].
simpl.
unfold exprD'.
simpl.
unfold exprT_App.
simpl.
unfold ExprI.exprT_Inj. simpl.
unfold BILogicFunc.typ2_cast_bin.
simpl.
vm_compute.
*)