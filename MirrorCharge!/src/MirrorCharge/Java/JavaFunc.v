Require Import Charge.Open.Subst.
Require Import Charge.Open.Open.
Require Import Charge.Open.Stack.
Require Import Charge.Logics.BILogic.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
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

Class JavaFunc func := {
	fVar : var -> func;
	fField : field -> func;
	fClass : class -> func;
	fVal : sval -> func;
	fVarList : list var -> func;
	fProg : Prog_wf -> func;
	fCmd : cmd -> func;
	fDExpr : dexpr -> func;
	fFields : SS.t -> func;
	fMethodSpec : func;
	fProgEq : func;
	fTriple : func;
	fTypeOf : func;
	fEval : func;
	fFieldLookup : func;
	fSetFold : typ -> func;
	fSetFoldFun : func;
	fPointsto : func;
	fNull : func
}.

Section JavaFuncSum.
	Context {func : Type} {H : JavaFunc func}.

	Global Instance JavaFuncSumL (A : Type) : 
		JavaFunc (func + A) := {
			fVar v := inl (fVar v);
			fField f := inl (fField f);
			fClass c := inl (fClass c);
			fVal v := inl (fVal v);
			fVarList vs := inl (fVarList vs);
			fProg P := inl (fProg P);
			fCmd c := inl (fCmd c);
			fDExpr e := inl (fDExpr e);
			fFields fs := inl (fFields fs);
			fMethodSpec := inl fMethodSpec;
			fProgEq := inl fProgEq;
			fTriple := inl fTriple;
			fTypeOf := inl fTypeOf;
			fEval := inl fEval;
			fFieldLookup := inl fFieldLookup;
			fSetFold t := inl (fSetFold t);
			fSetFoldFun := inl fSetFoldFun;
			fPointsto := inl fPointsto;
			fNull := inl fNull
		}.

	Global Instance JavaFuncSumR (A : Type) : 
		JavaFunc (A + func) := {
			fVar v := inr (fVar v);
			fField f := inr (fField f);
			fClass c := inr (fClass c);
			fVal v := inr (fVal v);
			fVarList vs := inr (fVarList vs);
			fProg P := inr (fProg P);
			fCmd c := inr (fCmd c);
			fDExpr e := inr (fDExpr e);
			fFields fs := inr (fFields fs);
			fMethodSpec := inr fMethodSpec;
			fProgEq := inr fProgEq;
			fTriple := inr fTriple;
			fTypeOf := inr fTypeOf;
			fEval := inr fEval;
			fFieldLookup := inr fFieldLookup;
			fSetFold t := inr (fSetFold t);
			fSetFoldFun := inr fSetFoldFun;
			fPointsto := inr fPointsto;
			fNull := inr fNull
		}.
		
	Global Instance JavaFuncExpr : 
		JavaFunc (expr typ func) := {
			fVar v := Inj (fVar v);
			fField f := Inj (fField f);
			fClass c := Inj (fClass c);
			fVal v := Inj (fVal v);
			fVarList vs := Inj (fVarList vs);
			fProg P := Inj (fProg P);
			fCmd c := Inj (fCmd c);
			fDExpr e := Inj (fDExpr e);
			fFields fs := Inj (fFields fs);
			fMethodSpec := Inj fMethodSpec;
			fProgEq := Inj fProgEq;
			fTriple := Inj fTriple;
			fTypeOf := Inj fTypeOf;
			fEval := Inj fEval;
			fFieldLookup := Inj fFieldLookup;
			fSetFold t := Inj (fSetFold t);
			fSetFoldFun := Inj fSetFoldFun;
			fPointsto := Inj fPointsto;
			fNull := Inj fNull
		}.

End JavaFuncSum.
	
Section JavaFuncInst.
	Context {func : Type} {H : JavaFunc func}.

	Inductive java_func :=
	| pVar (_ : var)
	| pField (_ : field)
	| pClass (_ : class)
	| pVal (_ : sval)
	| pVarList (_ : list var) 
	| pProg (_ : Prog_wf)
	| pCmd (_ : cmd)
	| pDExpr (_ : dexpr)
	| pFields (_ : SS.t)
	
	| pMethodSpec
	| pProgEq
	| pTriple
	| pTypeOf
	| pEval
	| pFieldLookup
	
	| pSetFold (_ : typ)
	| pSetFoldFun 
	
	| pPointsto
	| pNull.

	Global Instance JavaFuncInst : JavaFunc java_func := {
		fVar := pVar;
		fField := pField;
		fClass := pClass;
		fVal := pVal;
		fVarList := pVarList;
		fProg := pProg;
		fCmd := pCmd;
		fDExpr := pDExpr;
		fFields := pFields;
		fMethodSpec := pMethodSpec;
		fProgEq := pProgEq;
		fTriple := pTriple;
		fTypeOf := pTypeOf;
		fEval := pEval;
		fFieldLookup := pFieldLookup;
		fSetFold := pSetFold;
		fSetFoldFun := pSetFoldFun;
		fPointsto := pPointsto;
		fNull := pNull
	}.

	Fixpoint beq_list {A} (f : A -> A -> bool) (xs ys : list A) :=
		match xs, ys with
			| nil, nil => true
			| x::xs, y :: ys => andb (f x y) (beq_list f xs ys)
			| _, _ => false
		end.

	Definition typeof_java_func bf :=
		match bf with
		    | pVar _ => Some tyVar
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
		    | pEval => Some (tyArr tyDExpr tyExpr)
		    
		    | pTypeOf => Some (tyArr tyVar (tyArr tyVal tyProp))
		    
		    | pFieldLookup => Some (tyArr tyProg (tyArr tyClass (tyArr tyFields tyProp)))
		    
		    | pSetFoldFun => Some (tyArr tyString (tyArr tyString (tyArr tySasn tySasn)))
		    | pSetFold t => Some (tyArr (tyArr tyString (tyArr t t)) (tyArr tyFields (tyArr t t)))
		    
		    | pPointsto => Some (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn)))
		    
		    | pNull => Some tyVal
		end.

	Definition java_func_eq (a b : java_func) : option bool :=
	  match a , b with
	    | pVar a, pVar b => Some (a ?[ eq ] b)
	    | pField a, pField b => Some (a ?[ eq ] b)
	    | pClass a, pClass b => Some (a ?[ eq ] b)
		| pVal a, pVal b => Some (beq_val a b)
	    | pVarList a, pVarList b => Some (beq_list beq_string a b)
	    | pProg a, pProg b => Some true (* THIS IS FALSE! We need an equivalence checker for programs. This should just be syntactic equality. *)
	    | pCmd a, pCmd b => Some (beq_cmd a b)
	    | pDExpr e1, pDExpr e2 => Some (beq_dexpr e1 e2)
	    | pFields a, pFields b => Some (SS.equal a b)
	        
	    | pMethodSpec, pMethodSpec => Some true
	    | pProgEq, pProgEq => Some true
		| pTriple, pTriple => Some true
	
	    | pTypeOf, pTypeOf => Some true
	
		| pEval, pEval => Some true
	
	    | pPointsto, pPointsto => Some true
	    | pFieldLookup, pFieldLookup => Some true
	    | pSetFold t, pSetFold u => Some (t ?[ eq ] u)
	    | pSetFoldFun, pSetFoldFun => Some true
	
	    | pNull, pNull => Some true
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
                  repeat rewrite rel_dec_correct; intuition congruence ];
                  	admit.
    Qed.
  
Definition set_fold_fun (x : String.string) (f : field) (P : sasn) :=
	(`pointsto) (x/V) `f `null ** P.
  
  	 Definition java_func_symD bf :=
		match bf as bf return match typeof_java_func bf with
								| Some t => typD t
								| None => unit
							  end with
              | pVar v => v
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
              | pEval => eval
              
              | pTypeOf => typeof
                            
              | pFieldLookup => field_lookup
              | pSetFold t => @SS.fold (typD t)
              | pSetFoldFun => set_fold_fun
              
              | pPointsto => pointsto
              
              | pNull => null
	end.

	Global Instance RSym_JavaFunc : SymI.RSym java_func := {
	  typeof_sym := typeof_java_func;
	  symD := java_func_symD;
	  sym_eqb := java_func_eq
	}.

	Global Instance RSymOk_JavaFunc : SymI.RSymOk RSym_JavaFunc.
	Proof.
		admit.

		(*
		split; intros.
		destruct a, b; simpl; try apply I.
		+ consider (v ?[ eq ] v0); intuition congruence.
		+ consider (f ?[ eq ] f0); intuition congruence.
		+ consider (c ?[ eq ] c0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; 
		  intuition congruence.
*)
	Qed.

End JavaFuncInst.

Section MakeJavaFunc.
	Context {func : Type} {H : JavaFunc func} {HT : ListFunc typ func}.

	Definition mkTriple P c Q := App (App (App fTriple P) Q) c.
	Definition mkFieldLookup P C f := App (App (App fFieldLookup P) C) f.
	Definition mkSetFold t x f P:= (App (App (App (fSetFold t) (App fSetFoldFun x)) f) P). 
	Definition mkTypeOf C x := App (App fTypeOf C) x.
	Definition mkVal v : expr typ func := Inj (fVal v).
	Definition mkField f : expr typ func := Inj (fField f).
	Definition mkVar f : expr typ func := Inj (fVar f).
	Definition mkClass c : expr typ func := Inj (fClass c).
	Definition mkVarList vs : expr typ func := Inj (fVarList vs).
	Definition mkProg P : expr typ func := Inj (fProg P).
	Definition mkCmd c : expr typ func := Inj (fCmd c).
	Definition mkDExpr e : expr typ func := Inj (fDExpr e).
	Definition mkFields fs : expr typ func := Inj (fFields fs).
	Definition mkProgEq P := App fProgEq P.
	
	Definition mkExprList es :=
		(fold_right (fun (e : dexpr) (acc : expr typ func) => 
			mkCons tyExpr (mkDExpr e) acc) (mkNil tyExpr) es).
	
	Definition mkEval e s := App (App fEval e) s.
	
	Definition mkNull : expr typ func := fNull.

End MakeJavaFunc.

Definition func := (SymEnv.func + @ilfunc typ + @bilfunc typ + 
                    @base_func typ + @list_func typ + @open_func typ + 
                    @embed_func typ + @later_func typ + java_func)%type.

Example test : expr typ func := mkStar tySasn (mkFalse tySasn) (mkTrue tySasn).

Eval vm_compute in test.

Print RSym.

Definition fs : @SymEnv.functions typ _ := SymEnv.from_list nil.
Locate RSym_func.
Instance RSym_env : RSym SymEnv.func := RSym_func fs.

Instance RSym_ilfunc : RSym (@ilfunc typ) := 
	RSym_ilfunc _ _ ilops.
Instance RSym_bilfunc : RSym (@bilfunc typ) := 
	RSym_bilfunc _ bilops.
Instance RSym_embed_func : RSym (@embed_func typ) :=
	RSym_embed_func _ eops.
Instance RSym_later_func : RSym (@later_func typ) :=
	RSym_later_func _ lops.
	Check null.
Instance RSym_open_func : RSym (@open_func typ) :=
	@RSym_OpenFunc _ _ _ RType_typ _ _ tyVar tyVal _ null _ _ _ _.

Existing Instance RSym_sum.
Existing Instance RSymOk_sum.

Instance Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
Instance Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := ExprOk_expr.

Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
  FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ func).
Instance SO : SubstI.SubstOk Expr_expr SS := 
  @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _ _.

Definition test_lemma :=
  @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
          (fun tus tvs e => exprD' tus tvs tyProp e)
          tyProp
          (fun x => x) nil nil.