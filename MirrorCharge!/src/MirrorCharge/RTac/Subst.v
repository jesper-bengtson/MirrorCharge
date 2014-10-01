Require Import String.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.RedAll.

Require Import MirrorCharge.ModularFunc.OpenFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.LaterFunc.
Require Import MirrorCharge.ModularFunc.ListFunc.
Require Import MirrorCharge.ModularFunc.SubstType.

Set Implicit Arguments.
Set Strict Implicit.

Section ApplySubst.
	Context {typ func : Type} {RType_typ : RType typ} {ST : SubstType typ}
	        {HOF : OpenFunc typ func} {HLF : ListFunc typ func}.
	Context {RelDec_typ : RelDec (@eq typ)}.
	Context {RelDec_var : RelDec (@eq (typD tyVar))}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

	Definition applySingleSubst (p : expr typ func) (x y : typD tyVar) e :=
		if x ?[ eq ] y then e else p.
		    	
    Fixpoint applyParSubst (p : expr typ func) (x : typD tyVar) vs es :=
    	match es with
    		| App (App f e) es =>
    			match vs, listS f with
    				| v :: vs, Some (pCons t) =>
    					if t ?[ eq ] tyArr tyVar tyVal then
    						if x ?[ eq ] v then
    							e
    						else
    							applyParSubst p x vs es
    					else
    						p
    				| _, _ => p
    			end
    		| _ => p
    	end.
    						
    Fixpoint applyTruncSubst (p : expr typ func) (x : typD tyVar) vs es :=
    	match es with
    		| App (App f e) es =>
    			match vs, listS f with
    				| v :: vs, Some (pCons t) =>
    					if t ?[ eq ] tyArr tyVar tyVal then
    						if x ?[ eq ] v then
    							e
    						else
    							applyParSubst p x vs es
    					else
    						fNull
    				| _, _ => fNull
    			end
    		| _ => fNull
    	end.				

	Definition applySubst (t : typ) (f e : expr typ func) (x : typD tyVar) :=
		match f with
		  | App (App g e') y =>
		  	match open_funcS g, open_funcS y with
		  	  | Some (of_singleSubst), Some (of_var v) => applySingleSubst e x v e'
		  	  | _, _ => mkApplySubst t e f
		  	end
		  | _ => mkApplySubst t e f
(*		  | mkApplySubst [t, p, mkSubstList [mkVarList [vs], es]] => applyParSubst p x vs es
		  | mkApplyTruncSubst [t, p, mkSubstList [mkVarList [vs], es]] => applyTruncSubst x vs es*)
		end.

End ApplySubst.

Section PushSubst.
  Context {typ func : Type} {ST : SubstType typ} {RType_typ : RType typ}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func}.
  Context {RelDec_var : RelDec (@eq (typD tyVar))}.
  
  Variable Typ2_tyArr : Typ2 _ Fun.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable f : expr typ func.

  Fixpoint pushSubst (e : expr typ func) (t : typ) : expr typ func :=
    match e with
    	| App (App g p) q =>
    		match ilogicS g with
    			| Some (ilf_and l) => mkAnd l (pushSubst p l) (pushSubst q l)
    			| Some (ilf_or l) => mkOr l (pushSubst p l) (pushSubst q l)
    			| Some (ilf_impl l) => mkImpl l (pushSubst p l) (pushSubst q l)
    			| _ => match open_funcS g with
		    			 | Some (of_ap t1 t2) => mkAp t1 t2 (pushSubst p (tyArr t1 t2))
		    			             									 (pushSubst q t2)
		    			 | _ => match bilogicS g with
		    			          | Some (bilf_star l) => mkStar l (pushSubst p l) (pushSubst q l)
		    			          | Some (bilf_wand l) => mkWand l (pushSubst p l) (pushSubst q l)
		    			 	      | _ => mkApplySubst t e f
		    			 	    end
		    		   end
    		end
    	| App g x =>
    		match open_funcS g, open_funcS x with
    			| Some of_stack_get, Some (of_var y) => applySubst t f e y
    			| Some (of_const _), _ => e
    			| _, _ => mkApplySubst t e f
    		end
    	| _ => match ilogicS e with
    		     | Some (ilf_true l) => mkTrue l
    		     | Some (ilf_false l) => mkFalse l
    		     | _ => match bilogicS e with
    		     		  | Some (bilf_emp l) => mkEmp l
    		     		  | _ => mkApplySubst t e f
    		     		end
    		   end
    end.
    
End PushSubst.

Section SubstTac.
  Context {typ func subst : Type} {ST : SubstType typ} {RType_typ : RType typ}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func}.
  Context {RelDec_var : RelDec (@eq (typD tyVar))}.
  
  Variable Typ2_tyArr : Typ2 _ Fun.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

	Definition substTac (e : expr typ func) (args : list (expr typ func))
	: expr typ func :=
	  match open_funcS e with
	    | Some (of_apply_subst t) =>
	      match args with
	        | e :: f :: nil =>
	          pushSubst Typ2_tyArr f e t
	        | _ => apps e args
	      end
	    | _ => apps e args
	  end.

	Definition SUBST := SIMPLIFY (typ := typ) (subst := subst) (fun _ _ => beta_all substTac nil nil).

End SubstTac.

Implicit Arguments SUBST [[ST] [RType_typ] [OF] [ILF] [BILF] [RelDec_var] [Typ2_tyArr]].
