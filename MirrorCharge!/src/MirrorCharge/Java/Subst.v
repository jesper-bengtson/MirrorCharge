Require Import String.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.Java.Syntax.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Local Notation "a @ b" := (@App typ _ a b) (at level 30).
Local Notation "\ t -> e" := (@Abs typ _ t e) (at level 40).
Local Notation "'Ap' '[' x , y ']'" := (Inj (inl (inr (pAp x y)))) (at level 0).
Local Notation "'Const' '[' x ']'" := (Inj (inl (inr (pConst x)))) (at level 0).

Section ApplySubst.

	Definition applySingleSubst (p : expr typ func) x y e :=
		if string_dec x y then e else p.
		    	
    Fixpoint applyParSubst (p : expr typ func) x vs es :=
    	match vs, es with
    		| v :: vs, App (App (Inj (inl (inr (pCons tyExpr)))) e) es =>
    			if string_dec x v then
    				e
    			else
    				applyParSubst p x vs es
    	    | _, _ => p
    	 end.

	Fixpoint applyTruncSubst (x : String.string) (vs : list String.string) 
	                         (es : expr typ func) :=
		match vs, es with
			| v :: vs, App (App (Inj (inl (inr (pCons tyExpr)))) e) es =>
				if string_dec x v then
					e
				else
					applyTruncSubst x vs es 
			| _, _ => fNull
		end.
Print mkApplySingleSubst.
Print mkApplySubst.
Print mkSingleSubst.
	Definition applySubst (t : typ) (f e : expr typ func) (x : String.string) :=
		match f with
		  | App (App (Inj (inl (inr (pApplySubst t)))) P) 
		             (App (App (Inj (inl (inr pSingleSubst))) (Inj (inl (inr (pString y))))) e) =>
			applySingleSubst P x y e
(*		  | mkApplySubst [t, p, mkSubstList [mkVarList [vs], es]] => applyParSubst p x vs es
		  | mkApplyTruncSubst [t, p, mkSubstList [mkVarList [vs], es]] => applyTruncSubst x vs es*)
		  | _ => mkApplySubst t e f
		end.

End ApplySubst.

Section PushSubst.
  Variable f : expr typ func.

  Fixpoint pushSubst (e : expr typ func) (t : typ) : expr typ func :=
    match e with
    	| App (App (Inj (inr (ilf_and l))) p) q => mkAnd l (pushSubst p t) (pushSubst q t)
    	| App (App (Inj (inr (ilf_or l))) p) q => mkOr l (pushSubst p t) (pushSubst q t)
    	| App (App (Inj (inr (ilf_impl l))) p) q => mkImpl l (pushSubst p t) (pushSubst q t)
    	| Inj (inr (ilf_true l)) => mkTrue l
    	| Inj (inr (ilf_false l)) => mkFalse l
    	| App (App (Ap [t1, t2]) p) q => mkAp t1 t2 (pushSubst p (tyArr t1 t2)) (pushSubst q t1)
    	| App (Const [l]) p => mkConst l p
    	| App fstack_get (Inj (inl (inr (pString v)))) => applySubst t f e v 
    	| _ => mkApplySubst t e f
    end.
    
End PushSubst.

Definition simplify (e : expr typ func) (args : list (expr typ func))
: expr typ func :=
  match e with
    | Inj (inl (inr pEval)) =>
      match args with
        | App (Inj (inl (inr eVar))) X :: xs =>
          apps (App fStackGet X) xs
        | _ => apps e args
      end
    | Inj (inl (inr (pApplySubst t))) =>
      match args with
        | e :: f :: nil =>
          pushSubst f e t
        | _ => apps e args
      end
    | _ => apps e args
  end.

