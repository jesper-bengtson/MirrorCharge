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

Section ApplySubst.

	Definition applySingleSubst (p : expr typ func) x y e :=
		if string_dec x y then e else p.
		    	
    Fixpoint applyParSubst (p : expr typ func) x vs es :=
    	match vs, es with
    		| v :: vs, mkCons [tyExpr, e, es] =>
    			if string_dec x v then
    				e
    			else
    				applyParSubst p x vs es
    	    | _, _ => p
    	 end.

	Fixpoint applyTruncSubst x vs (es : expr typ func) :=
		match vs, es with
			| v :: vs, mkCons [tyExpr, e, es] =>
				if string_dec x v then
					e
				else
					applyTruncSubst x vs es 
			| _, _ => fNull
		end.

	Definition applySubst t (f e : expr typ func) (x : String.string) := 
		match f with
		  | mkApplySingleSubst [t, p, mkString [y], e] => applySingleSubst p x y e
(*		  | mkApplySubst [t, p, mkSubstList [mkVarList [vs], es]] => applyParSubst p x vs es
		  | mkApplyTruncSubst [t, p, mkSubstList [mkVarList [vs], es]] => applyTruncSubst x vs es*)
		  | _ => mkApplySubst [t, e, f]
		end.

End ApplySubst.

Section PushSubst.
  Variable f : expr typ func.

  Fixpoint pushSubst (e : expr typ func) (t : typ) : expr typ func :=
    match e with
    	| mkAnd [l, p, q] => mkAnd [l, pushSubst p t, pushSubst q t]
    	| mkOr [l, p, q] => mkOr [l, pushSubst p t, pushSubst q t]
    	| mkImpl [l, p, q] => mkImpl [l, pushSubst p t, pushSubst q t]
    	| mkTrue [l] => mkTrue [l]
    	| mkFalse [l] => mkFalse [l]
    	| mkAp [t1, t2, p, q] => mkAp [t1, t2, pushSubst p (tyArr t1 t2), pushSubst q t1]
    	| mkConst [l, p] => mkConst [l, p]
    	| App fstack_get (mkString [v]) => applySubst t f e v 
    	| _ => mkApplySubst [t, e, f]
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
        | f :: e :: nil =>
          pushSubst f e t
        | _ => apps e args
      end
    | _ => apps e args
  end.

