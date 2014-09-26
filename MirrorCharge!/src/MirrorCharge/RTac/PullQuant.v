Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.syms.SymSum.

Require Import MirrorCharge.AutoSetoidRewrite.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BaseFunc.

Require Import Charge.Logics.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Section ILPullQuant.
  Context {typ func : Type}.

  Context {RType_typ : RType typ} {RelDec_typ_eq : RelDec (@eq typ)}
          {RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq}.
          
  Context {RelDec_func_eq : RelDec (@eq (expr typ func))}.

  Context {HIL : ILogicFunc typ func}.
  Context {HB : BaseFunc typ func}.

  Variable inhabited : typ -> bool.  
  Variable inhabited_sound : forall t, inhabited t = true -> Inhabited (typD t).

Let Rbase := expr typ func.

Definition m (T : Type) : Type :=
  rsubst Rbase -> option (T * rsubst Rbase).

Definition rg_bind {T U} (a : m T) (b : T -> m U) : m U :=
  fun s => match a s with
             | None => None
             | Some (val,s') => b val s'
           end.
Definition rg_fail {T} : m T := fun _ => None.
Definition rg_ret {T} (v : T) : m T := fun s => Some (v, s).
Definition rg_plus {T} (l r : m T) : m T :=
  fun s =>
    let v := l s in
    match v with
      | None => r s
      | Some _ => v
    end.

Definition match_plus_l (e : expr typ func) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App b P)) Q =>
      let P := beta (App P (Var 0)) in
      let Q := lift 0 1 Q in
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	| Some (ilf_and _), Some (ilf_exists t l) =>
	      rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	        (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	        (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
      	| Some (ilf_or _), Some (ilf_exists t l) =>
      	  let rewrite_rl :=
	        rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		      (fun _ => rg_ret (mkExists t l (mkOr l P Q))) in
			if inhabited t then
		      rg_plus 
		        rewrite_rl 
		        (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
		          (fun _ => rg_ret (mkExists t l (mkOr l P Q))))
		    else
		      rewrite_rl
	    | _, _ => rg_fail
	  end
	| _ => rg_fail
  end.
  
Definition match_plus_r (e : expr typ func) (rg : RG Rbase) : m (expr typ func) :=
  match e with
   | App (App a P) (App b Q) =>
   	 let P := lift 0 1 P in
   	 let Q := beta (App Q (Var 0)) in
     match ilogicS a, ilogicS b with
       | Some (ilf_and _), Some (ilf_exists t l) =>
	      rg_plus
	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
	            (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
  	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	            (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
       | Some (ilf_or _), Some (ilf_exists t l) =>
         let rewrite_rl := 
		   rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		     (fun _ => rg_ret (mkExists t l (mkOr l P Q))) in
		   if inhabited t then
		     rg_plus
		       rewrite_rl
		       (rg_bind (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
		         (fun _ => rg_ret (mkExists t l (mkOr t P Q))))
		   else
		     rewrite_rl
	   | _, _ => rg_fail
	 end
   | _ => rg_fail
 end.

Definition rewrite_exs (e : (expr typ func)) (_ : list (RG (expr typ func))) (rg : RG (expr typ func)) : m (expr typ func) :=
  rg_plus (match_plus_l e rg) (match_plus_r e rg).

Definition rewrite_respects (e : Rbase) (_ : list (RG Rbase))
	 (rg : RG Rbase) : m (expr typ func) :=
	match ilogicS (func := expr typ func) e with
		| Some (ilf_and l) => 
			rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			        (RGrespects (RGinj (fEntails l)) 
			        (RGrespects (RGinj (fEntails l)) 
			        (RGinj (fEntails l)))))
				(fun _ => rg_ret (fAnd l))
		| Some (ilf_or l) => 
			rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			        (RGrespects (RGinj (fEntails l)) 
			        (RGrespects (RGinj (fEntails l))
			        (RGinj (fEntails l)))))
				(fun _ => rg_ret (fOr l))
		| Some (ilf_impl l) => 
			rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			                 (RGrespects (RGflip (RGinj (fEntails l))) 
			                 (RGrespects (RGinj (fEntails l)) 
			                 (RGinj (fEntails l)))))
				(fun _ => rg_ret (fImpl l))
		| Some (ilf_exists t l) => 
			rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			                 (RGrespects (RGrespects (RGinj (fEq t))
						                             (RGinj (fEntails l)))
						                 (RGinj (fEntails l))))
						                 
				(fun _ => rg_ret (fExists t l))
		| Some (ilf_true l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
				(fun _ => rg_ret (fTrue l))
		| _ => rg_fail
	end.
		
Definition rw_type := expr typ func -> list (RG (expr typ func))
                      -> RG (expr typ func) -> m (expr typ func).

Section interleave.
  Variables (rw rw' : rw_type -> rw_type).

  Fixpoint interleave (n : nat)
           (e : expr typ func) (rvars : list (RG (expr typ func)))
           (rg : RG (expr typ func)) : m (expr typ func) :=
    match n with
      | 0 => rg_fail
      | S n => rw (fun rs => rw' (fun e rvars rg rs => interleave n e rvars rg rs) rs) e rvars rg
    end.
End interleave.

Fixpoint rw_fix (n : nat)
  (rw : rw_type -> rw_type)
  (e : expr typ func) (rvars : list (RG Rbase)) (rg : RG Rbase)
  (rs : rsubst Rbase)
: option (expr typ func * rsubst Rbase) :=
  match n with
    | 0 => Some (e,rs)
    | S n => rw (fun e rvars rg rs => rw_fix n rw e rvars rg rs) e rvars rg rs
  end.

Definition quant_pull (l : typ) (e : expr typ func) : expr typ func :=
  match
    rw_fix 500 (@setoid_rewrite typ func (expr typ func)
                     rel_dec
                     rewrite_exs rewrite_respects)
      e nil (RGinj (fEntails (func := expr typ func) l))
      (rsubst_empty _)
  with
    | None => e
    | Some (e,_) => e
  end.
  
End ILPullQuant.