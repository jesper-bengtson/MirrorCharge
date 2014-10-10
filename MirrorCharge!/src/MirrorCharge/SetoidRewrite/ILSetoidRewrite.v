Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.AutoSetoidRewrite.

Require Import Charge.Logics.ILogic.

Section ILSetoidRewrite.
	Context {typ func : Type} {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
	Context {RelDec_func : RelDec (@eq (expr typ func))} {RType_typ : RType typ}.
	Context {ilogic : forall t : typ, option (ILogicOps (typD t))}.
	Context {HT : Typ2 RType_typ Fun}.
	Context {RSym_func : RSym func}.
	
	Let Rbase := expr typ func.

  Definition il_respects (e : Rbase) (_ : list (RG Rbase))
	   (rg : RG Rbase) : m (expr typ func) :=
	   match ilogicS (typ := typ) (func := expr typ func) e with
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
(*		 | Some (ilf_true l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
			 	(fun _ => rg_ret (fTrue l))
		 | Some (ilf_false l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
			 	(fun _ => rg_ret (fFalse l))*)
		 | _ => rg_fail
	 end.

  Definition il_respects_reflexive (e : Rbase) (_ : list (RG Rbase))
	   (rg : RG Rbase) : m (expr typ func) :=
  	match typeof_expr nil nil e with
      | Some t => match ilogic t with
  				    | Some _ => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails t)))
								 	(fun _ => rg_ret e)
  				    | None => rg_fail
  				  end
  	  | None => rg_fail
  	end.
(*
	   rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	   	 (fun _ => rg_ret e).

  Definition il_respects_reflexive := fold_right (fun t acc => sr_combine (il_respects_reflexive_aux t) acc) 
  	(fun _ _ _ => rg_fail).
*)
End ILSetoidRewrite.

Implicit Arguments il_respects_reflexive [[typ] [func] [HIL] [RelDec_func] [RType_typ] [HT] [RSym_func]].