Require Import MirrorCore.Lambda.ExprCore.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.AutoSetoidRewrite.

Section ILSetoidRewrite.
	Context {typ func : Type} {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
	Context {RelDec_func : RelDec (@eq (expr typ func))}.

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
		 | Some (ilf_true l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
			 	(fun _ => rg_ret (fTrue l))
		 | _ => rg_fail
	 end.

End ILSetoidRewrite.