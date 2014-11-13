Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.RTac.RTac.

Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.
Require Import MirrorCharge.Java.Reify.
Require Import MirrorCharge.ModularFunc.OpenFunc.
Require Import MirrorCharge.ModularFunc.ListFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.AutoSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.
Require Import MirrorCharge.RTac.Apply.

Require Import Java.Examples.ListModel.
Require Import Java.Examples.ListClass.
Require Import Java.Language.Lang.
Require Import Java.Logic.AssertionLogic.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.PullConjunct.ILPullConjunct.

Require Import MirrorCharge.Java.SymEx.

Set Printing Width 180.

Definition fList : expr typ JavaFunc.func := 
	Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))).
Definition fNode : expr typ JavaFunc.func := 
	Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))).

Definition mkList (p : var) (xs : expr typ JavaFunc.func) : expr typ JavaFunc.func:=
	 mkAps fList 
	 	((xs, tyList tyVal)::
	 	(((App (fStackGet (func := expr typ JavaFunc.func)) 
	 	(mkVar (func := JavaFunc.func) p)), tyVal)::nil)) tyAsn.

Definition mkNode (p xs : expr typ JavaFunc.func) :=
	 mkAps fNode 
	 	((xs, tyList tyVal)::
	 	(p, tyVal)::nil) tyAsn.

Definition apCons t (p : var) (xs : expr typ JavaFunc.func) :=
	mkAps (fCons (func := expr typ JavaFunc.func) tyVal)
	 	((xs, tyList t)::
	 	(((App (fStackGet (func := expr typ JavaFunc.func)) 
	 	(mkVar (func := JavaFunc.func) p)), tyVal)::nil)) (tyList t).

Definition rw_true (e : expr typ JavaFunc.func) 
	(rvars : list (RG (expr typ JavaFunc.func))) (rg : RG (expr typ JavaFunc.func)) :
 	m (expr typ JavaFunc.func) :=
  match e with
  	| App (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_and tySasn)))))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))))
         (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))) =>
         (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
          (fun _ => rg_ret (mkTrue tySasn)))
    | _ => rg_fail
  end.
  	  
(* List rewrite rule type checks *)

Eval vm_compute in typeof_expr nil nil (mkExists tyVal tySasn 
	(mkStar tySasn (mkPointstoVar "x" "head" (mkConst tyVal (Var 0))) 
		(mkNode (mkConst tyVal (Var 0)) (mkConst (tyList tyVal) (mkNil tyVal))))).

(* Unfold predicate for list *)

Definition test_op : expr typ JavaFunc.func :=
  ((App (Inj (inl (inl (inl (inr of_stack_get))))) 
  (Inj (inl (inl (inl (inr (of_var "p")))))))).

Eval vm_compute in typeof_expr nil nil test_op.

Eval vm_compute in mkNode (Var 0) (apCons tyVal "n" (Var 0)).

Definition rw_unfold_list (e : expr typ JavaFunc.func) 
	(rvars : list (RG (expr typ JavaFunc.func))) (rg : RG (expr typ JavaFunc.func)) :
 	m (expr typ JavaFunc.func) :=
  match e with
    | App
        (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
           (App
              (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                 (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                    (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))))))
              (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var p)))))))))
        xs =>
          rg_plus
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointstoVar p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs))))
              	))
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGflip (RGinj (fEntails tySasn))))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointstoVar p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs))))
              ))
    | App
         (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
            (App
               (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                  (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))))))
               p))
         (App
            (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) (tyList tyVal)))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) (tyList tyVal))))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) (tyList tyVal))))))))) (Inj (inl (inl (inl (inl (inr (pCons tyVal)))))))))
                 x))
            xs)
        => rg_plus
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto (lift 0 1 p) "val" (lift 0 1 x)) 
              	(mkStar tySasn (mkPointsto (lift 0 1 p) "next" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs)))))))
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGflip (RGinj (fEntails tySasn))))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto (lift 0 1 p) "val" (lift 0 1 x)) 
              	(mkStar tySasn (mkPointsto (lift 0 1 p) "next" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs)))))))
    | _ => rg_fail
  end.

(* List match works *)

Eval vm_compute in 
	match mkList "this" (mkConst (tyList tyVal) (mkConst tyVal (mkNil tyVal))) with
    | App
        (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
           (App
              (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                 (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                    (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))))))
              (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var p)))))))))
        xs => true
    | _ => false
    end.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.EmbedSetoidRewrite.

Require Import MirrorCharge.PullQuant.BILPullQuant.
Require Import MirrorCharge.PullQuant.ILPullQuant.
Require Import MirrorCharge.PullQuant.EmbedPullQuant.

Definition pull_quant vars :=
  setoid_rewrite vars _ (fEntails : typ -> expr typ func) rw_fail
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ func _ _ _ ilops _ _)
                                        (sr_combine bil_respects (sr_combine embed_respects
                                                    (sr_combine eq_respects refl)))))
    (sr_combineK  (il_match_plus (fun _ => true) fEq)
                  (sr_combineK (bil_match_plus fEq) (eil_match_plus fEq))).

Definition PULL_EXISTSR : rtac typ (expr typ func) :=
  fun tus tvs lus lvs c s e =>
  match e with
    | App (App f p) q =>
      match ilogicS f with
        | Some (ilf_entails t) => 
          match pull_quant (getVars c) t q with
            | Some (q', _) => More s (GGoal (App (App f p) q'))
            | _ => More s (GGoal e)
          end
        | _ => More s (GGoal e)
      end
    | _ => More s (GGoal e)
  end.

Require Import MirrorCharge.ModularFunc.EmbedFunc.
Require Import MirrorCharge.RTac.Intro.

Definition exists_body : expr typ func :=
  mkForall tyVal tyProp 
    (mkForall tyVal tyProp
    (mkEntails tyProp (mkTrue tyProp) 
    	(mkAnd tyProp (mkTrue tyProp) (mkExists tyVal tyProp (mkEq tyVal (Var 0) (Var 1)))))).

Eval vm_compute in (THEN (INTRO typ func) PULL_EXISTSR)
	 nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ JavaFunc.func)) exists_body.
Eval vm_compute in exists_body.

Require Import MirrorCore.Lambda.Red.

Definition blarf : expr typ func :=
App (Abs tyVal (App (App (Inj (inl (inl (inl (inl (inl (inr (pEq tyVal)))))))) 
	(ExprCore.Var 0)) (ExprCore.Var 8))) (Var 3).
Check beta.
Eval vm_compute in beta blarf.
Eval vm_compute in typeof_expr nil nil exists_body.

(* Rewriting with rw_true works *)

Eval vm_compute in 
  setoid_rewrite nil _ (fEntails : typ -> expr typ (JavaFunc.func)) rw_true
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail) tySasn (mkAnd tySasn (mkTrue tySasn) (mkTrue tySasn)).

(* rewriting with rw_unfold_list does not *)

Eval vm_compute in
  setoid_rewrite nil _ (fEntails : typ -> expr typ (JavaFunc.func)) rw_unfold_list
    (sr_combine (il_respects (typ := typ) (func := JavaFunc.func))
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail) tySasn (mkList "x" (mkConst (tyList tyVal) (mkNil tyVal))).

Definition add_body := 
      cseq (calloc "tn" "NodeC")
         (cseq (cwrite "tn" "val" (E_var "n"))
              (cseq (cread "lst" "this" "head")   
                    (cseq (cwrite "tn" "next" (E_var "lst"))
                          (cseq (cwrite "this" "head" (E_var "tn")) cskip)))).

Definition testAdd :=
		(mkForall (tyList tyVal) tyProp
		  	(mkEntails tySpec (mkProgEq (mkProg ListProg))
		  	           (mkTriple (mkList "this" (mkConst (tyList tyVal) (Var 0)))
		  	           			 (mkCmd add_body)
		  	           			 (mkList "this" (apCons tyVal "n" (mkConst (tyList tyVal) (Var 0))))))).


Set Printing Depth 100.  	           		

Fixpoint goal_to_expr (g : Goal typ (expr typ func)) : list (expr typ func) :=
  match g with
    | GGoal e => e::nil
    | GSolved => nil
    | GExs _ _ g => goal_to_expr g
    | GHyp _ g => goal_to_expr g
    | GAll _ g => goal_to_expr g
    | GConj_ l r => (goal_to_expr l) ++ (goal_to_expr r)
  end.

Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Cancellation.
Print ent_exists_right_lemma.
Print pull_exists_lemma.
Definition runTac2 (tac : expr typ JavaFunc.func) rw := 
     (THEN (THEN (THEN (THEN (THEN (THEN (THEN (REPEAT 1000 (INTRO typ JavaFunc.func)) (symE rw)) 
	(INSTANTIATE typ JavaFunc.func)) 
		(TRY (THEN (THEN (THEN (APPLY typ JavaFunc.func ent_exists_right_lemma) (INSTANTIATE typ JavaFunc.func))
			(INTRO typ JavaFunc.func)) BETA)))
	 (STEP_REWRITE rw))  PULL_EXISTSR)
		((THEN (THEN (THEN (APPLY typ JavaFunc.func ent_exists_right_lemma) (INSTANTIATE typ JavaFunc.func))
			(INTRO typ JavaFunc.func)) BETA)))
			
     (CANCELLATION typ func tySasn is_pure))
	 nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ JavaFunc.func)) tac.

Time Eval vm_compute in runTac2 testAdd rw_unfold_list.

Time Eval vm_compute in 
	match (runTac testAdd rw_unfold_list) with
		| More_ _ g => 
		  Some (match goalD nil nil g with
		          | Some _ => None
		          | _ => Some g
		        end
		       )
		| _ => None
	end.
