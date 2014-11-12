Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.
Require Import MirrorCharge.Java.SymEx.
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

Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.

Require Import Java.Examples.ListModel.
Require Import Java.Examples.ListClass.
Require Import Java.Language.Lang.
Require Import Java.Logic.AssertionLogic.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.PullConjunct.ILPullConjunct.

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
	(mkStar tySasn (mkPointsto "x" "head" (mkConst tyVal (Var 0))) 
		(mkNode (mkConst tyVal (Var 0)) (mkConst (tyList tyVal) (mkNil tyVal))))).

(* Unfold predicate for list *)

Definition test_op : expr typ JavaFunc.func :=
  ((App (Inj (inl (inl (inl (inr of_stack_get))))) 
  (Inj (inl (inl (inl (inr (of_var "p")))))))).

Eval vm_compute in typeof_expr nil nil test_op.

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
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs))))
              	))
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGflip (RGinj (fEntails tySasn))))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) (lift 0 1 xs))))
              ))
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

(* Rewriting with rw_true works *)

Eval vm_compute in 
  setoid_rewrite _ (fEntails : typ -> expr typ (JavaFunc.func)) rw_true
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail) tySasn (mkAnd tySasn (mkTrue tySasn) (mkTrue tySasn)).

(* rewriting with rw_unfold_list does not *)

Eval vm_compute in
  setoid_rewrite _ (fEntails : typ -> expr typ (JavaFunc.func)) rw_unfold_list
    (sr_combine (il_respects (typ := typ) (func := JavaFunc.func))
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail) tySasn (mkList "x" (mkConst (tyList tyVal) (mkNil tyVal))).

Definition add_body := 
  cseq (calloc "tn" "NodeC") cskip.
    (*   (cseq (cwrite "tn" "val" (E_var "n"))
              (cseq (cread "lst" "this" "head")   
                    (cseq (cwrite "tn" "next" (E_var "lst"))
                          (cseq (cwrite "this" "head" (E_var "tn")) cskip)))).*)
(*
Definition testAdd :=
		(mkForall (tyList tyVal) tyProp
		  	(mkEntails tySpec (mkProgEq (mkProg ListProg))
		  	           (mkTriple (mkList "this" (mkConst (tyList tyVal) (Var 0)))
		  	           			 (mkCmd add_body)
		  	           			 (mkList "this" (apCons tyVal "n" (mkConst (tyList tyVal) (Var 0))))))).
*)
Definition testAdd :=
		(mkForall (tyList tyVal) tyProp
		  	(mkEntails tySpec (mkProgEq (mkProg ListProg))
		  	           (mkTriple (mkList "this" (mkConst (tyList tyVal) (Var 0)))
		  	           			 (mkCmd add_body)
		  	           			 (mkFalse tySasn)))).

Set Printing Depth 100.  	           		

Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Instantiate.
	 
Definition runTac (tac : expr typ JavaFunc.func) rw := 
   THEN (THEN (REPEAT 1000 (INTRO typ JavaFunc.func subst)) (runOnGoals (symE rw))) 
	(runOnGoals (INSTANTIATE typ JavaFunc.func subst))
	 nil nil 0 0 (@SubstI.empty (ctx_subst subst CTop) (expr typ JavaFunc.func) _) tac.

Eval vm_compute in runTac testAdd rw_unfold_list.

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

Definition g : Goal typ (expr typ JavaFunc.func) :=
GAll (tyList tyVal)
                  (GAll tyVal
                     (GGoal
                        (App
                           (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_entails tySpec))))))))))
                              (App (Inj (inr pProgEq))
                                 (Inj
                                    (inr
                                       (pProg
                                          {|
                                          Program.p_classes := ("List",
                                                               {|
                                                               Program.c_fields := "head" :: nil;
                                                               Program.c_methods := ("add",
                                                                    {|
                                                                    Program.m_params := "this" :: "n" :: nil;
                                                                    Program.m_body := "tn" N=  alloc "NodeC";;
                                                                    "tn" ["val"]W=E_var "n";; "lst" R= "this" ["head"];; "tn" ["next"]W=E_var "lst";; "this" ["head"]W=E_var "tn";
                                                                    Program.m_ret := E_val 0%Z |}) :: nil |})
                                                               :: ("NodeC", {| Program.c_fields := "val" :: "next" :: nil; Program.c_methods := nil |}) :: nil |})))))
                           (App
                              (App
                                 (App (Inj (inr pTriple))
                                    (App
                                       (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_and tySasn))))))))))
                                          (App (Inj (inl (inl (inr (EmbedFunc.eilf_embed tyPure tySasn)))))
                                             (App
                                                (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_and tyPure))))))))))
                                                   (App
                                                      (App (Inj (inl (inl (inl (inr (of_ap tyVal tyProp))))))
                                                         (App
                                                            (App (Inj (inl (inl (inl (inr (of_ap tyClass (tyArr tyVal tyProp)))))))
                                                               (App (Inj (inl (inl (inl (inr (of_const (tyArr tyClass (tyArr tyVal tyProp)))))))) (Inj (inr pTypeOf))))
                                                            (App (Inj (inl (inl (inl (inr (of_const tyClass)))))) (Inj (inr (pClass "NodeC"))))))
                                                      (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var "tn")))))))))
                                                (App
                                                   (App (Inj (inl (inl (inl (inr (of_ap tyVal tyProp))))))
                                                      (App
                                                         (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyVal tyProp)))))))
                                                            (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyVal tyProp))))))))
                                                               (Inj (inl (inl (inl (inl (inl (inr (pEq tyVal))))))))))
                                                         (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var "tn")))))))))
                                                   (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Var 1))))))
                                       (App
                                          (App (Inj (inl (inl (inl (inl (inl (inl (inr (bilf_star tySasn)))))))))
                                             (App
                                                (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                                                   (App
                                                      (App (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                                         (App
                                                            (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                                               (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn)))))))))
                                                                  (Inj (inr pPointsto))))
                                                            (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var "tn")))))))))
                                                      (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "val"))))))
                                                (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Inj (inr (pVal null))))))
                                          (App
                                             (App (Inj (inl (inl (inl (inl (inl (inl (inr (bilf_star tySasn)))))))))
                                                (App
                                                   (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                                                      (App
                                                         (App (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                                            (App
                                                               (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                                                  (App 
                                                                    (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn)))))))))
                                                                    (Inj (inr pPointsto))))
                                                               (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var "tn")))))))))
                                                         (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "next"))))))
                                                   (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Inj (inr (pVal null))))))
                                             (App
                                                (App (Inj (inl (inl (inl (inr (of_apply_subst tyAsn))))))
                                                   (App
                                                      (App (Inj (inl (inl (inl (inl (inl (inl (inr (bilf_star tySasn)))))))))
                                                         (App
                                                            (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                                                               (App
                                                                  (App 
                                                                    (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                                                    (App
                                                                    (App 
                                                                    (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                                                    (App 
                                                                    (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn)))))))))
                                                                    (Inj (inr pPointsto))))
                                                                    (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var "this")))))))))
                                                                  (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "head"))))))
                                                            (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Var 1))))
                                                      (App
                                                         (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                                                            (App
                                                               (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                                                                  (App 
                                                                    (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                                                    (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))))))
                                                               (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Var 1))))
                                                         (App (Inj (inl (inl (inl (inr (of_const (tyList tyVal))))))) (Var 0)))))
                                                (App (App (Inj (inl (inl (inl (inr of_single_subst))))) (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Var 1)))
                                                   (Inj (inl (inl (inl (inr (of_var "tn")))))))))))) 
                                 (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_false tySasn))))))))))) 
                              (Inj (inr (pCmd Skip))))))).

Time Eval vm_compute in 
match goalD nil nil g with
		          | Some _ => None
		          | _ => Some g
		      
	end.


