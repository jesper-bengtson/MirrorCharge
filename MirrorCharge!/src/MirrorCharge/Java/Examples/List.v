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

Definition rw_true (rw : @rw_type typ JavaFunc.func) (e : expr typ JavaFunc.func) 
	(rvars : list (RG (expr typ JavaFunc.func))) (rg : RG (expr typ JavaFunc.func)) :
 	m (expr typ JavaFunc.func) :=
  match e with
  	| App (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_and tySasn)))))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))))
         (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tySasn)))))))))) =>
         (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGinj (fEntails tySasn)))
          (fun _ => rw (mkTrue tySasn) rvars rg))
    | _ => rg_fail
  end.
  	  

(* List rewrite rule type checks *)

Eval vm_compute in typeof_expr nil nil (mkExists tyVal tySasn 
	(mkStar tySasn (mkPointsto "x" "head" (mkConst tyVal (Var 0))) 
		(mkNode (mkConst tyVal (Var 0)) (mkConst (tyList tyVal) (mkNil tyVal))))).

(* Unfold predicate for list *)

Definition rw_unfold_list (rw : @rw_type typ JavaFunc.func) (e : expr typ JavaFunc.func) 
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
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) xs)))
              	))
            (rg_bind (unifyRG (@rel_dec (expr typ JavaFunc.func) _ _) rg (RGflip (RGinj (fEntails tySasn))))
              (fun _ => rg_ret (mkExists tyVal tySasn (mkStar tySasn (mkPointsto p "head" (mkConst tyVal (Var 0))) (mkNode (mkConst tyVal (Var 0)) xs)))
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
  setoid_rewrite _ (fEntails : typ -> expr typ (JavaFunc.func))
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    rw_true tySasn (mkAnd tySasn (mkTrue tySasn) (mkTrue tySasn)).

(* rewriting with rw_unfold_list does not *)

Eval vm_compute in
  setoid_rewrite _ (fEntails : typ -> expr typ (JavaFunc.func))
    (sr_combine (il_respects (typ := typ) (func := JavaFunc.func))
               (sr_combine (@il_respects_reflexive typ (JavaFunc.func) _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    rw_unfold_list tySasn (mkEntails tyProp (mkList "x" (mkConst (tyList tyVal) (mkNil tyVal))) (mkTrue tySasn)).

(* The rest of the file is junk *)

(*

Eval vm_compute in (STEP_REWRITE rw_true) nil nil 0 0 
	CTop (@ctx_empty typ (expr typ JavaFunc.func) subst SU CTop) goal3.


Definition add_body :=
  cseq (calloc "tn" "NodeC")
       (cseq (cwrite "tn" "val" (E_var "n")) cskip). (*
              (cseq (cread "lst" "this" "head") 
                    (cseq (cwrite "tn" "next" (E_var "lst"))
                          (cwrite "this" "head" (E_var "tn")))))).*)

Definition testAdd :=
		(mkForall (tyList tyVal) tyProp
		  	(mkEntails tySpec (mkProgEq (mkProg ListProg))
		  	           (mkTriple (mkList "this" (mkConst (tyList tyVal) (Var 0)))
		  	           			 (mkCmd add_body)
		  	           			 (mkList "this" (apCons tyVal "n" (mkConst (tyList tyVal) (Var 0))))))).
		  	           	
Set Printing Depth 100.  	           			 

Time Eval vm_compute in runTac testAdd rw_unfold_list.

Require Import MirrorCore.Lambda.AppN.

Definition onetuh : expr typ JavaFunc.func := 
(App (App
                                          (Abs tyExpr
            (Abs (tyArr tyStack (tyList tyVal))
               (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyExpr tySasn))))))))))
                  (Abs tyExpr
                     (App
                        (App (Inj (inl (inl (inl (inl (inl (inl (inr (BILogicFunc.bilf_star tySasn)))))))))
                           (App
                              (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                                 (App
                                    (App (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                       (App
                                          (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                             (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))) (Inj (inr pPointsto)))) 
                                          (Var 2))) (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "head")))))) 
                              (Var 0)))
                        (App
                           (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                              (App
                                 (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                                    (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                       (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))) 
                                 (Var 0))) (Var 1)))))))
                                                (App (Inj (inl (inl (inl (inr of_stack_get))))) (Inj (inl (inl (inl (inr (of_var "this"))))))))
                                          (App (Inj (inl (inl (inl (inr (of_const (tyList tyVal))))))) (Var 0))).

Eval vm_compute in typeof_expr nil (tyList tyVal::nil) onetuh.

Print List.
Goal True.

pose (vint 0) as x.


reify_imp (List x (@nil val) = ILogic.lexists (fun h : val => BILogic.sepSP (pointsto x ("head":field) h) (NodeList h (@nil val)))).

Eval vm_compute in il_lift nil nil 
	(App
       (App (fEq tyAsn) (App (App (Ext 1%positive) (mkVal x)) (fNil tyVal)))
       (App (fExists tyVal tyAsn)
          (Abs tyVal
             (App
                (App (BILogicFunc.fStar tyAsn)
                   (App
                      (App (App fPointsto (mkVal x)) (mkField ("head":field)))
                      (Var 0)))
                (App (App (Ext 2%positive) (Var 0)) (fNil tyVal)))))
  : expr typ JavaFunc.func).

Eval vm_compute in typeof_expr nil nil
(App
            (App (Inj (inl (inl (inl (inr (of_ap tyAsn tyProp))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap tyAsn (tyArr tyAsn tyProp)))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr tyAsn (tyArr tyAsn tyProp)))))))) (Inj (inl (inl (inl (inl (inl (inr (pEq tyAsn))))))))))
                  (App
                     (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                        (App
                           (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                              (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                 (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))) 
                           (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Inj (inr (pVal 0%Z))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyList tyVal))))))) (Inj (inl (inl (inl (inl (inr (pNil tyVal)))))))))))
            (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyExpr tySasn))))))))))
               (Abs tyExpr
                  (App
                     (App (Inj (inl (inl (inl (inl (inl (inl (inr (BILogicFunc.bilf_star tySasn)))))))))
                        (App
                           (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                              (App
                                 (App (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                    (App
                                       (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                          (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))) (Inj (inr pPointsto))))
                                       (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Inj (inr (pVal 0%Z))))))
                                 (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "head")))))) 
                           (Var 0)))
                     (App
                        (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                           (App
                              (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                                 (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                    (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive))))))))))) 
                              (Var 0))) (App (Inj (inl (inl (inl (inr (of_const (tyList tyVal))))))) (Inj (inl (inl (inl (inl (inr (pNil tyVal))))))))))))).
reify_imp List.

Eval vm_compute in il_lift nil nil (Ext 1%positive).

Eval vm_compute in typeof_expr nil nil (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))))).

Definition stuff : expr typ JavaFunc.func :=
       App
        (App (fEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))
           (Ext 1%positive))
        (Abs tyVal
           (Abs (tyList tyVal)
              (App (fExists tyVal tyAsn)
                 (Abs tyVal
                    (App
                       (App (BILogicFunc.fStar tyAsn)
                          (App
                             (App (App fPointsto (Var 2))
                                (mkField ("head":field))) (Var 0)))
                       (App (App (Ext 2%positive) (Var 0)) (Var 1))))))).

Eval vm_compute in il_lift nil nil stuff.

Eval vm_compute in typeof_expr nil nil 
         (App
            (App (Inj (inl (inl (inl (inr (of_ap (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp)))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp))))))))
                        (Inj (inl (inl (inl (inl (inl (inr (pEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))))))
                  (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))))
            (Abs tyExpr
               (Abs (tyArr tyStack (tyList tyVal))
                  (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyExpr tySasn))))))))))
                     (Abs tyExpr
                        (App
                           (App (Inj (inl (inl (inl (inl (inl (inl (inr (BILogicFunc.bilf_star tySasn)))))))))
                              (App
                                 (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                                    (App
                                       (App (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                          (App
                                             (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                                (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))) (Inj (inr pPointsto)))) 
                                             (Var 2))) (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "head")))))) 
                                 (Var 0)))
                           (App
                              (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                                 (App
                                    (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                                       (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                          (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive))))))))))) 
                                    (Var 0))) (Var 1)))))))).Require Import Charge.Logics.ILogic.
Require Import Java.Logic.SpecLogic.
pose (vint 0) as v.
reify_imp (List v nil).
Eval vm_compute in typeof_expr nil nil (App (App (Ext 1%positive) (mkVal v)) (fNil tyVal)).
Eval vm_compute in il_lift nil nil (App (App (Ext 1%positive) (mkVal v)) (fNil tyVal)).
Eval vm_compute in typeof_expr nil nil (App
    (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
       (App
          (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
             (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
               (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive)))))))))))
          (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Inj (inr (pVal 0%Z))))))
    (App (Inj (inl (inl (inl (inr (of_const (tyList tyVal))))))) 
      (Inj (inl (inl (inl (inl (inr (pNil tyVal))))))))).
reify_imp (List = fun x xs => List x xs).
Eval vm_compute in typeof_expr nil nil ( App
        (App (fEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))
           (Ext 1%positive))
        (Abs tyVal
           (Abs (tyList tyVal) (App (App (Ext 1%positive) (Var 1)) (Var 0))))
   : expr typ JavaFunc.func).
Eval vm_compute in il_lift nil nil ( App
        (App (fEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))
           (Ext 1%positive))
        (Abs tyVal
           (Abs (tyList tyVal) (App (App (Ext 1%positive) (Var 1)) (Var 0))))
   : expr typ JavaFunc.func).
  
Eval vm_compute in typeof_expr nil nil   
           (App
            (App (Inj (inl (inl (inl (inr (of_ap (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp)))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp))))))))
                        (Inj (inl (inl (inl (inl (inl (inr (pEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))))))
                  (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))))
            (Abs tyExpr
               (Abs (tyArr tyStack (tyList tyVal))
                  (App
                     (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                        (App
                           (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                              (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                 (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))) 
                           (Var 1))) (Var 0))))).
reify_imp (@lexists Prop _ nat = (fun f => (@lexists Prop _ nat) f).
Eval vm_compute in il_lift nil nil (App
       (App (fEq (tyArr (tyArr tyNat tyProp) tyProp)) (fExists tyNat tyProp))
       (Abs (tyArr tyNat tyProp) (App (fExists tyNat tyProp) (Var 0))):expr typ JavaFunc.func).

Eval vm_compute in typeof_expr nil nil
(App
            (App (Inj (inl (inl (inl (inr (of_ap (tyArr (tyArr tyNat tyProp) tyProp) tyProp))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap (tyArr (tyArr tyNat tyProp) tyProp) (tyArr (tyArr (tyArr tyNat tyProp) tyProp) tyProp)))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr (tyArr (tyArr tyNat tyProp) tyProp) (tyArr (tyArr (tyArr tyNat tyProp) tyProp) tyProp))))))))
                        (Inj (inl (inl (inl (inl (inl (inr (pEq (tyArr (tyArr tyNat tyProp) tyProp)))))))))))
                  (App (Inj (inl (inl (inl (inr (of_const (tyArr (tyArr tyNat tyProp) tyProp))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyNat tyProp)))))))))))))
            (Abs (tyArr tyStack (tyArr tyNat tyProp)) (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists (tyArr tyStack tyNat) tyPure)))))))))) (Var 0)))).

Eval vm_compute in typeof_expr nil nil
(App (Inj (inl (inl (inl (inr (of_const (tyArr (tyArr tyNat tyProp) tyProp))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyNat tyProp))))))))))).
Eval vm_compute in il_lift nil nil (Ext 1%positive).
pose (vint 0) as v.
Check mkEq.
Definition conj (v : val) : expr typ JavaFunc.func :=
	mkExists tyVal tyProp (mkAnd tyProp (mkTrue tyProp) (mkEq tyVal (mkVal v) (Var 0))).
Print conj.
Eval vm_compute in conj.
Eval vm_compute in typeof_expr nil nil (conj v).
Eval vm_compute in il_lift nil nil (conj v).

Eval vm_compute in typeof_expr nil nil 
         (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyExpr tyPure))))))))))
            (Abs tyExpr
               (App (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_and tyPure)))))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_true tyPure)))))))))))
                  (App
                     (App (Inj (inl (inl (inl (inr (of_ap tyVal tyProp))))))
                        (App
                           (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyVal tyProp)))))))
                              (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyVal tyProp)))))))) (Inj (inl (inl (inl (inl (inl (inr (pEq tyVal))))))))))
                           (App (Inj (inl (inl (inl (inr (of_const tyVal)))))) (Inj (inr (pVal 0%Z)))))) 
                     (Var 0))))).
                     
Require Import Charge.Logics.ILogic.

Eval vm_compute in il_lift nil nil
((App (App (fEq tyProp) (mkTrue tyProp)) (mkTrue tyProp)):expr typ JavaFunc.func).

Eval vm_compute in il_lift nil nil (Abs tyVal
       (Abs (tyList tyVal) (App (App (Ext 1%positive) (Var 1)) (Var 0)))).
Eval vm_compute in typeof_expr nil nil (Abs tyExpr
         (Abs tyExpr
            (Abs (tyArr tyStack (tyList tyVal))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                     (App
                        (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                           (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                              (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))) 
                        (Var 1))) (Var 0))))).

reify_imp (mkTrue tyProp = mkTrue tyProp).

                        
reify_imp (List = fun (p : val) (xs : list val) => ILogic.lexists (fun h : val => BILogic.sepSP (pointsto p ("head":field) h) (NodeList h xs))).

reify_imp List.

Eval vm_compute in il_lift nil nil (Ext 1%positive).

Eval vm_compute in typeof_expr nil nil (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive)))))))))).

Definition stuff : expr typ JavaFunc.func :=
       App
        (App (fEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))
           (Ext 1%positive))
        (Abs tyVal
           (Abs (tyList tyVal)
              (App (fExists tyVal tyAsn)
                 (Abs tyVal
                    (App
                       (App (BILogicFunc.fStar tyAsn)
                          (App
                             (App (App fPointsto (Var 2))
                                (mkField ("head":field))) (Var 0)))
                       (App (App (Ext 2%positive) (Var 0)) (Var 1))))))).

Eval vm_compute in il_lift nil nil stuff.

Eval vm_compute in typeof_expr nil nil 
         (App
            (App (Inj (inl (inl (inl (inr (of_ap (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp))))))
               (App
                  (App (Inj (inl (inl (inl (inr (of_ap (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp)))))))
                     (App (Inj (inl (inl (inl (inr (of_const (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) (tyArr (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) tyProp))))))))
                        (Inj (inl (inl (inl (inl (inl (inr (pEq (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))))))
                  (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn)))))))) (Inj (inl (inl (inl (inl (inl (inl (inl (inl 1%positive))))))))))))
            (Abs tyExpr
               (Abs (tyArr tyStack (tyList tyVal))
                  (App (Inj (inl (inl (inl (inl (inl (inl (inl (inr (ilf_exists tyExpr tySasn))))))))))
                     (Abs tyExpr
                        (App
                           (App (Inj (inl (inl (inl (inl (inl (inl (inr (BILogicFunc.bilf_star tySasn)))))))))
                              (App
                                 (App (Inj (inl (inl (inl (inr (of_ap tyVal tyAsn))))))
                                    (App
                                       (App (Inj (inl (inl (inl (inr (of_ap tyField (tyArr tyVal tyAsn)))))))
                                          (App
                                             (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))
                                                (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))))))))) (Inj (inr pPointsto)))) 
                                             (Var 2))) (App (Inj (inl (inl (inl (inr (of_const tyField)))))) (Inj (inr (pField "head")))))) 
                                 (Var 0)))
                           (App
                              (App (Inj (inl (inl (inl (inr (of_ap (tyList tyVal) tyAsn))))))
                                 (App
                                    (App (Inj (inl (inl (inl (inr (of_ap tyVal (tyArr (tyList tyVal) tyAsn)))))))
                                       (App (Inj (inl (inl (inl (inr (of_const (tyArr tyVal (tyArr (tyList tyVal) tyAsn))))))))
                                          (Inj (inl (inl (inl (inl (inl (inl (inl (inl 2%positive))))))))))) 
                                    (Var 0))) (Var 1)))))))).
*)