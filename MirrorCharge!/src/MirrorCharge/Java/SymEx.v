Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.provers.DefaultProver.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN. 
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Java.Cancelation.
Require Import MirrorCharge.Java.Syntax.
Require Import MirrorCharge.Java.Semantics.

Require Import MirrorCore.Reify.Reify.

Require Import MirrorCharge.Java.Reify.

Require Import MirrorCharge.Java.Subst.


Require Import Java.Language.Lang.
Require Import Java.Language.Program.
 
Require Import Coq.Arith.Peano_dec.
    
Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Fixpoint search_NoDup
    {A} (A_dec: forall a b: A, {a=b}+{a=b->False}) (l: list A) : option (NoDup l) :=
  match l with
  | nil => Some (NoDup_nil A)
  | a::l' =>
      match search_NoDup A_dec l' with
      | Some nodup =>
          match In_dec A_dec a l' with
          | left isin => None
          | right notin => 
 			match search_NoDup A_dec l' with
 				| Some pf => Some (NoDup_cons _ notin pf)
 				| None => None         
            end
          end
      | None => None
      end
  end.

Definition list_notin_set lst s :=
  	fold_right (fun a acc => andb (SS.for_all (fun b => negb (string_dec a b)) s) acc) true lst.
(*
Definition method_specI : stac typ (expr typ func) subst :=
  fun tus tvs s lst e =>
    match e with
    	| mkEntails [l, mkProgEq [mkProg [P]], mkMethodSpec [C, m, mkVarList [args], mkString [r], p, q]] => 
    	      match C, m with
    	        | Inj (inl (inr (pString Cname))), Inj (inl (inr (pString Mname))) => 
    	          match SM.find Cname (p_classes P) with
    	          	| Some Class => 
    	          	  match SM.find Mname (c_methods Class) with
    	          	    | Some Method => 
						  match search_NoDup Coq.Strings.String.string_dec args with
						  	| Some pf => 
						  	  match eq_nat_dec (length args) (length (m_params Method)) with
						  	    | left pf' => 
						  	      if list_notin_set args (modifies (m_body Method)) then
						  	        More tus tvs s lst 
						  	        mkEntails [l, mkProgEq [mkProg [P]], 
						  	                      mkTriple [mkApplyTruncSubst [tyAsn, p, mkSubstList [mkVarList [args], mkExprList [map E_var (m_params Method)]] ], mkCmd [m_body Method], 
						  	                               mkApplyTruncSubst [tyAsn, q, mkSubstList [mkVarList [r::args], mkConsExprList [App fEval (mkExpr [m_ret Method]), mkExprList[map E_var (m_params Method)]]] ]]]
						  	      else
						  	        @Fail _ _ _
						  	    | right _ => @Fail _ _ _
						  	  end 
						  	| None => @Fail _ _ _
						  end
    	          	    | None => @Fail _ _ _
    	          	  end
    	          	| None => @Fail _ _ _
    	          end
    	        | _, _ => @Fail _ _ _
    	      end
      	| _ => @Fail _ _ _
    end.
*)

Fixpoint get_alls (e : expr typ func) : list typ * expr typ func :=
  match e with
    | ExprCore.App (@ExprCore.Inj (inr (ILogicFunc.ilf_forall t tyProp)))
                   (ExprCore.Abs _ e) =>
      let (alls,e) := get_alls e in
      (t :: alls, e)
    | _ => (nil, e)
  end.

Fixpoint get_impls (e : expr typ func) : list (expr typ func) * expr typ func :=
  match e with
    | ExprCore.App (ExprCore.App (Inj (inr (ILogicFunc.ilf_impl tyProp))) P) Q =>
      let (impls,e) := get_impls Q in
      (P :: impls,e)
    | _ => (nil, e)
  end.

Definition convert_to_lemma (e : expr typ func)
: lemma typ (expr typ func) (expr typ func) :=
  let (alls, e) := get_alls e in
  let (impls, e) := get_impls e in
  {| vars := rev alls
   ; premises := impls
   ; concl := e |}.

Ltac reify_lemma_aux T :=
(let k e :=
           let e := constr:(convert_to_lemma e) in
           let e := eval unfold convert_to_lemma in e in
           let e := eval simpl in e in
           refine e
       in
       reify_expr Reify.reify_imp k [ True ] [ T ]).

Ltac reify_lemma e :=
	let T := type of e in reify_lemma_aux T.
(*
Ltac reify_lemma e :=
  match type of e with
    | ?T =>
      (let k e :=
           let e := constr:(convert_to_lemma e) in
           let e := eval unfold convert_to_lemma in e in
           let e := eval simpl in e in
           refine e
       in
       reify_expr Reify.reify_imp k [ True ] [ T ])
  end.
*)

Require Import MirrorCharge.Java.Semantics.
  
(** Skip **)
Definition skip_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma rule_skip.
Defined.
Print skip_lemma.

Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func).
reify_lemma rule_skip2.
Defined.
Print skip_lemma2.

Definition seq_lemma (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma (@rule_seq c1 c2).
Defined.
Print seq_lemma.

Ltac reify_lemma2 e :=
  match type of e with
    | ?T =>
      (let k e :=
           let e := constr:(convert_to_lemma e) in
           let e := eval unfold convert_to_lemma in e in
           let e := eval simpl in e in
           refine e
       in
       reify_imp T)
 (*     reify_expr Reify.reify_imp k [ True ] [ T ])*)
  end.

Definition if_lemma (e : dexpr) (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma (@rule_if e c1 c2).
Defined.
Print if_lemma.

Definition read_lemma (x y f : String.string) : lemma typ (expr typ func) (expr typ func).
Proof.  
  reify_lemma (@rule_read_fwd x y f).
Defined.
Print read_lemma.

Definition write_lemma (x f : String.string) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma (@rule_write_fwd x f e).
Defined.
Print write_lemma.

Example test_write x f e : test_lemma (write_lemma x f e). Admitted.

Definition assign_lemma (x : String.string) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma (@rule_assign_fwd x e).
Defined.
Print assign_lemma.

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma (@pull_exists sval).
Defined.

Print pull_exists_lemma.

(*
Definition fieldLookupTac : stac typ (expr typ func) subst :=
	fun tus tvs s lst e =>
		match e with
		  | mkFieldLookup [mkProg [P], mkString [C], X] =>
		  	match SM.find C (p_classes P) with
    	      | Some Class =>
    	        match @exprUnify subst typ func _ _ RS SS SU 3
                                 tus tvs 0 s X (mkFields[c_fields Class]) tyVarList with
                  | Some s => Solved nil nil s
                  | None   => Fail
                end
    	      | None => Fail 
		    end
		  | _ => Fail
		end.
*)

Let EAPPLY :=
  @EAPPLY typ (expr typ func) subst _ _ SS SU ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func)
(*                lem (apply_to_all tac)*).

  Let APPLY :=
    @APPLY typ (expr typ func) subst _ Typ0_Prop SS SU
           ExprLift.vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ RS SS SU 3
                         tus tvs n s e1 e2 t)
           (@ExprSubst.instantiate typ func)
          (* lem (apply_to_all tac)*).

Require Import MirrorCharge.Java.Subst.

Let INSTANTIATE := 
	@INSTANTIATE typ (expr typ func) subst SS (@ExprSubst.instantiate typ func).

Require Import MirrorCore.RTac.RTac.

Definition fintro e : option (OpenAs typ (expr typ func)) :=
	match e with
		| App (Inj (inr (ilf_forall t tyProp))) P => Some (AsAl t (fun x => beta (App P x)))
		| App (Inj (inr (ilf_exists t tyProp))) P => Some (AsEx t (fun x => beta (App P x)))
		| App (App (Inj (inr (ilf_impl tyProp))) P) Q => Some (AsHy typ P Q)
		| _ => None
	end.

Let INTRO := @INTRO typ (expr typ func) subst (@Var typ func) (@UVar typ func) fintro.

(*
Let FINISH := @finish typ (expr typ func) subst SU.
*)

Definition solve_entailment : rtac typ (expr typ func) subst := 
   (*   (THEN INSTANTIATE
             (THEN (SIMPLIFY (fun _ _ => beta_all simplify nil nil))*)
                   (STAC_no_hyps (@ExprSubst.instantiate typ func) stac_cancel).

Definition simStep (r : rtac typ (expr typ func) subst) : 
	rtac typ (expr typ func) subst :=
	THEN INSTANTIATE
	     (THEN (TRY (THEN (APPLY pull_exists_lemma) (REPEAT 10 INTRO)))
	           r).

Fixpoint tripleE (c : cmd) : rtac typ (expr typ func) subst :=
	match c with
	    | cskip => THEN INSTANTIATE (THEN (APPLY skip_lemma) solve_entailment)
		| cseq c1 c2 => simStep (THEN (EAPPLY (seq_lemma c1 c2))
						              (FIRST (tripleE c1::tripleE c2::nil)))
		| cassign x e => simStep (THEN (EAPPLY (assign_lemma x e)) solve_entailment)
		| cread x y f => simStep (THEN (EAPPLY (read_lemma x y f)) solve_entailment)
		| cwrite x f e => simStep (THEN (EAPPLY (write_lemma x f e)) solve_entailment)
		| _ => @IDTAC _ _ _
	end.

Definition symE : rtac typ (expr typ func) subst :=
	(fun ctx s e => 
		(match e return rtac typ (expr typ func) subst with 
			| App (App (Inj (inr (ilf_entails tySpec))) G) 
			      (App (App (App (Inj (inl (inr pTriple))) P) Q) (Inj (inl (inr (pCmd c))))) => 
			  (tripleE c)
			| _ => @FAIL _ _ _
		end) ctx s e).  
		
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.

Require Import Charge.Logics.ILogic.

Definition typecheck_goal g :=
  match goalD nil nil g with
    | None => false
    | Some _ => true
  end.

Definition testSkip := 
      mkForall tyProp tySpec
      (mkForall tyProp tySasn
                (mkEntails tySpec (Var 1)
                (mkTriple (Var 0) (mkCmd cskip) (Var 0)))).
Time Eval vm_compute in typeof_expr nil nil testSkip.

Time Eval vm_compute in 
  (THEN (REPEAT 10 INTRO) symE) CTop (SubstI.empty (expr := expr typ func)) testSkip.
  
Time Eval vm_compute in testSkip.

Open Scope string.

Definition mkPointsto x f e : expr typ func :=
   mkAp tyVal tyAsn 
        (mkAp tyString (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyString (tyArr tyVal tyAsn))
                    (mkConst (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn))) 
                             fPointsto)
                    (App fStackGet (mkString x)))
              (mkConst tyString (mkString f)))
        e.

Definition test_read :=
    mkExists tyProp tySasn
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cread "x" "o" "f"))
  	                     (Var 0))).
Eval vm_compute in typeof_expr nil nil test_read.

Definition runTac tac := (THEN (REPEAT 10 INTRO) symE)
	 CTop (SubstI.empty (expr :=expr typ func)) tac.

Set Printing Width 140.

Time Eval vm_compute in runTac test_read.

Eval vm_compute in match runTac test_read with
					| More _ g => Some (typecheck_goal g)
					| _ => None
				   end.

Opaque the_canceller.

(* GREGORY: This example test demonstrates the problem *)

Example test : exists x, x = runTac test_read.
Proof.
  compute.
  Check the_canceller.
  match goal with
  | |- context [the_canceller ?a ?b ?c ?d ?e] =>
  	remember (the_canceller a b c d e)
  end.
  
  Transparent the_canceller.

  compute in Heqs.
  rewrite Heqs.
  clear.

  match goal with
  | |- context [the_canceller ?a ?b ?c ?d ?e] =>
 	 pose c; pose d; remember (the_canceller a b c d e)
  end.
  (* Here c is an expression and d is a unification variable. I want this cancellation to succeed *)
  clear e e0.
  cbv in Heqs. (*But here it fails *)

  rewrite Heqs.
  
  (* And we get a lot of new uninstantiated unification variables that I don't know where they are coming from *)
  
  
  Opaque the_canceller.
  
  compute.
  vm_compute.
  Check nat.

Definition read_result := Eval vm_compute in test_read.

Eval vm_compute in 
     match read_result with
	   | More _ g => Some (typecheck_goal g)
	   | _ => None
	 end.

Print More.
Print read_lemma.
Definition testWrite :=
  let goal :=
    mkExists [tyProp, tySasn,
  	mkEntails [tySpec, mkTrue [tySpec], 
  	           mkTriple [mkPointsto "o" "f" (mkConst [tyVal, mkVal [vint 3]]),
  	                     mkCmd [cwrite "o" "f" (E_val (vint 0))],
  	                     (Var 0)]]]
  in
  (THEN (REPEAT 10 INTRO) symE)
  	    CTop (SubstI.empty (expr :=expr typ func)) goal.

Set Printing Width 140.

Time Eval vm_compute  in testWrite.

(* GREGORY this fails *)

Print write_lemma.
Eval compute in typeof_expr nil nil (
                              mkStar  [tySasn, mkEmp  [tySasn],
                                      mkAp  [tyVal, tyAsn,
                                            mkAp  [tyString, tyArr tyVal tyAsn,
                                                  mkAp  [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                                  mkConst  [tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)), 
                                                           fPointsto], 
                                                  App fStackGet mkString  ["o"]], 
                                            mkConst  [tyString, mkString  ["f"]]], 
                                      mkConst  [tyVal, mkVal  [3%Z]]]] ).

Print write_lemma.


Definition testSwap :=
  let goal := mkExists [tyProp, tySasn,
              mkEntails [tySpec, mkTrue [tySpec],
  	                     mkTriple [mkStar [tySasn,
  		                                   mkPointsto "o" "f1" (mkConst [tyVal, mkVal [vint 1]]),
	  	                                   mkPointsto "o" "f2" (mkConst [tyVal, mkVal [vint 2]])],                                           	                      
  	                               mkCmd [cseq (cread "x1" "o" "f1")
  	                                           (cseq (cread "x2" "o" "f2")
  	                                                 (cseq (cwrite "o" "f1" (E_var "x2"))
  	                                                       (cwrite "o" "f2" (E_var "x1"))))], 
			                       
			                       mkStar [tySasn,
			                               mkPointsto "o" "f1" (mkConst [tyVal, mkVal [vint 2]]),
			                               mkPointsto "o" "f2" (mkConst [tyVal, mkVal [vint 1]])]]]]
  in
  (THEN (REPEAT 10 INTRO) symE)
  	    CTop (SubstI.empty (expr :=expr typ func)) goal.

Print pull_exists_lemma.
 
Time Eval vm_compute in testSwap.
Print seq_lemma.
Definition test := Eval vm_compute in testSwap.

Print Goal.
Locate Goal.

Check goalD.

Print goalD.

Eval vm_compute in 
match test with
	| More _ g => Some (goalD (typ := typ) (expr := expr typ func) nil nil g)
	| _ => None
end.

Print Goal.

Print Result.

Print test.


Lemma test : exists x, x = testSwap.
Proof.
  Opaque tripleE.
  compute.
  Transparent tripleE.
  Opaque read_lemma.
  unfold tripleE.
  
  unfold simStep.
  Opaque EAPPLY.
  unfold THEN.
  unfold INSTANTIATE, Instantiate.INSTANTIATE, SIMPLIFY, TRY.
  unfold runRTac, runRTac'.
  
  match goal with
  	| |- context [APPLY ?a ?b ?c ?d] =>
  		remember (APPLY a b c d)
  end.
  
  compute in Heqr. rewrite Heqr.
  clear.
  
  simpl.
  
  match goal with
  	| |- context [EAPPLY ?a ?b ?c ?d] =>
  		remember (EAPPLY a b c d)
  end.
  
  Transparent EAPPLY.
  
  compute in Heqr.
  
  rewrite Heqr.
  
  clear.
  
  simpl.
  
  match goal with
  	| |- context [EAPPLY ?a ?b ?c ?d] =>
  		remember (EAPPLY a b c d)
  end.
  
  unfold EAPPLY, EApply.EAPPLY in Heqr.
  
  Opaque LemmaApply.eapplicable.
  simpl in Heqr.
  
   
 match goal with
  	| H : context [LemmaApply.eapplicable ?a ?b ?c ?d ?e ?f ?g ?h] |- _ =>
	remember (LemmaApply.eapplicable a b c d e f g h)
  end.
  
  Transparent LemmaApply.eapplicable.
  
  unfold LemmaApply.eapplicable in Heqo.
  
  Transparent read_lemma.
  
  simpl in Heqo.
  
  Print read_lemma.
  
  compute in Heqo.
  rewrite Heqo in Heqr.
  
  Opaque read_lemma.
  
  simpl in Heqo.
  
  Transparent read_lemma.
  
  simpl in Heqo.
  
  cbv in Heqo.
  
  cbv in Heqo.
    
  compute in Heqr0.
  unfold EAPPLY in Heqr.
  
  compute in Heqr.
  
  Check FIRST.
  
  Opaque seq_lemma.
  unfold tripleE.
  Opaque
  unfold solve_entailment.
  compute.
