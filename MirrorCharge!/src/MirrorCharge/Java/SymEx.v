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
Require Import MirrorCharge.Java.Semantics.
Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import MirrorCore.Reify.Reify.

Require Import MirrorCharge.Java.Reify.

Require Import MirrorCharge.RTac.Subst.


Require Import Java.Language.Lang.
Require Import Java.Language.Program.
 
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.Cancellation.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.EApply.
Require Import MirrorCharge.RTac.Instantiate.
 
Require Import Coq.Arith.Peano_dec.

Fixpoint mkStars n P Q : expr typ func := 
	match n with
		| 0 => mkStar tySasn P Q
		| S n => mkStar tySasn (mkStars n P Q) (mkStars n P Q)
	end.
	
Definition cancelTest n :=
      mkForall tySasn tyProp
      (mkForall tySasn tyProp
          (mkEntails tySasn (mkStars n (Var 0) (Var 1)) (mkStars n (Var 1) (Var 0)))).
Time Eval vm_compute in typeof_expr nil nil (cancelTest 10).

Time Eval vm_compute in 
	(THEN (REPEAT 10 (INTRO typ func subst)) 
	(CANCELLATION typ func subst tySasn)) 
		CTop (SubstI.empty (expr := expr typ func)) (cancelTest 10).

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

Require Import MirrorCharge.Java.Semantics.
  
(** Skip **)
Definition skip_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_imp rule_skip.
Defined.
Print skip_lemma.

Example test_skip_lemma : test_lemma skip_lemma. Admitted.

Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func).
reify_lemma reify_imp rule_skip2.
Defined.
Print skip_lemma2.

Example test_skip_lemma2 : test_lemma skip_lemma2. Admitted.

Definition seq_lemma (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_seq c1 c2).
Defined.
Print seq_lemma.

Example test_seq_lemma (c1 c2 : cmd) : test_lemma (seq_lemma c1 c2). Admitted.

Definition if_lemma (e : dexpr) (c1 c2 : cmd) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_if e c1 c2).
Defined.

Print if_lemma.

Example test_if_lemma e (c1 c2 : cmd) : test_lemma (if_lemma e c1 c2). Admitted.

Definition read_lemma (x y : var) (f : field) : lemma typ (expr typ func) (expr typ func).
Proof.  
  reify_lemma reify_imp (@rule_read_fwd x y f).
Defined.

Example test_read_lemma x y f : test_lemma (read_lemma x y f). Admitted.

Set Printing Width 140.

Definition write_lemma (x : var) (f : field) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_write_fwd x f e).
Defined.
Print write_lemma.

Example test_write_lemma x f e : test_lemma (write_lemma x f e). Admitted.

Definition assign_lemma (x : var) (e : dexpr) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_assign_fwd x e).
Defined.
Print assign_lemma.
Example test_assign_lemma x e : test_lemma (assign_lemma x e). Admitted.

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@pull_exists val).
Defined.

Print pull_exists_lemma.

Example test_pull_exists : test_lemma (pull_exists_lemma). Admitted.

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

Definition solve_entailment : rtac typ (expr typ func) subst := 
      THEN (INSTANTIATE typ func subst)
             (THEN (SUBST typ func subst)
                   (CANCELLATION typ func subst tySasn)).

Definition simStep (r : rtac typ (expr typ func) subst) : 
	rtac typ (expr typ func) subst := 
	THEN (INSTANTIATE typ func subst)
	     (THEN (TRY (THEN (APPLY typ func subst pull_exists_lemma) (REPEAT 10 (INTRO typ func subst))))
	           r).

Fixpoint tripleE (c : cmd) : rtac typ (expr typ func) subst :=
	match c with
	    | cskip => THEN (INSTANTIATE typ func subst) (THEN (APPLY typ func subst skip_lemma) solve_entailment)
		| cseq c1 c2 => simStep (THEN (EAPPLY typ func subst (seq_lemma c1 c2))
						              (FIRST (tripleE c1::tripleE c2::nil)))
		| cassign x e => simStep (THEN (EAPPLY typ func subst (assign_lemma x e)) solve_entailment)
		| cread x y f => simStep (THEN (EAPPLY typ func subst (read_lemma x y f)) solve_entailment)
		| cwrite x f e => simStep (THEN (EAPPLY typ func subst (write_lemma x f e)) solve_entailment)
		| _ => @IDTAC _ _ _
	end.

Definition symE : rtac typ (expr typ func) subst :=
	(fun ctx s e => 
		(match e return rtac typ (expr typ func) subst with 
			| App (App (Inj f) G) H =>
			  match ilogicS f, H with
			  	| Some (ilf_entails tySpec), 
			  	  App (App (App (Inj (inr pTriple)) P) Q) (Inj (inr (pCmd c))) =>
			  	  	tripleE c
			  	| _, _ => @FAIL _ _ _
			  end
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

Definition testSkip : expr typ func := 
      mkForall tySpec tyProp
      (mkForall tySasn tyProp
                (mkEntails tySpec (Var 1)
                (mkTriple (Var 0) (mkCmd cskip) (Var 0)))).
Time Eval vm_compute in typeof_expr nil nil testSkip.

Eval vm_compute in
(mkForall tyProp tySpec
      (mkForall tyProp tySasn
                (mkEntails tySpec (Var 1)
                (mkTriple (Var 0) (mkCmd cskip) (Var 0)))) : expr typ func).

Time Eval vm_compute in 
  (THEN (REPEAT 10 (INTRO typ func subst)) symE) CTop (SubstI.empty (expr := expr typ func)) testSkip.
  
Time Eval vm_compute in testSkip.

Require Import MirrorCharge.ModularFunc.OpenFunc.

Definition mkPointsto x f e : expr typ func :=
   mkAp tyVal tyAsn 
        (mkAp tyField (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyField (tyArr tyVal tyAsn))
                    (mkConst (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))) 
                             fPointsto)
                    (App fStackGet (mkVar x)))
              (mkConst tyField (mkField f)))
        e.

Require Import String.
Open Scope string.

Definition test_read :=
    mkExists tySasn tyProp
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cread "x" "o" "f"))
  	                     (Var 0))).

Definition test_read2 :=
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointsto "x" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cread "x" "o" "f"))
  	                     (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 4)))))).

Definition runTac tac := (THEN (REPEAT 10 (INTRO typ func subst)) symE)
	 CTop (SubstI.empty (expr :=expr typ func)) tac.

Time Eval vm_compute in runTac test_read.
Time Eval vm_compute in runTac test_read2.

Definition test_write :=
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cwrite "o" "f" (E_val (vint 4))))
  	                     (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 4)))))).

Time Eval vm_compute in runTac test_write.

Definition testSwap :=
	mkForall tyVal tyProp
		(mkForall tyVal tyProp
		  	(mkEntails tySpec (mkTrue tySpec)
		  	           (mkTriple (mkStar tySasn 
		  	           			    (mkPointsto "o" "f1" (mkConst tyVal (Var 0)))
		  	           			    (mkPointsto "o" "f2" (mkConst tyVal (Var 1))))
		  	           			 (mkCmd (cseq (cread "x1" "o" "f1")
  	                                           (cseq (cread "x2" "o" "f2")
  	                                                 (cseq (cwrite "o" "f1" (E_var "x2"))
  	                                                       (cwrite "o" "f2" (E_var "x1"))))))
		  	           			 (mkStar tySasn 
		  	           			    (mkPointsto "o" "f1" (mkConst tyVal (Var 1)))
		  	           			    (mkPointsto "o" "f2" (mkConst tyVal (Var 0))))))).
			
Time Eval vm_compute in runTac testSwap.
