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
Require Import MirrorCharge.RTac.PullConjunct.
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
	(CANCELLATION typ func subst tySasn is_pure)) 
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
(*


Definition list_notin_set lst s :=
  	fold_right (fun a acc => andb (SS.for_all (fun b => negb (string_dec a b)) s) acc) true lst.

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

Definition alloc_lemma (x : var) (C : class) : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@rule_alloc_fwd x C).
Defined.
Print alloc_lemma.
Example test_alloc_lemma x C : test_lemma (alloc_lemma x C). Admitted.

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@pull_exists val).
Defined.
Eval vm_compute in pull_exists_lemma.

Definition eq_to_subst_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp eq_to_subst.
Defined.
Eval vm_compute in eq_to_subst_lemma.
Example test_eq_lemma : test_lemma (eq_to_subst_lemma). Admitted.

Print pull_exists_lemma.

Example test_pull_exists : test_lemma (pull_exists_lemma). Admitted.

Definition fieldLookupTac : stac typ (expr typ func) subst :=
	fun tus tvs s lst e =>
		match e with
		  | App (App (App (Inj (inr pFieldLookup)) (Inj (inr (pProg P)))) (Inj (inr (pClass C)))) f =>
		  	match class_lookup C P with
    	      | Some Class =>
    	        match @exprUnify subst typ func _ _ _ SS SU 3
                                 tus tvs 0 s f (mkFields (c_fields Class)) tyVarList with
                  | Some s => STac.Core.Solved nil nil s
                  | None   => STac.Core.Fail
                end
    	      | None => STac.Core.Fail 
		    end
		  | _ => STac.Core.Fail
		end.

Definition FIELD_LOOKUP := STAC_no_hyps (@ExprSubst.instantiate typ func) fieldLookupTac.

Require Import MirrorCharge.ModularFunc.ListFunc.

	Definition foldTac (e : expr typ func) (args : list (expr typ func))
	: expr typ func :=
	  match listS e with
	    | Some (pFold t u) =>
	      match args with
	        | f :: acc :: (Inj (inr (pFields fs)))::nil =>
	            fold_right (fun x acc => beta (beta (App (App f (mkField x)) acc))) acc fs
	        | _ => apps e args
	      end
	    | _ => apps e args
	  end.

	Definition FOLD := SIMPLIFY (typ := typ) (subst := subst) (fun _ _ => beta_all foldTac nil nil).

Definition BETA := SIMPLIFY (typ := typ) (subst := subst) (fun _ _ => beta_all (@apps typ func) nil nil).
Definition EQSUBST := THEN (APPLY typ func subst eq_to_subst_lemma) (SUBST typ func subst).
(*
Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := Fun stack) (ap (T := Fun stack) (pure (T := Fun stack) (@eq val)) x) y).
*)

Require Import MirrorCharge.ModularFunc.OpenFunc.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Definition match_ap_eq (e : expr typ func) : bool :=
	match e with 
	  | App emb (App (App f (App (App g (App h e)) x)) y) =>
	  	match embedS emb, open_funcS f, open_funcS g, open_funcS h, baseS e with
	  		| Some (eilf_embed _ _), Some (of_ap _ _), Some (of_ap _ _), Some (of_const _), Some (pEq _) => true
	  		| _, _, _, _, _ => false
	  	end
	  | _ => false
	end.

Definition PULLEQL := PULLCONJUNCTL typ func subst match_ap_eq ilops.

Definition solve_alloc : rtac typ (expr typ func) subst :=
	THEN (INSTANTIATE typ func subst) (THEN (THEN (TRY FIELD_LOOKUP) (CANCELLATION typ func subst tySpec (fun _ => false))) FOLD).

Definition solve_entailment : rtac typ (expr typ func) subst := 
	THEN (INSTANTIATE typ func subst) 
		(FIRST (SOLVE (CANCELLATION typ func subst tySasn is_pure)::
	           THEN (THEN PULLEQL (REPEAT 10 EQSUBST)) (CANCELLATION typ func subst tySasn is_pure)::
	           nil)).
		
Definition simStep (r : rtac typ (expr typ func) subst) : 
	rtac typ (expr typ func) subst := 
	THEN (THEN (SUBST typ func subst) 
	                 (THEN (THEN (TRY (APPLY typ func subst pull_exists_lemma)) (REPEAT 10 (INTRO typ func subst))) BETA))
		 r.

Set Printing Depth 100.

Print alloc_lemma.

Fixpoint tripleE (c : cmd) : rtac typ (expr typ func) subst :=
	match c with
	    | cskip => simStep (THEN (EAPPLY typ func subst skip_lemma) solve_entailment)
	    | calloc x C => simStep (THEN (EAPPLY typ func subst (alloc_lemma x C)) solve_alloc)
		| cseq c1 c2 => simStep (THEN (EAPPLY typ func subst (seq_lemma c1 c2))
						              (THEN (FIRST (tripleE c1::tripleE c2::nil)) solve_entailment))
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
			  	| Some (ilf_entails tySpec), (* tySpec is a pattern, should be checked for equality with tySpec *)
			  	  App (App (App (Inj (inr pTriple)) P) Q) (Inj (inr (pCmd c))) =>
			  	  	tripleE c
			  	| _, _ => @FAIL _ _ _
			  end
			| _ => @FAIL _ _ _
		end) ctx s e).  

Definition runTac tac := THEN (THEN (REPEAT 10 (INTRO typ func subst)) symE) (INSTANTIATE typ func subst)
	 CTop (SubstI.empty (expr :=expr typ func)) tac.

Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Examples.ListClass.
Require Import Charge.Logics.ILogic.

Definition typecheck_goal g :=
  match goalD nil nil g with
    | None => false
    | Some _ => true
  end.

Definition test_alloc : expr typ func :=
	mkEntails tySpec (mkProgEq (mkProg ListProg))
		(mkTriple (mkTrue tySasn) (mkCmd (calloc "x" "NodeC")) (mkFalse tySasn)).

Print alloc_lemma.

Eval vm_compute in runTac test_alloc.


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

Time Eval vm_compute in runTac testSkip.

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
Local Open Scope string.

Definition test_read := 
    mkExists tySasn tyProp
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cseq (cread "x" "o" "f") cskip))
  	                     (Var 0))).

Definition test_read2 :=
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cseq (cread "x" "o" "f") cskip))
  	                     (mkPointsto "o" "f" (mkConst tyVal (mkVal (vint 3)))))).

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
		  	           			    (mkPointsto "o" "f1" (mkConst tyVal (Var 1)))
		  	           			    (mkPointsto "o" "f2" (mkConst tyVal (Var 0))))
		  	           			 (mkCmd (cseq (cread "x1" "o" "f1")
  	                                          (cseq (cread "x2" "o" "f2")
  	                                                (cseq (cwrite "o" "f1" (E_var "x2"))
  	                                                      (cwrite "o" "f2" (E_var "x1"))))))
		  	           			 (mkStar tySasn 
		  	           			    (mkPointsto "o" "f1" (mkConst tyVal (Var 0)))
		  	           			    (mkPointsto "o" "f2" (mkConst tyVal (Var 1))))))).
						
Time Eval vm_compute in runTac testSwap.

