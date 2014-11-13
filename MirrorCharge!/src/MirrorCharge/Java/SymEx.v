Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Lemma. 
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
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
Require Import MirrorCore.Lambda.ExprVariables.
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
Check THEN.
Check runOnGoals.
Time Eval vm_compute in 
	(THEN (REPEAT 10 (INTRO typ func)) 
	(runOnGoals (CANCELLATION typ func tySasn is_pure))) 
		nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) (cancelTest 10).

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
Example test_alloc_lemma x C : test_lemma (alloc_lemma x C). Admitted.

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@pull_exists val).
Defined.
Example test_pull_exists_lemma : test_lemma pull_exists_lemma. Admitted.
Eval vm_compute in pull_exists_lemma.

Definition ent_exists_right_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp (@ent_left_exists val).
Defined.
Example test_pull_exists_lemma2 : test_lemma ent_exists_right_lemma. Admitted.

Definition eq_to_subst_lemma : lemma typ (expr typ func) (expr typ func).
Proof.
  reify_lemma reify_imp eq_to_subst.
Defined.
Eval vm_compute in eq_to_subst_lemma.
Example test_eq_lemma : test_lemma (eq_to_subst_lemma). Admitted.

Print pull_exists_lemma.

Example test_pull_exists : test_lemma (pull_exists_lemma). Admitted.

Definition fieldLookupTac : rtac typ (expr typ func) :=
	fun tus tvs n m c s e =>
		match e with
		  | App (App (App (Inj (inr pFieldLookup)) (Inj (inr (pProg P)))) (Inj (inr (pClass C)))) f =>
		  	match class_lookup C P with
    	      | Some Class =>
    	        match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 s f (mkFields (c_fields Class)) tyVarList with
                  | Some s => Solved s
                  | None   => Fail
                end
    	      | None => Fail 
		    end
		  | _ => Fail
		end.

Definition FIELD_LOOKUP := fieldLookupTac.

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

	Definition FOLD := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all foldTac nil nil).

Definition BETA := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all (@apps typ func) nil nil).

Definition THEN (r1 r2 : rtac typ (expr typ func)) := THEN r1 (runOnGoals r2).

Definition EQSUBST := THEN (THEN (APPLY typ func eq_to_subst_lemma) 
	(INSTANTIATE typ func)) (SUBST typ func).
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

Definition PULLEQL := PULLCONJUNCTL typ func match_ap_eq ilops.

                        (*
	THEN (INSTANTIATE typ func subst) (runOnGoals (THEN (THEN (TRY FIELD_LOOKUP) 
		(runOnGoals (CANCELLATION typ func subst tySpec (fun _ => false)))) (runOnGoals FOLD))) ::
		solve_entailment :: nil).
	           *)
Require Import MirrorCharge.AutoSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.

  Definition spec_respects (e : expr typ func) (_ : list (RG (expr typ func)))
	   (rg : RG (expr typ func)) : m (expr typ func) :=
	   match e with
	     | Inj (inr pTriple) =>
	       rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg
	         (RGrespects (RGflip (RGinj (fEntails tySasn)))
	           (RGrespects (RGinj (fEq tyCmd))
	             (RGrespects (RGinj (fEntails tySasn))
	               (RGinj (fEntails tySpec))))))
	         (fun _ => rg_ret fTriple)
	     | _ => rg_fail
	   end.

Definition step_unfold vars rw :=
  setoid_rewrite vars _ (fEntails : typ -> expr typ func) rw
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ func _ _ _ ilops _ _)
                                        (sr_combine bil_respects
                                                    (sr_combine eq_respects 
                                                    (sr_combine spec_respects refl)))))
    (fun _ => rw_fail).
    
  Definition STEP_REWRITE rw : rtac typ (expr typ func) :=
    fun tus tvs lus lvs c s e =>
      match step_unfold (getVars c) rw tyProp e with
        | Some (e', _) => More s (GGoal e')
        | _ => More s (GGoal e)
      end.

Definition PULL_TRIPLE_EXISTS : rtac typ (expr typ func) :=
  THEN (THEN (THEN (APPLY typ func pull_exists_lemma) (INTRO typ func)) (INSTANTIATE typ func)) BETA.

Definition solve_entailment (rw : rewriter (typ := typ) (func := func)) : rtac typ (expr typ func) :=
	THEN (INSTANTIATE typ func) 
		(FIRST (SOLVE (CANCELLATION typ func tySasn is_pure) ::
	           (THEN (THEN (THEN (THEN PULLEQL (REPEAT 1000 EQSUBST)) 
	           (STEP_REWRITE rw)) (REPEAT 1000 (INTRO typ func))) 
	              (CANCELLATION typ func tySasn is_pure)::
	           nil))).

Definition solve_alloc rw : rtac typ (expr typ func) :=
    THEN (INSTANTIATE typ func)
    (FIRST (SOLVE (CANCELLATION typ func tySpec (fun _ => false)) ::
                        FIELD_LOOKUP ::
                        THEN FOLD (solve_entailment rw) :: nil)).


Definition simStep (rw : rewriter (typ := typ) (func := func)) (r : rtac typ (expr typ func)) :=
    THEN (THEN (THEN (THEN (THEN (INSTANTIATE typ func) (SUBST typ func))
    	(TRY PULL_TRIPLE_EXISTS)) (STEP_REWRITE rw)) (REPEAT 10 PULL_TRIPLE_EXISTS)) r.

Set Printing Depth 100.

Print alloc_lemma.

Print runOnGoals.

Fixpoint tripleE (c : cmd) rw : rtac typ (expr typ func) :=
	match c with
	    | cskip => simStep rw (THEN (APPLY typ func skip_lemma) 
	                 (solve_entailment rw))
	    | calloc x C => simStep rw (THEN (EAPPLY typ func (alloc_lemma x C)) 
	    	(FIRST (solve_alloc rw :: solve_entailment rw :: nil)))
		| cseq c1 c2 => simStep rw (THEN (EAPPLY typ func (seq_lemma c1 c2))
						              (FIRST ((fun x => tripleE c1 rw x)::(fun x => tripleE c2 rw x)::nil)))
		| cassign x e => simStep rw (THEN (EAPPLY typ func (assign_lemma x e)) (solve_entailment rw))
		| cread x y f => simStep rw (THEN (EAPPLY typ func (read_lemma x y f)) (solve_entailment rw))
		| cwrite x f e => simStep rw (THEN (EAPPLY typ func (write_lemma x f e)) (solve_entailment rw))
		| _ => IDTAC
	end.

Definition symE rw : rtac typ (expr typ func) :=
	(fun tus tvs n m ctx s e => 
		(match e return rtac typ (expr typ func) with 
			| App (App (Inj f) G) H =>
			  match ilogicS f, H with
			  	| Some (ilf_entails tySpec), (* tySpec is a pattern, should be checked for equality with tySpec *)
			  	  App (App (App (Inj (inr pTriple)) P) Q) (Inj (inr (pCmd c))) =>
			  	  	tripleE c rw
			  	| _, _ => FAIL
			  end
			| _ => FAIL
		end) tus tvs n m ctx s e).  

Definition runTac (tac : expr typ func) rw := 
   (THEN (THEN (REPEAT 1000 (INTRO typ func)) (symE rw)) 
	(INSTANTIATE typ func))
	 nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) tac.

Eval vm_compute in 
  BETA nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func))
  	(App (Abs tySasn (mkAnd tySasn (Var 0) (mkTrue tySasn))) (mkTrue tySasn)).

Definition mkPointsto (x : expr typ func) (f : field) (e : expr typ func) : expr typ func :=
   mkAp tyVal tyAsn 
        (mkAp tyField (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyField (tyArr tyVal tyAsn))
                    (mkConst (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))) 
                             fPointsto)
                    x)
              (mkConst tyField (mkField f)))
        e.
        
Definition mkPointstoVar x f e : expr typ func :=
   mkAp tyVal tyAsn 
        (mkAp tyField (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyField (tyArr tyVal tyAsn))
                    (mkConst (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))) 
                             fPointsto)
                    (App fStackGet (mkVar x)))
              (mkConst tyField (mkField f)))
        e.
        
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

Fixpoint seq_skip n := 
	match n with
	  | 0 => cskip
	  | S n => cseq cskip (seq_skip n)
	end.
	
Definition testSkip n : expr typ func := 
      mkForall tySpec tyProp
      (mkForall tySasn tyProp
                (mkEntails tySpec (Var 1)
                (mkTriple (Var 0) (mkCmd (seq_skip n)) (Var 0)))).
Time Eval vm_compute in typeof_expr nil nil (testSkip 5).

Time Eval vm_compute in runTac (testSkip 10) rw_fail.

Definition test_alloc : expr typ func :=
	mkEntails tySpec (mkProgEq (mkProg ListProg))
		(mkTriple (mkTrue tySasn) (mkCmd (cseq (calloc "x" "NodeC") cskip)) (mkFalse tySasn)).

Eval vm_compute in runTac test_alloc rw_fail.

Definition runTac2 (tac : expr typ func) rw := 
   (THEN (THEN (THEN (THEN (REPEAT 1000 (INTRO typ func)) (symE rw)) 
	(INSTANTIATE typ func)) BETA) (CANCELLATION typ func tySasn is_pure))
	 nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) tac.
Check @App.
Definition test_read : expr typ func := 
    mkExists tySasn tyProp
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointstoVar "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cseq (cread "x" "o" "f") cskip))
  	                     (Var 0))).

Eval vm_compute in (CANCELLATION typ func tySasn is_pure) nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func))
  (mkEntails tySasn (mkTrue tySasn) (mkTrue tySasn)).
  


Definition test_read2 :=
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointstoVar "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cseq (cread "x" "o" "f") cskip))
  	                     (mkPointstoVar "o" "f" (mkConst tyVal (mkVal (vint 3)))))).
Time Eval vm_compute in runTac test_read rw_fail.
Check instantiate.

Time Eval vm_compute in runTac test_read2 rw_fail.





Definition test_write :=
  	(mkEntails tySpec (mkTrue tySpec)
  	           (mkTriple (mkPointstoVar "o" "f" (mkConst tyVal (mkVal (vint 3))))
  	                     (mkCmd (cwrite "o" "f" (E_val (vint 4))))
  	                     (mkPointstoVar "o" "f" (mkConst tyVal (mkVal (vint 4)))))).

Time Eval vm_compute in runTac test_write rw_fail.

Definition testSwap :=
	mkForall tyVal tyProp
		(mkForall tyVal tyProp
		  	(mkEntails tySpec (mkTrue tySpec)
		  	           (mkTriple (mkStar tySasn (mkStar tySasn 
		  	           			    (mkPointstoVar "o" "f1" (mkConst tyVal (Var 1)))
		  	           			    (mkPointstoVar "o" "f0" (mkConst tyVal (Var 0)))) (mkEmp tySasn))
		  	           			 (mkCmd (cseq (cread "x0" "o" "f0")
  	                                          (cseq (cread "x1" "o" "f1")
  	                                                (cseq (cwrite "o" "f1" (E_var "x0"))
  	                                                      (cseq (cwrite "o" "f0" (E_var "x1")) cskip)))))
		  	           			 (mkStar tySasn (mkStar tySasn 
		  	           			    (mkPointstoVar "o" "f1" (mkConst tyVal (Var 0)))
		  	           			    (mkPointstoVar "o" "f0" (mkConst tyVal (Var 1)))) (mkEmp tySasn))))).
SearchAbout string nat.

Fixpoint mkPre n :=
	match n with
	  | 0   => mkEmp tySasn
	  | S n => mkStar tySasn (mkPointstoVar "o" (append "f" (nat2string10 n)) (mkConst tyVal (Var n)))
	                         (mkPre n)
	end.
	
Fixpoint mkPostAux n m :=
  match n with
    | 0 => mkEmp tySasn
    | S n => mkStar tySasn (mkPointstoVar "o" (append "f" (nat2string10 n)) (mkConst tyVal (Var (m - (S n)))))
                           (mkPostAux n m)
  end.
  
Definition mkPost n := mkPostAux n n.

Fixpoint mkRead n c :=
	match n with
	  | 0 => c
	  | S n => cseq (cread (append "x" (nat2string10 n)) "o" (append "f" (nat2string10 n)))
	                (mkRead n c)
    end.
						
Fixpoint mkWriteAux n m c :=
	match n with
	  | 0 => c
	  | S n => cseq (cwrite "o" (append "f" (nat2string10 n)) (E_var (append "x" (nat2string10 (m - (S n))))))
	                (mkWriteAux n m c)
    end.

Definition mkWrite n c := mkWriteAux n n c.

Fixpoint mkSwapAux n P c Q :=
	match n with
	  | 0 => (mkEntails tySpec (mkTrue tySpec) (mkTriple P c Q))
	  | S n => mkForall tyVal tyProp (mkSwapAux n P c Q)
	end.

Definition mkSwapProg n c := mkRead n (mkWrite n c).
	
Definition mkSwap n :=
	mkSwapAux n (mkPre n) (mkCmd (mkSwapProg n cskip)) (mkPost n).

Definition mkSwapFalse n :=
	mkSwapAux n (mkPre n) (mkCmd (mkSwapProg n cskip))(* (mkFalse tySasn).*).

Time Eval vm_compute in (mkCmd (mkSwapProg 2 (mkSwapProg 2 cskip))).


Definition mkSwap2 n :=
	mkSwapAux n (mkPre n) (mkCmd (mkSwapProg n (mkSwapProg n cskip)))(* (mkPre n).*).
Eval vm_compute in mkSwap 5.
Check EAPPLY.
Time Eval vm_compute in runTac (mkSwap 4) rw_fail.

Time Eval vm_compute in 
	match (runTac (mkSwap 20) rw_fail) with
		| More_ _ g => 
		  Some (match goalD nil nil g with
		          | Some _ => true
		          | _ => false
		        end
		       )
		| _ => None
	end.

