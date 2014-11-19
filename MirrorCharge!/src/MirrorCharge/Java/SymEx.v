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

Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.RedAll.
Lemma FOLD_sound : rtac_sound FOLD.
Proof.
  unfold FOLD.
  apply SIMPLIFY_sound.
  intros; simpl.
  forward.
  (* beta_all_sound is missing *)
  admit.
Qed.

Definition BETA := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all (@apps typ func) nil nil).

Lemma BETA_sound : rtac_sound BETA.
Proof.
  unfold BETA.
  apply SIMPLIFY_sound.
  intros; simpl; forward.
  admit.
Qed.

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

Definition runTac rw := 
   (THEN (THEN (REPEAT 1000 (INTRO typ func)) (symE rw)) 
	(INSTANTIATE typ func)).
	
Lemma runTac_sound rw : rtac_sound (runTac rw).
Proof.
  admit.
Qed.

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
	Check triple.

Ltac solve_equation :=
	intros; repeat ((repeat eexists); try reflexivity).
	
Ltac cbv_denote e :=
          eval cbv [
          goalD_aux
          
		  (* ExprD' *)
          exprD' funcAs  typeof_sym typeof_func type_cast type_cast_typ
          exprD'_simul func_simul
          ExprD.Expr_expr
          ExprDsimul.ExprDenote.exprD'
          (* RSym *)
          
          SymSum.RSym_sum Rcast Relim Rsym eq_sym symD RSym_env
          Rcast_val eq_rect_r eq_rect Datatypes.id
          
          (* Monad *)
          
          Monad.bind Monad.ret
          
          OptionMonad.Monad_option
          
          (* HList *)
          
          HList.hlist_hd HList.hlist_tl
          
          (* TypesI *)
          
          TypesI.typD 
          typ2_match typ2 typ2_cast
          typ0_match typ0 typ0_cast
          (* ExprI *)
          
          MirrorCore.VariablesI.Var ExprVariables.ExprVar_expr
          MirrorCore.VariablesI.UVar
          MirrorCore.Lambda.ExprVariables.ExprUVar_expr
          ExprI.exprT_Inj ExprI.exprT_UseV ExprI.exprT_UseU
          exprT_App ExprI.exprT OpenT
          nth_error_get_hlist_nth
          
          exprT_GetVAs exprT_GetUAs
          
          (* ILogicFunc*)
          
          ILogicFunc.mkEntails ILogicFunc.mkTrue ILogicFunc.mkFalse 
          ILogicFunc.mkAnd ILogicFunc.mkOr ILogicFunc.mkImpl
          ILogicFunc.mkExists ILogicFunc.mkForall
          
          ILogicFunc.fEntails ILogicFunc.fTrue ILogicFunc.fFalse ILogicFunc.fAnd 
          ILogicFunc.fOr ILogicFunc.fImpl ILogicFunc.fExists ILogicFunc.fForall
          ILogicFuncSumL ILogicFuncSumR ILogicFuncExpr
          ILogicFunc.RSym_ilfunc 
          MirrorCharge.ModularFunc.ILogicFunc.ILogicFuncInst
          
          ILogicFunc.funcD ILogicFunc.typ2_cast_quant ILogicFunc.typ2_cast_bin
          
          (* BILogicFunc *)
          
          BILogicFunc.mkEmp BILogicFunc.mkStar BILogicFunc.mkWand
          
          BILogicFunc.fEmp BILogicFunc.fStar BILogicFunc.fWand
          
          BILogicFuncSumL BILogicFuncSumR BILogicFuncExpr
          BILogicFunc.RSym_bilfunc BILogicFunc.BILogicFuncInst
          
          BILogicFunc.funcD BILogicFunc.typ2_cast_bin
          
          BILogicFunc.typeof_bilfunc
          
          (* LaterFunc *)
          
          LaterFunc.mkLater
          
          LaterFunc.fLater
          
          LaterFunc.LaterFuncSumL LaterFunc.LaterFuncSumR LaterFunc.LaterFuncExpr          
          LaterFunc.RSym_later_func LaterFunc.LaterFuncInst
          
          LaterFunc.funcD LaterFunc.typ2_cast'
          
          LaterFunc.typeof_later_func
          
          (* EmbedFunc *)
          
          EmbedFunc.mkEmbed
          
          EmbedFunc.fEmbed
          
          EmbedFunc.EmbedFuncSumL EmbedFunc.EmbedFuncSumR EmbedFuncExpr
          EmbedFunc.RSym_embed_func EmbedFunc.EmbedFuncInst
          
          EmbedFunc.funcD EmbedFunc.typ2_cast_bin
          

          EmbedFunc.typeof_embed_func
          
          (* BaseFunc *)
          
          BaseFunc.BaseFuncSumL BaseFunc.BaseFuncSumR BaseFunc.BaseFuncExpr
          
          BaseFunc.BaseFuncInst
          BaseFunc.mkNat BaseFunc.mkString BaseFunc.mkBool
          BaseFunc.mkEq BaseFunc.mkPair
          
          BaseFunc.fNat BaseFunc.fString BaseFunc.fBool
          BaseFunc.fEq BaseFunc.fPair
          
          BaseFunc.RSym_BaseFunc
          
          BaseFunc.typeof_base_func BaseFunc.base_func_eq BaseFunc.base_func_symD
          BaseFunc.RelDec_base_func
          
          (* ListFunc *)
          
          ListFunc.ListFuncSumL ListFunc.ListFuncSumR ListFunc.ListFuncExpr
          
          ListFunc.ListFuncInst
          ListFunc.mkNil ListFunc.mkCons ListFunc.mkLength 
          ListFunc.mkZip ListFunc.mkMap ListFunc.mkFold
          
          ListFunc.fNil ListFunc.fCons ListFunc.fLength
          ListFunc.fZip ListFunc.fMap ListFunc.fFold
          
          ListFunc.typeof_list_func ListFunc.list_func_eq ListFunc.list_func_symD
          ListFunc.RelDec_list_func
          
		  (* OpenFunc *)
		  
		  OpenFunc.mkConst OpenFunc.mkAp OpenFunc.mkVar OpenFunc.mkNull OpenFunc.mkStackGet
		  OpenFunc.mkStackSet OpenFunc.mkApplySubst OpenFunc.mkSingleSubst OpenFunc.mkSubst
		  OpenFunc.mkTruncSubst
		    
		  OpenFunc.fConst OpenFunc.fAp OpenFunc.fVar OpenFunc.fNull OpenFunc.fStackGet
		  OpenFunc.fApplySubst OpenFunc.fSingleSubst OpenFunc.fSubst OpenFunc.fTruncSubst
		  
		  OpenFunc.OpenFuncSumL OpenFunc.OpenFuncSumR OpenFunc.OpenFuncExpr
		  OpenFunc.OpenFuncInst
		  
		  OpenFunc.typeof_open_func OpenFunc.RSym_OpenFunc
		  OpenFunc.typ2_cast_bin OpenFunc.typ3_cast_bin
		  OpenFunc.RelDec_open_func
		  
		  RSym_OpenFunc_obligation_1

          (* BaseType *)
          
          BaseType.tyPair BaseType.tyNat BaseType.tyString BaseType.tyBool
          BaseType.btPair BaseType.btNat BaseType.btBool BaseType.btString
          
          (* ListType *)
          
          ListType.tyList ListType.btList
          
          (* SubstType *)
          
          SubstType.tyVar SubstType.tyVal SubstType.tySubst
          SubstType.stSubst
          
          (* JavaType *)
         
          Typ2_Fun Typ0_Prop RType_typ typD
          should_not_be_necessary should_also_not_be_necessary
         
          JavaType.BaseType_typ JavaType.BaseTypeD_typ JavaType.ListType_typ
          JavaType.ListTypeD_typ JavaType.bilops JavaType.ilops
          JavaType.eops JavaType.lops
          
       (*   JavaType.typD *)
		 (* JavaFunc *)
          
          ilops is_pure func RSym_JavaFunc typeof_java_func java_func_eq
          java_func_symD RelDec_java_func
                   
          RSym_ilfunc RSym_open_func RSym_OpenFunc RSym_ListFunc
          JavaFunc.RSym_bilfunc JavaFunc.RSym_embed_func JavaFunc.RSym_later_func
          JavaFunc.RSym_ilfunc
          JavaFunc.Expr_expr
          mkPointstoVar
          
          JavaFunc.mkField JavaFunc.mkClass JavaFunc.mkVal JavaFunc.mkVarList
          JavaFunc.mkProg JavaFunc.mkCmd JavaFunc.mkDExpr JavaFunc.mkFields
          JavaFunc.fMethodSpec JavaFunc.fProgEq JavaFunc.fTriple JavaFunc.fTypeOf
          JavaFunc.fFieldLookup JavaFunc.fPointsto JavaFunc.mkNull
          JavaFunc.fPlus JavaFunc.fMinus JavaFunc.fTimes JavaFunc.fAnd
          JavaFunc.fOr JavaFunc.fNot JavaFunc.fLt JavaFunc.fValEq
          JavaFunc.mkTriple JavaFunc.mkFieldLookup JavaFunc.mkTypeOf
          JavaFunc.mkProgEq JavaFunc.mkExprList JavaFunc.evalDExpr
          
          (* Applicative *)
  (*        
          ExtLib.Structures.Applicative.ap ExtLib.Structures.Applicative.pure
 	      Applicative_Fun
          
          Charge.Logics.Pure.pure
    *)      
          SubstType_typ
          
          goalD propD exprD'_typ0 exprD split_env
          
          amap_substD
          substD
          SUBST.raw_substD
          UVarMap.MAP.fold
          FMapPositive.PositiveMap.fold
          FMapPositive.PositiveMap.xfoldi
          FMapPositive.append
          UVarMap.MAP.from_key
          pred
          plus
          Pos.to_nat
          Pos.iter_op
          app
          HList.hlist_app
          Quant._foralls
          Quant._exists
          ] in e.

Ltac run_rtac tac_sound :=
  match type of tac_sound with
    | rtac_sound ?tac =>
	  let name := fresh "e" in
	  match goal with
	    | |- ?P => 
	      reify_aux P name;
	      let t := eval vm_compute in (typeof_expr nil nil name) in
	      let goal := eval unfold name in name in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac tac (GGoal goal)) in 
	          let result := eval vm_compute in goal_result in 
	          match result with
	            | More_ ?s ?g =>
	              let Q := cbv_denote (goalD_aux nil nil g Hnil Hnil) in
	              match Q with
	                | Some ?Q' => 
	                  cut Q'; [
		              let P := cbv_denote (exprD nil nil goal tyProp) in 
		              pose (H1 := @eq_refl (option Prop) P <: 
		              	exprD nil nil goal tyProp = P);
		              pose (H2 := @eq_refl (Result (CTop nil nil)) result <: 
		              	run_tac tac (GGoal goal) = result)  ;
		              pose (H3 := @eq_refl (option Prop) Q <:
		              	goalD_aux nil nil g Hnil Hnil = Q);
		              exact (@run_rtac_More tac _ _ _ _ _ H1 H2 H3 tac_sound)|]
		            | None => idtac "Unable to find a denotation for" Q
		          end
	            | Solved ?s =>
	              let P := cbv_denote (exprD nil nil goal tyProp) in
	              let H1 := fresh "H" in
	              pose (H1 := @eq_refl (option Prop) P <:
	                exprD nil nil goal tyProp = P);
		          pose (H2 := @eq_refl (Result (CTop nil nil)) result <: 
		            run_tac tac (GGoal goal) = result);
	              exact (@run_rtac_Solved tac _ _ _ H1 H2 tac_sound)
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.

Definition testSkip n : Prop :=
  forall (G : spec) (P : sasn), G |-- triple P P (seq_skip n).


Lemma test_skip_lemma3 : testSkip 20.
Proof.
  unfold testSkip; simpl.
  Time run_rtac (@runTac_sound rw_fail).
  solve_equation.
Time Qed.

Definition test_alloc : expr typ func :=
	mkEntails tySpec (mkProgEq (mkProg ListProg))
		(mkTriple (mkTrue tySasn) (mkCmd (cseq (calloc "x" "NodeC") cskip)) (mkFalse tySasn)).


  
  Lemma test_alloc_correct : 
  prog_eq ListProg |-- triple ltrue lfalse ((calloc "x" "NodeC");;Skip).
Proof.

  Time run_rtac (@runTac_sound rw_fail).

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

