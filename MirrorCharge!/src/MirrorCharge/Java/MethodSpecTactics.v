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
						  	                      mkTriple [mkTruncSubst [tyAsn, p, mkSubstList [mkVarList [args], mkExprList [map E_var (m_params Method)]] ], mkCmd [m_body Method], 
						  	                               mkTruncSubst [tyAsn, q, mkSubstList [mkVarList [r::args], mkConsExprList [App fEval (mkExpr [m_ret Method]), mkExprList[map E_var (m_params Method)]]] ]]]
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

Definition skip_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn ::  nil
 ; premises := nil
 ; concl := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [cskip], Var 1]]
 |}.
 
Check test_lemma.
 (* 
Time Eval compute in (test_lemma skip_lemma).
 *)
Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySasn ::  nil
 ; premises := nil
 ; concl := mkEntails [tySasn, Var 0, Var 0]
 |}.
 (*
Eval vm_compute in (test_lemma skip_lemma2).
*)
Definition seq_lemma c1 c2 : lemma typ (expr typ func) (expr typ func) :=
	{| vars := tySpec :: tySasn :: tySasn :: tySasn :: nil;
	   premises := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [c1], Var 2]] ::
                   mkEntails [tySpec, Var 0, mkTriple [Var 2, mkCmd [c2] , Var 3]] :: nil;
       concl := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [cseq c1 c2], Var 3]]
    |}.

Example skip_test c1 c2 : test_lemma (seq_lemma c1 c2). admit.

Definition assign_lemma x e : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn :: (tyArr (tyArr tyString tyVal) tyVal) :: tyString :: nil
 ; premises := nil
 ; concl := mkEntails [tySpec, Var 0, 
                       mkTriple [Var 1,
                                 mkCmd [cassign x e], 
                                 mkExists [tySasn, tyVal, 
                                         mkAnd [tySasn,
                                               lembed tyPure tySasn 
                                                       (mkAp [tyVal, tyProp, 
                                                             mkAp [tyVal, tyArr tyVal tyProp,
                                                                  mkConst [tyArr tyVal (tyArr tyVal tyProp), fEq [tyVal]],
                                                                  App fstack_get (mkString [x])],
                                                             mkSingleSubst [tyVal, App fEval (mkExpr [e]), mkString [x], mkConst[tyVal, Var 0]]]),
                                               mkSingleSubst [tyAsn, Var 2, mkString [x], mkConst[tyVal, Var 0]]]]]]
|}.

Example assign_test x e : test_lemma (assign_lemma x e).
Proof.
  admit.
Qed.

Definition write_lemma x f e : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn :: tySasn :: nil
 ; premises := mkEntails [tySasn, Var 1, mkExists [tySasn, tyVal, 
      											   mkStar [tySasn, 
      											           Var 3, 
                                                           mkAp [tyVal, tyAsn,
                                                                 mkAp [tyString, tyArr tyVal tyAsn,
                                                                       mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                                                             mkConst [tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)), fPointsto],
                                                                             App fstack_get (mkString [x])],
                                                                      mkConst [tyString, mkString [f]]],
                                                                mkConst [tyVal, Var 0]]]]] :: nil
 ; concl := mkEntails [tySpec, Var 0, 
                       mkTriple [Var 1, 
                                 mkCmd [cwrite x f e], 
                                 mkStar [tySasn, Var 2, 
                                       mkAp [tyVal, tyAsn,
                                              mkAp [tyString, tyArr tyVal tyAsn,
                                                    mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                                          mkConst [tyArr tyVal 
                                                                         (tyArr tyString (tyArr tyVal tyAsn)), 
                                                                   fPointsto],
                                                          App fstack_get (mkString [x])],
                                                    mkConst [tyString, mkString [f]]],
                                              App fEval (mkExpr [e])]]]]
     
 |}.

Example write_test x f e : test_lemma (write_lemma x f e).
Proof.
  admit.
Qed.

Definition read_lemma x y f : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn :: tyExpr :: nil
 ; premises :=
     mkEntails [tySasn,
               Var 1,
               (mkAp [tyVal, tyAsn, 
                      mkAp [tyString, tyArr tyVal tyAsn,
                            mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                  mkConst [tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)), fPointsto],
                                  App fstack_get (mkString [y])],
                            mkConst [tyString, mkString [f]]],
                      App fEval (Var 2)])] :: nil
 ; concl := mkEntails [tySpec,
                       Var 0,
                       mkTriple [Var 1, mkCmd [cread x y f], 
                       mkExists [tySasn, tyVal, mkAnd [tySasn, lembed tyPure tySasn
                                                                 (mkAp [tyVal, tyProp, 
                                                                        mkAp [tyVal, tyArr tyVal tyProp,
                                                                              mkConst [tyArr tyVal (tyArr tyVal tyProp), fEq [tyVal]],
                                                                              (App fstack_get (mkString [x]))],
                                                                        mkSingleSubst[tyVal, App fEval (Var 3), mkString [x], mkConst[tyVal, Var 0]]]),
														 mkSingleSubst[tyAsn, Var 2, mkString [x], mkConst[tyVal, Var 0]]]]]]
                                 
 |}.

Example read_test x y e : test_lemma (read_lemma x y e).
Proof.
   admit.
Qed.

Definition fieldLookupTac : stac typ (expr typ func) subst :=
	fun tus tvs s lst e =>
		match e with
		  | mkFieldLookup [mkProg [P], mkString [C], X] =>
		  	match SM.find C (p_classes P) with
    	      | Some Class =>
    	        match @exprUnify subst typ func _ _ RS SS SU 3 nil
                                 tus tvs 0 s X (mkFields[c_fields Class]) tyVarList with
                  | Some s => Solved nil nil s
                  | None   => Fail
                end
    	      | None => Fail 
		    end
		  | _ => Fail
		end.

Definition alloc_lemma x C : lemma typ (expr typ func) (expr typ func) :=
  {|
     vars := tySpec :: tySasn :: tyProg :: tyFields :: nil;
     premises := mkEntails [tySpec, Var 0, mkProgEq [Var 2]] :: 
                 mkFieldLookup [Var 2, mkString [C], Var 3] :: nil;
     concl := mkEntails [tySpec, Var 0,
                         mkTriple [Var 1, mkCmd [calloc x C], 
                                   mkExists[tySasn, tyVal,
                                           mkSetFold [mkString [x], Var 4, 
                                                      mkSingleSubst[tyAsn, Var 2, mkString [x], mkConst[tyVal, Var 0]]]]]]
  |}.

Example alloc_test x C : test_lemma (alloc_lemma x C).
Proof.
	admit.
Qed.

Definition dcall_lemma x (y : var) m es : lemma typ (expr typ func) (expr typ func) :=
  {|
     vars := tySpec :: tySasn :: tyString :: tyVarList :: tyString :: tySasn :: tySasn :: tySasn :: nil;
     premises := mkEntails [tySasn, Var 1, lembed tyPure tySasn 
                                                  (mkAp [tyVal, tyProp, 
                                                   mkAp [tyString, tyArr tyVal tyProp,
                                                         mkConst [tyArr tyString (tyArr tyVal tyProp), fTypeOf],
                                                         mkConst [tyString, Var 2]],
                                                   (App fstack_get (mkString [y]))])] :: 
                mkEntails [tySpec, Var 0, mkMethodSpec [Var 2, mkString [m], Var 3, Var 4, Var 5, Var 6]] ::
                mkEq [tyNat, mkLengthVarList [Var 3], mkExprList [(E_var y)::es]] ::
                mkEntails [tyAsn, Var 1, mkStar [tySasn, mkSubst [tyAsn, Var 5, mkSubstList [Var 3, mkExprList [(E_var y)::es]]], Var 7]] ::
                nil ;
     concl := mkEntails [tySpec, Var 0, 
                         mkTriple [Var 1, mkCmd [cdcall x y m es], 
                                   mkExists [tySasn, tyVal, 
                                           mkAnd [tySasn, lembed tyPure tySasn 
                                                  (mkAp [tyVal, tyProp, 
                                                   mkAp [tyString, tyArr tyVal tyProp,
                                                         mkConst [tyArr tyString (tyArr tyVal tyProp), fTypeOf],
                                                         mkConst [tyString, Var 3]],
                                                   mkSingleSubst [tyVal, App fstack_get (mkString [y]), mkString [x], mkConst[tyVal, Var 0]]]),
                                           mkStar [tySasn,
                                           mkSubst [tyAsn, Var 7, 
                                                    mkSubstList [mkConsVarList[Var 5, Var 4], 
                                                                mkConsExprList [App fstack_get (mkString [x]), 
                                                                                mkConsExprList [mkSingleSubst [tyVal, App fstack_get (mkString [y]), mkString [x], mkConst [tyVal, Var 0]],
                                                                                                mkSubstExprList [es, mkString [x], mkConst[tyVal, Var 0]]]]]],
                                           mkSingleSubst[tyAsn, Var 8, mkString [x], mkConst[tyVal, Var 0]]]]]]]
  |}.

Example dcall_test x y m es : test_lemma (dcall_lemma x y m es).
Proof.
   admit.
Qed.

Definition scall_lemma x (C : class) m es : lemma typ (expr typ func) (expr typ func) :=
  {|
     vars := tySpec :: tySasn :: tyVarList :: tyString :: tySasn :: tySasn :: tySasn :: nil;
     premises := mkEntails [tySpec, Var 0, mkMethodSpec [mkString [C], mkString [m], Var 2, Var 3, Var 4, Var 5]] ::
                 mkEq [tyNat, mkLengthVarList [Var 3], mkExprList [es]] ::
                 mkEntails [tyAsn, Var 1, mkStar [tySasn, mkSubst [tyAsn, Var 4, mkSubstList [Var 2, mkExprList [es]]], Var 6]] ::
                 nil ;
     concl := mkEntails [tySpec, Var 0, 
                         mkTriple [Var 1, mkCmd [cscall x C m es], 
                                   mkExists [tySasn, tyVal, 
                                           mkStar [tySasn,
                                           mkSubst [tyAsn, Var 6, 
                                                    mkSubstList [mkConsVarList[Var 5, Var 4], 
                                                                mkConsExprList [App fstack_get (mkString [x]), 
                                                                                mkSubstExprList [es, mkString [x], mkConst[tyVal, Var 0]]]]],
                                           mkSingleSubst[tyAsn, Var 7, mkString [x], mkConst[tyVal, Var 0]]]]]]
  |}.

Example scall_test x C m es : test_lemma (scall_lemma x C m es).
Proof.
   admit.
Qed.

Definition solve_entailment :=
  THEN (SIMPLIFY (fun _ _ _ => beta_all simplify nil nil))
       stac_cancel.

Let EAPPLY lem tac :=
  @EAPPLY typ (expr typ func) subst _ _ ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3 nil
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func) SS SU
                lem (apply_to_all tac).

  Let APPLY :=
    @APPLY typ (expr typ func) subst _ Typ0_Prop
           ExprLift.vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ RS SS SU 3 nil
                         tus tvs n s e1 e2 t)
           (@ExprSubst.instantiate typ func) SS SU.
Locate apply_to_all.
Check EAPPLY.
Check APPLY.
Fixpoint tripleE (c : cmd) : stac typ (expr typ func) subst :=
	match c with
	    | cskip => APPLY skip_lemma (apply_to_all (@IDTAC _ _ _))
		| cseq c1 c2 => EAPPLY (seq_lemma c1 c2) (apply_to_all (FIRST (tripleE c1::tripleE c2::nil)))
		| cassign x e => EAPPLY (assign_lemma x e) (apply_to_all (@IDTAC _ _ _))
		| cread x y f => EAPPLY (read_lemma x y f) (apply_to_all (@IDTAC _ _ _))
		| cwrite x f e => EAPPLY (write_lemma x f e) (apply_to_all (@IDTAC _ _ _))
		| _ => @IDTAC _ _ _
	end.

Definition symE : stac typ (expr typ func) subst :=
	fun tus tvs s lst e => 
		match e with 
			| mkEntails [tySpec, G, mkTriple [P, mkCmd [c], Q]] => 
			  (tripleE c) tus tvs s lst e
			| _ => Fail
		end.  

Definition testSkip :=
  let vars := tySpec :: tySasn :: nil in
  let goal :=
      mkEntails [tySpec, Var 0,
                 mkTriple [Var 0, mkCmd [cseq cskip (cseq cskip cskip)], Var 0]]
  in
  @symE nil vars (SubstI.empty (expr :=expr typ func)) nil goal.
  
Time Eval vm_compute in testSkip.

