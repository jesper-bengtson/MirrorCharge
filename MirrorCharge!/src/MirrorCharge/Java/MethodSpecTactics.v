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
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.

Require Import MirrorCharge.Java.Syntax.
 
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
    	| mkEntails [l, mkProgEq [mkProg [P]], mkMethodSpec [C, m, mkVarList [args], r, p, q]] =>
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
						  	                      mkTriple [p, mkCmd [m_body Method], q]]
						  	                      (* Must add substitutions for the arguments here *)
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
 
Eval vm_compute in (test_lemma skip_lemma).
 
Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySasn ::  nil
 ; premises := nil
 ; concl := mkEntails [tySasn, Var 0, Var 0]
 |}.
 
Eval vm_compute in (test_lemma skip_lemma2).

Definition seq_lemma c1 c2 : lemma typ (expr typ func) (expr typ func) :=
	{| vars := tySpec :: tySasn :: tySasn :: tySasn :: nil;
	   premises := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [c1], Var 2]] ::
                   mkEntails [tySpec, Var 0, mkTriple [Var 2, mkCmd [c2] , Var 3]] :: nil;
       concl := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [cseq c1 c2], Var 3]]
    |}.

Eval vm_compute in (test_lemma skip_lemma2).


Definition assign_lemma x e : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn :: nil
 ; premises := nil
 ; concl := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [cassign x e], 
                       lexists tySasn tyVal (land tySasn (lembed tyPure tySasn
                                                                 (mkAp [tyVal, tyProp, 
                                                                        mkAp [tyVal, tyArr tyVal tyProp,
                                                                              mkConst [tyArr tyVal (tyArr tyVal tyProp), fEq [tyVal]],
                                                                              (App fstack_get (mkVar [x]))],
                                                                        lupdate tyVal (App (App fstack_set (mkVar [x])) (Var 0)) (App fEval (mkExpr [e]))]))
                                                         (lupdate tyAsn (App (App fstack_set (mkVar [x])) (Var 0)) (Var 1))) ]]
|}.

Definition write_lemma x f e : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn :: tySasn :: nil
 ; premises := mkEntails [tySasn, Var 1, lexists tySasn tyVal 
      											 (lstar tySasn (Var 3) 
                                                        (mkAp [tyVal, tyAsn,
                                                               mkAp [tyString, tyArr tyVal tyAsn,
                                                                     mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                                                           mkConst [tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)), fPointsto],
                                                                           App fstack_get (mkVar [x])],
                                                                     mkConst [tyString, mkString [f]]],
                                                               mkConst [tyVal, Var 0]]))] :: nil
 ; concl := mkEntails [tySpec, Var 0, 
                       mkTriple [Var 1, 
                                 mkCmd [cwrite x f e], 
                                 lstar tySasn (Var 2) 
                                       (mkAp [tyVal, tyAsn,
                                              mkAp [tyString, tyArr tyVal tyAsn,
                                                    mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                                          mkConst [tyArr tyVal 
                                                                         (tyArr tyString (tyArr tyVal tyAsn)), 
                                                                   fPointsto],
                                                          App fstack_get (mkVar [x])],
                                                    mkConst [tyString, mkString [f]]],
                                              App fEval (mkExpr [e])])
 ]]
     
 |}.

Definition read_lemma x y f : lemma typ (expr typ func) (expr typ func) :=
{| vars := tySpec :: tySasn :: tyExpr :: nil
 ; premises :=
     mkEntails [tySpec,
               Var 0,
               (mkAp [tyVal, tyAsn, 
                      mkAp [tyString, tyArr tyVal tyAsn,
                            mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                  mkConst [tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)), fPointsto],
                                  App fstack_get (mkVar [y])],
                            mkConst [tyString, mkString [f]]],
                      App fEval (Var 2)])] :: nil
 ; concl := mkEntails [tySpec,
                       Var 0,
                       mkTriple [Var 1, mkCmd [cread x y f], 
                       lexists tySasn tyVal (land tySasn (lembed tyPure tySasn
                                                                 (mkAp [tyVal, tyProp, 
                                                                        mkAp [tyVal, tyArr tyVal tyProp,
                                                                              mkConst [tyArr tyVal (tyArr tyVal tyProp), fEq [tyVal]],
                                                                              (App fstack_get (mkVar [x]))],
                                                                        lupdate tyVal (App (App fstack_set (mkVar [x])) (Var 0)) (App fEval (Var 3))]))
                                                         (lupdate tyAsn (App (App fstack_set (mkVar [x])) (Var 0)) (Var 1))) ]]
                                 
 |}.

Print cmd.

  Let EAPPLY :=
    @EAPPLY typ (expr typ func) subst _ Typ0_Prop
           vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ RS SS SU 3 nil
                         tus tvs n s e1 e2 t)
           (@instantiate typ func) SS SU.

  Let APPLY :=
    @APPLY typ (expr typ func) subst _ Typ0_Prop
           vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ RS SS SU 3 nil
                         tus tvs n s e1 e2 t)
           (@instantiate typ func) SS SU.

Fixpoint tripleE (c : cmd) : stac typ (expr typ func) subst :=
	match c with
	    | cskip => APPLY skip_lemma (apply_to_all (@IDTAC _ _ _))
		| cseq c1 c2 => EAPPLY (seq_lemma c1 c2) (apply_to_all (FIRST (tripleE c1::tripleE c2::nil)))
		| _ => @IDTAC _ _ _
	end.

Definition symE : stac typ (expr typ func) subst :=
	fun tus tvs s lst e => 
		match e with 
			| mkEntails [tySpec, G, mkTriple [P, mkCmd [c], Q]] => 
			  (tripleE c) tus tvs s lst e
			| _ => Fail _ _ _
		end.
	
Definition test_skip :=
  let uvars := nil in
  let vars := tySasn :: tySpec :: nil in
  let goal := mkEntails [tySpec, Var 1, mkTriple [Var 0, mkCmd [cskip], Var 0]]
  in
  let tac := symE in
  @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.
Time Eval vm_compute in test_skip.

Definition test_skip2 :=
  let uvars := nil in
  let vars := tySpec :: tySasn :: nil in
  let goal := mkEntails [tySpec, Var 0, mkTriple [Var 1, mkCmd [cseq (cseq cskip cskip) (cseq cskip cskip)], Var 1]]
  in
  let tac := symE in
  @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.
Time Eval vm_compute in test_skip2.


Fixpoint tripleE tus tvs (G P Q : expr typ func) l (c : cmd) s args : Result typ (expr typ func) subst :=
	match c with 
	  | cskip =>
	    match @exprUnify subst typ func _ _ RS SS SU 3 nil
                              tus tvs 0 s P Q tyAsn with
          | Some s => Solved _ tus tvs s
          | None   => Fail _ _ _
        end
	  | cseq c1 c2 => 
	    let i := S (length tus) in
	    match tripleE (tySpec::tus) tvs G P (UVar i) l c1 s args with
	      | Solved tus tvs s => 
	        match UVarMap.MAP.find i s with
	          | Some R => tripleE tus tvs G R Q l c2 s args
	          | None => Fail _ _ _
	        end
	      | _ => More nil nil s args (mkEntails [l, G, mkTriple [P, mkCmd [c], Q]])
	    end
	  | _ => More nil nil s args (mkEntails [l, G, mkTriple [P, mkCmd [c], Q]])
    end.
    
(** Sequence **)



Definition symE : stac typ (expr typ func) subst :=
	fun tus tvs s lst e => 
		match e with 
			| mkEntails [l, G, mkTriple [P, mkCmd [c], Q]] => 
			  tripleE tus tvs G P Q l c s lst
			| _ => Fail _ _ _
		end.

Require Import ExtLib.Tactics.
Require Import Lambda.ExprTac.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance SO.
Check @stac_sound.
Check REC.



Lemma symE_sound : @stac_sound typ (expr typ func) subst RType_typ Syntax.Expr_expr _ SS SO symE.
Proof.
  intros tus tvs s hs g WFs.
  remember (symE tus tvs s hs g).
  
  destruct r; [apply I | |].
  unfold symE in Heqr.
  forward; inv_all; subst.
  
  Lemma tripleE_Solved_WellFormed_subst : tus tvs G P Q l c s args tus' tvs' s' (H : tripleE tus tvs G P Q l c s args = Solved (expr typ func) tus' tvs' s') 
    (:
    wellFormedSubst s'.

  unfold goalD; simpl; red_exprD.
  split; [admit|]. forward.
  
  unfold symE in Heqr.
  forward; inv_all; subst.
  split; [admit|].
  unfold goalD. 
  forward; inv_all; subst.
  unfold typ0_cast. simpl.
  match goal with
	| |- match ?X with _ => _ end =>
          consider X; intros
  end.
  match goal with
	| |- match ?X with _ => _ end =>
          consider X; intros
  end.
  match goal with
	| |- match ?X with _ => _ end =>
          consider X; intros
  end.
  forward; inv_all; subst.
  simpl in WFs.
  
  Focus 3. generalize dependent l1.
  forward_reason.
  unfold SUBST.WellFormed in WFs.
  unfold SUBST.normalized in WFs.
simpl in *. 
  
  assert (ExprDsimul.ExprDenote.exprD' nil (tus ++ l) (tvs ++ l0) tyProp x = Some (fun _ _ => Prop)).
  red_exprD.
  assert (exists t, @exprD' typ RType_typ (expr typ func) Expr_expr (@app typ tus l)
      (@app typ tvs l0) e (@typ0 typ RType_typ Prop Typ0_Prop) = Some t) by admit.
  destruct H0 as [t' H0].    rewrite H0.
  simpl. red_exprD.
  assert (exists t, exprD' (tus ++ l) (tvs ++ l0) e (typ0 (F := Prop)) = Some t).
  simpl in *.
  induction c; simpl in H15; try (inversion H15; subst). 
  Check @app_nil_r typ tvs.
  Check @exprD'_weaken.
  destruct (@ExprFacts.exprD'_weaken typ RType_typ Typ2_Fun func _ _ _ _ _ _ _ nil tus tvs _ tyProp t nil nil H) as [t' [H3 H4]].
  simpl in *.
  simpl in *.
  rewrite H3.
  forward_reason.
  red.
  unfold ilfunc.
  rewrite H3.
  destruct (@ExprFacts.exprD'_weaken typ RType_typ _ (expr typ func) _ _ _ Expr_expr Expr_ok tus tvs _ tyProp t H nil nil) as [t' [H3 H4]].
  unfold ExprDsimul.ExprDenote.exprD'.
  SearchAbout exprD' List.app List.nil.
  pose
  Check exprD'_weaken.
  assert ( ExprDsimul.ExprDenote.exprD' nil (tus ++ nil) (tvs ++ nil) tyProp
      mkEntails  [logic, e3, mkTriple  [e9, mkCmd  [cassign v d], e5]] = Some t).
  forward_reason.
  rewrite <- (@app_nil_r typ) in H.
  replace tvs with (tvs ++ nil) in H by admit.
  replace(tvs ++ nil) with tvs by (symmetry; apply app_nil_r).
  rewrite app_nil_r.
  SearchAbout nil List.app.
  red_exprD; forward; inv_all; subst.
  destruct g; inv_all; subst.
  inversion Heqr; subst. simpl in *. red_exprD.
  SearchAbout exprD' nth_error_get_hlist_nth.
  unfold ExprDsimul.ExprDenote.exprD' in H.
  unfold Open_GetVAs in H. simpl in H. forward; inv_all; subst.
  red_exprD.
  progress simpl in *.
  
  simpl.
  
  forward.
  red_exprD.  
  simpl. unfold goalD. simpl.
  red_exprD. split. admit.
  forward. split. admit. forward.
  simp
  admit.
Qed.
  forward.
  
  simpl in *.
  unfold goalD.
  red_exprD.
  red_exprD.
  unfold mk_entails.
  SearchAbout stac.
  simpl in *.
  unfold symE. simpl.
  forward.
  forward_reason.
  unfold symE.
  forward_reason.
  destruct g. simpl.
  remember (goalD tus tvs (Var v)) as g.
  destruct g; [|tauto]. simpl in *.
  split; [tauto|].
  
  destruct (goalD tus tvs (Var v)); [|tauto].
  
  simpl.
  forward.
  unfold stac_sound.
  