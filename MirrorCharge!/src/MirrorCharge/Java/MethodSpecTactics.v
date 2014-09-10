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

Require Import MirrorCore.Reify.Reify.

Require Import MirrorCharge.Java.Reify.

(*
Require Import MirrorCharge.Java.Subst.
*)

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
Require Import Semantics.
  
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

Definition pull_exists_lemma : lemma typ (expr typ func) (expr typ func) :=
{|
   vars := tySpec :: tyArr tyVal tySasn :: tyCmd :: tySasn :: nil
 ; premises :=  mkEntails [tySpec, Var 0, mkForall [tySpec, tyVal, mkTriple [App (Var 2) (Var 0), Var 3, Var 4]]] :: nil 
 ; concl := mkEntails [tySpec, Var 0, mkTriple [mkExists [tySasn, tyVal, App (Var 2) (Var 0)], Var 2, Var 3]]
|}.

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

Let EAPPLY lem tac :=
  @EAPPLY typ (expr typ func) subst _ _ ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3 nil
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func) SS SU
                lem (apply_to_all tac).

  Let APPLY lem tac :=
    @APPLY typ (expr typ func) subst _ Typ0_Prop
           ExprLift.vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ RS SS SU 3 nil
                         tus tvs n s e1 e2 t)
           (@ExprSubst.instantiate typ func) SS SU
           lem (apply_to_all tac).

Require Import MirrorCharge.Java.Subst.
Check @INSTANTIATE.
Let INSTANTIATE := 
	@INSTANTIATE typ (expr typ func) subst (@ExprSubst.instantiate typ func) SS.

Definition solve_entailment :=
  THEN (TRY (APPLY pull_exists_lemma (@IDTAC _ _ _)))
       (THEN INSTANTIATE (THEN
             (SIMPLIFY (fun _ _ _ => beta_all simplify nil nil))
                        stac_cancel)).

Fixpoint tripleE (c : cmd) : stac typ (expr typ func) subst :=
	match c with
	    | cskip => EAPPLY skip_lemma solve_entailment
		| cseq c1 c2 => EAPPLY (seq_lemma c1 c2) (FIRST (tripleE c1::tripleE c2::nil))
		| cassign x e => EAPPLY (assign_lemma x e) solve_entailment
		| cread x y f => EAPPLY (read_lemma x y f) solve_entailment
		| cwrite x f e => EAPPLY (write_lemma x f e) solve_entailment
		| _ => @IDTAC _ _ _
	end.

Definition symE : stac typ (expr typ func) subst :=
	fun tus tvs s lst e => 
		match e with 
			| mkEntails [tySpec, G, mkTriple [P, mkCmd [c], Q]] => 
			  (tripleE c) tus tvs s lst e 
			| _ => Fail
		end.  
		
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.

Require Import Charge.Logics.ILogic.

Definition testSkip :=
  let vars := tySpec :: tySasn :: nil in
  let goal :=
      mkEntails [tySpec, Var 0,
                 mkTriple [Var 1, mkCmd [cskip], Var 1]]
  in
  @symE nil vars (SubstI.empty (expr :=expr typ func)) nil goal.
  
Time Eval vm_compute in testSkip.

Definition mkPointsto x f e : expr typ func :=
(mkAp [tyVal, tyAsn, 
                      mkAp [tyString, tyArr tyVal tyAsn,
                            mkAp [tyVal, tyArr tyString (tyArr tyVal tyAsn),
                                  mkConst [tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)), fPointsto],
                                  App fStackGet (mkString [x])],
                            mkConst [tyString, mkString [f]]],
                      e]).

Require Import String.
Open Scope string.

Definition test_read :=
  let uvars := tySasn :: nil in
  let vars := nil in
  let goal :=
  	mkEntails [tySpec, mkTrue [tySpec], 
  	           mkTriple [mkStar [tySasn, 
  	                             mkPointsto "o1" "f1" (mkConst [tyVal, mkVal [vint 3]]),
  	                             mkPointsto "o" "f" (mkConst [tyVal, mkVal [vint 4]])],
  	                     mkCmd [cseq (cread "x" "o" "f") cskip],
  	                     UVar 0]]
  in
  @symE uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.
 
Time Eval vm_compute  in test_read.

Definition testWrite :=
  let uvars := tySasn :: nil in
  let vars := nil in
  let goal :=
  	mkEntails [tySpec, mkTrue [tySpec], 
  	           mkTriple [mkStar [tySasn, mkEmp [tySasn], mkPointsto "o" "f" (mkConst [tyVal, mkVal [vint 3]])],
  	                     mkCmd [cwrite "o" "f" (E_val (vint 0))],
  	                     (UVar 0)]]
  in
  @symE uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.
Time Eval vm_compute  in testWrite.

Definition testSwap :=
  let uvars := tySasn :: nil in
  let vars := nil in
  let goal := mkEntails [tySpec, mkTrue [tySpec],
  	                     mkTriple [mkStar [tySasn,
  		                                   mkPointsto "o" "f1" (mkConst [tyVal, mkVal [vint 1]]),
	  	                                   mkPointsto "o" "f2" (mkConst [tyVal, mkVal [vint 2]])],                                           	                      
  	                               mkCmd [cseq (cread "x1" "o" "f1")
  	                                           (cread "x2" "o" "f2")
  	                               (*       (cseq (cwrite "o" "f1" (E_var "x2"))
  	                                            (cwrite "o" "f2" (E_var "x1")))) *) ], 
			                       UVar 0
			                       (*mkStar [tySasn,
			                               mkPointsto "o" "f1" (App fEval (Var 1)),
			                               mkPointsto "o" "f2" (App fEval (Var 0))*)]]                                     
  in
  let tac := symE in
  @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.
  
Time Eval vm_compute in testSwap.
