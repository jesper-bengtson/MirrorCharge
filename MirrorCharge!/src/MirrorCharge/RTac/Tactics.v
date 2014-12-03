Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Subst.FMapSubst.

Require Import MirrorCharge.Java.JavaFunc.
Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.LaterFunc.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ListFunc.
Require Import MirrorCharge.ModularFunc.OpenFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Require Import Charge.Open.Stack.
Require Import Charge.Open.Subst.
Require Import Charge.Open.OpenILogic.

Require Import Charge.Logics.BILogic.
Require Import Charge.Logics.Later.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.
Require Import Java.Semantics.OperationalSemantics.

Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.

Require Import Coq.PArith.BinPos.

Definition exprD_Prop (uvar_env var_env : env) e :=
  match exprD uvar_env var_env e tyProp with
    | Some e' => e' 
    | None => True
  end.

Definition goalD_Prop (uvar_env var_env : env) goal :=
  let (tus, us) := split_env uvar_env in
  let (tvs, vs) := split_env var_env in
  match goalD tus tvs goal with
    | Some e => e us vs
    | None => False
  end.

Definition goalD_aux tus tvs goal (us : HList.hlist typD tus) (vs : HList.hlist typD tvs) :=
  match goalD tus tvs goal with
    | Some e => Some (e us vs)
    | None => None
  end.
    
Ltac cbv_denote :=
          cbv [
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
          typ0_match typ0 typ0_cast SubstTypeD_typ
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
          
(* OTHER *)
  
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
          goalD_Prop
          ].

Definition run_tac tac goal :=
  runOnGoals tac nil nil 0 0 (CTop nil nil) 
    (ctx_empty (typ := typ) (expr := expr typ func)) goal.

Lemma run_rtac_More tac s goal e
  (Hsound : rtac_sound tac) 
  (Hres : run_tac tac (GGoal e) = More_ s goal) :
  goalD_Prop nil nil goal -> exprD_Prop nil nil e.
Proof.
  intros He'.
  apply runOnGoals_sound_ind with (g := GGoal e) (ctx := CTop nil nil) 
  	(s0 := TopSubst (expr typ func) nil nil) in Hsound.
  unfold rtac_spec in Hsound. simpl in Hsound.
  unfold run_tac in Hres. simpl in Hres.
  rewrite Hres in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound H1 H2).
  destruct Hsound as [Hwfs [Hwfg Hsound]].
  unfold propD, exprD'_typ0 in Hsound.
  simpl in Hsound. unfold exprD_Prop, exprD; simpl.
  forward; inv_all; subst.

  destruct Hsound.
  inversion Hwfs; subst.
  simpl in H0; inv_all; subst.
  unfold pctxD in H0; inv_all; subst.
  apply H5.
  unfold goalD_Prop in He'. simpl in He'. forward; inv_all; subst.
Qed.

Lemma run_rtac_Solved tac s e
  (Hsound : rtac_sound tac) 
  (Hres : run_tac tac (GGoal e) = Solved s) :
  exprD_Prop nil nil e.
Proof.
  unfold run_tac in Hres.
  unfold rtac_sound in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound _ _ _ _ Hres H1 H2).
  destruct Hsound as [Hwfs Hsound].
  simpl in Hsound.
  unfold propD, exprD'_typ0 in Hsound.
  unfold exprD_Prop.
  
  simpl in Hsound. unfold exprD. simpl. forward.
  destruct Hsound. 
  SearchAbout pctxD.
  inversion Hwfs; subst. simpl in H8. inv_all; subst.
  admit.
Qed.

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_aux reify term_table e n :=
  let k fs e :=
      pose e as n in
  reify_expr reify k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].

Ltac run_rtac reify term_table tac_sound :=
  match type of tac_sound with
    | rtac_sound ?tac =>
	  let name := fresh "e" in
	  match goal with
	    | |- ?P => 
	      reify_aux reify term_table P name;
	      let t := eval vm_compute in (typeof_expr nil nil name) in
	      let goal := eval unfold name in name in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac tac (GGoal name)) in 
	          let result := eval vm_compute in goal_result in
	          match result with
	            | More_ ?s ?g => 
	              cut (goalD_Prop nil nil g); [
	                let goal_resultV := g in
	               (* change (goalD_Prop nil nil goal_resultV -> exprD_Prop nil nil name);*)
	                exact_no_check (@run_rtac_More tac _ _ _ tac_sound
	                	(@eq_refl (Result (CTop nil nil)) (More_ s goal_resultV) <:
	                	   run_tac tac (GGoal goal) = (More_ s goal_resultV)))
	                | cbv_denote
	              ]
	            | Solved ?s =>
	              exact_no_check (@run_rtac_Solved tac s name tac_sound 
	                (@eq_refl (Result (CTop nil nil)) (Solved s) <: run_tac tac (GGoal goal) = Solved s))
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.