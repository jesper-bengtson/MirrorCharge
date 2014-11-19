Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.

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

Reify Declare Patterns patterns_java_typ := typ.

Reify Declare Patterns patterns_java := (ExprCore.expr typ func).

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

(*
Reify Declare Patterns const_for_cmd += ((RHasType cmd ?0) => (fun (c : id cmd) => mkCmd [c] : expr typ func)).
*)

Require Import MirrorCore.Reify.Reify.

Axiom t : Type.
Reify Declare Patterns t_pat := t.



Reify Declare Syntax t_cmd :=
{ (@Patterns.CPatterns t t_pat) }.


Reify Declare Syntax reify_imp_typ :=
  { 
  	(@Patterns.CPatterns typ patterns_java_typ)
  }.

Reify Declare Typed Table term_table : BinNums.positive => reify_imp_typ.

Let Ext x := @ExprCore.Inj typ func (inl (inl (inl (inl (inl (inl (inl (inl x)))))))).

Reify Declare Syntax reify_imp :=
  { (@Patterns.CFirst _
  		((@Patterns.CVar _ (@ExprCore.Var typ func)) ::
  	     (@Patterns.CPatterns _ patterns_java) ::
         (@Patterns.CApp _ (@ExprCore.App typ func)) ::
    	 (@Patterns.CAbs _ reify_imp_typ (@ExprCore.Abs typ func)) ::
    	 (@Patterns.CTypedTable _ _ _ term_table Ext) :: nil))
  }.

Definition stack_get (x : var) (s : stack) := s x.

Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := Fun stack) (ap (T := Fun stack) (pure (T := Fun stack) (@eq val)) x) y).
Notation "'ap_pointsto' '[' x ',' f ',' e ']'" := 
	(ap (T := Fun stack) (ap (T := Fun stack) (ap (T := Fun stack) 
		(pure (T := Fun stack) pointsto) (stack_get x)) 
			(pure (T := Fun stack) f)) e).
Notation "'ap_typeof' '[' e ',' C ']'" :=
	(ap (T := Fun stack) 
	    (ap (T := Fun stack) 
	        (pure (T := Fun stack) typeof) 
	        (pure (T := Fun stack) C))
	    e).

Definition set_fold_fun (x f : String.string) (P : sasn) :=
	ap_pointsto [x, f, pure null] ** P.

Let _Inj := @ExprCore.Inj typ func.

Require Import Java.Examples.ListModel.

Reify Seed Typed Table term_table += 1 => [ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) , List ].
Reify Seed Typed Table term_table += 2 => [ (tyArr tyVal (tyArr (tyList tyVal) tyAsn)) , NodeList ].


Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_java_typ += (@RImpl (?0) (?1)) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_java_typ += (!! asn)  => tyAsn.
Reify Pattern patterns_java_typ += (!! sasn) => tySasn.
Reify Pattern patterns_java_typ += (!! (@vlogic var val)) => tyPure.
Reify Pattern patterns_java_typ += (!! Prop) => tyProp.
Reify Pattern patterns_java_typ += (!! spec) => tySpec.

Reify Pattern patterns_java_typ += (!! @prod @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => tyPair x y).
Reify Pattern patterns_java_typ += (!! (@list String.string)) => tyVarList.
Reify Pattern patterns_java_typ += (!! (@list field)) => tyFields.
Reify Pattern patterns_java_typ += (!! (@list (@Open.expr (Lang.var) val))) => tyVarList.
Reify Pattern patterns_java_typ += (!! (@list (Lang.var * @Open.expr (Lang.var) val))) => tySubstList.
Reify Pattern patterns_java_typ += (!! (@substlist var val)) => tySubstList.
Reify Pattern patterns_java_typ += (!! @list @ ?0) => (fun x : function reify_imp_typ => tyList x).
Reify Pattern patterns_java_typ += (!! nat) => tyNat.
Reify Pattern patterns_java_typ += (!! val) => tyVal.
Reify Pattern patterns_java_typ += (!! bool) => tyBool.
Reify Pattern patterns_java_typ += (!! field) => tyField.
Reify Pattern patterns_java_typ += (!! class) => tyClass.
Reify Pattern patterns_java_typ += (!! @Open.open var val asn) => tySasn.
Reify Pattern patterns_java_typ += (!! @Open.open var val Prop) => tyPure.
Reify Pattern patterns_java_typ += (!! var) => tyVar.
Reify Pattern patterns_java_typ += (!! String.string) => tyString.
Reify Pattern patterns_java_typ += (!! Program) => tyProg.
Reify Pattern patterns_java_typ += (!! stack) => tyStack.
Reify Pattern patterns_java_typ += (!! @Stack.stack var val) => tyStack.
Reify Pattern patterns_java_typ += (!! cmd) => tyCmd.
Reify Pattern patterns_java_typ += (!! dexpr) => tyExpr.
Reify Pattern patterns_java_typ += (!! (@Open.expr var val)) => tyExpr.
Reify Pattern patterns_java_typ += (!! @Subst.subst (String.string) val) => tySubst.

Reify Pattern patterns_java_typ += (!! Fun @ ?0 @ ?1) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_java += (RHasType String.string (?0)) => (fun (s : id String.string) => mkString (func := func) (typ := typ) s).
Reify Pattern patterns_java += (RHasType field (?0)) => (fun (f : id field) => mkField f).
Reify Pattern patterns_java += (RHasType Lang.var (?0)) => (fun (f : id Lang.var) => mkVar (func := func) f).
Reify Pattern patterns_java += (RHasType val (?0)) => (fun (v : id val) => mkVal v).
Reify Pattern patterns_java += (RHasType bool (?0)) => (fun (b : id bool) => mkBool (func := func) b).
Reify Pattern patterns_java += (RHasType nat (?0)) => (fun (n : id nat) => mkNat (func := func) n).
Reify Pattern patterns_java += (RHasType cmd (?0)) => (fun (c : id cmd) => mkCmd c).
Reify Pattern patterns_java += (RHasType dexpr (?0)) => (fun (e : id dexpr) => mkDExpr e).
Reify Pattern patterns_java += (RHasType Program (?0)) => (fun (P : id Program) => mkProg P).
Reify Pattern patterns_java += (RHasType (list field) (?0)) => (fun (fs : id (list field)) => mkFields fs).
Reify Pattern patterns_java += (RHasType class (?0)) => (fun (c : id class) => mkClass c).

Reify Pattern patterns_java += (RHasType (@list dexpr) (?0)) => (fun (es : id (@list dexpr)) => mkExprList es).
Reify Pattern patterns_java += (RHasType (@list String.string) (?0)) => (fun (vs : id (@list String.string)) => mkVarList vs).
Reify Pattern patterns_java += (!! (@eq) @ ?0) => (fun (x : function reify_imp_typ) => fEq (func := expr typ func) x).

(** Intuitionistic Operators **)
Reify Pattern patterns_java += (!! @ILogic.lentails @ ?0 @ #) => (fun (x : function reify_imp_typ) => fEntails (func := expr typ func) x).
Reify Pattern patterns_java += (!! @ILogic.ltrue @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkTrue (func := func) x).
Reify Pattern patterns_java += (!! @ILogic.lfalse @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkFalse (func := func) x).
Reify Pattern patterns_java += (!! @ILogic.land @ ?0 @ #) => (fun (x : function reify_imp_typ) => fAnd (func := expr typ func) x).
Reify Pattern patterns_java += (!! @ILogic.lor @ ?0 @ #) => (fun (x : function reify_imp_typ) => fOr (func := expr typ func) x).
Reify Pattern patterns_java += (!! @ILogic.limpl @ ?0 @ #) => (fun (x : function reify_imp_typ) => fImpl (func := expr typ func) x).

Reify Pattern patterns_java += (!! @ILogic.lexists @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fExists (func := expr typ func) y x).

Reify Pattern patterns_java += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fForall (func := expr typ func) y x).
(** Embedding Operators **)
Reify Pattern patterns_java += (!! @ILEmbed.embed @ ?0 @ ?1 @ #) => (fun (x y : function reify_imp_typ) => fEmbed (func := expr typ func) x y).

Reify Pattern patterns_java += (!! @pair @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => fPair (func := expr typ func) x y).

(** Special cases for Coq's primitives **)
Reify Pattern patterns_java += (!! True) => (mkTrue (func := func) tyProp).
Reify Pattern patterns_java += (!! False) => (mkFalse (func := func) tyProp).
Reify Pattern patterns_java += (!! and) => (fAnd (func := expr typ func) tyProp).

Reify Pattern patterns_java += (!! or) => (fOr (func := expr typ func) tyProp).

Reify Pattern patterns_java += (!! ex @ ?0) => (fun (x : function reify_imp_typ) => fExists (func := expr typ func) x tyProp).

Reify Pattern patterns_java += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (fForall (func := expr typ func) x tyProp) (ExprCore.Abs x y)).

Reify Pattern patterns_java += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => 
	ExprCore.App (ExprCore.App (fImpl (func := expr typ func) tyProp) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_java += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @BILogic.wandSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fWand (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (mkEmp (func := func) x)).

Reify Pattern patterns_java += (!! @Later.illater @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fLater (func := expr typ func) x)).

Reify Pattern patterns_java += (!! method_spec) => (fMethodSpec).

(** Program Logic **)


Reify Pattern patterns_java += (!! triple) => (fTriple).
Reify Pattern patterns_java += (!! eval @ (RHasType dexpr (?0))) => (fun e : id dexpr => evalDExpr e).
Reify Pattern patterns_java += (!! stack_get) => (fStackGet (typ := typ) (func := expr typ func)).
Reify Pattern patterns_java += (!! stack_add (val := val)) => (fStackSet (typ := typ) (func := expr typ func)).

Reify Pattern patterns_java += (!! pointsto) => (fPointsto).
Reify Pattern patterns_java += (!! prog_eq) => (fProgEq).
Reify Pattern patterns_java += (!! typeof) => (fTypeOf).

Reify Pattern patterns_java += (!! (@substl_trunc var val _)) => (fTruncSubst (func := expr typ func) (typ := typ)).
Reify Pattern patterns_java += (!! (@substl var val _)) => (fSubst (func := expr typ func) (typ := typ)).

Reify Pattern patterns_java += (!! @nil @ ?0) => (fun (x : function reify_imp_typ) => (fNil (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @cons @ ?0) => (fun (x : function reify_imp_typ) => (fCons (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @length @ ?0) => (fun (x : function reify_imp_typ) => (fLength (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @zip @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fZip (func := expr typ func) x y)).
Reify Pattern patterns_java += (!! @map @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fMap (func := expr typ func) x y)).
Reify Pattern patterns_java += (!! @fold_right @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fFold (func := expr typ func) x y)).

Reify Pattern patterns_java += (!! (@apply_subst var val) @ ?0) => (fun (x : function reify_imp_typ) => fApplySubst (func := expr typ func) x).
Reify Pattern patterns_java += (!! @subst1 var val _) => (fSingleSubst (func := expr typ func)).
Reify Pattern patterns_java += (!! @field_lookup) => (fFieldLookup).
(** Applicative **)
Reify Pattern patterns_java += (!! @Applicative.ap @ !! (Fun stack) @ # @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => fAp (func := expr typ func) x y).
Reify Pattern patterns_java += (!! @Applicative.pure @ !! (Fun stack) @ # @ ?0) => (fun (x : function reify_imp_typ) => fConst (func := expr typ func) x).

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_imp e :=
  let k fs e :=
      pose e in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].

Require Import ILogic.

Goal (forall (Pr : Program) (C : class) (v : val) (fields : list field), True).
  intros Pr C v fields.
  reify_imp (typeof C v).
  reify_imp (field_lookup).
  reify_imp (field_lookup Pr C fields).

  pose ((fun (_ : @Stack.stack var val) => null) : @Open.expr var val) as e2.
  pose ((fun (_ : stack) => null) : stack -> val) as e3.


  reify_imp (pure (T := Fun stack) pointsto).

  reify_imp e2.

  reify_imp e3.

  reify_imp (ap (T := Fun stack) (ap (T := Fun stack) (pure (@eq val)) e2) e2).

  pose (E_val (vint 3)) as d.

  reify_imp ((ap (ap (T := Fun stack) (pure (@eq val)) (eval d)) (pure (vbool true)))).
  
  generalize String.EmptyString. intro c.
   reify_imp (ltrue |-- {[ ltrue ]} cread c c c {[ ltrue ]}).

  reify_imp cskip.

  reify_imp (forall P, P /\ P).

  reify_imp (forall x : nat, x = x).
  reify_imp (exists x : nat, x = x).
  reify_imp (@map nat nat).
  reify_imp (@subst1 var val _).
  reify_imp (cseq cskip cskip).
  
  reify_imp (ILogic.lentails True True).

  reify_imp ((True -> False) -> True).
  reify_imp (forall P Q, P /\ Q).
  reify_imp (forall P : sasn, ILogic.lentails ILogic.ltrue P).
  reify_imp (forall (G : spec) (P Q : sasn), ILogic.lentails G (triple P Q cskip)).
  generalize (String.EmptyString : String.string).
  intro x.

  reify_imp stack_get.

  reify_imp (stack_get x).

  reify_imp (x = x).

  exact I.

Defined.
Locate ExprUVar_expr.
Locate ILogicFunc.BaseFuncInst.

Check typeof_expr.

Ltac reify_aux e n :=
  let k fs e :=
      pose e as n in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].

Definition mkPointstoVar x f e : expr typ func :=
   mkAp tyVal tyAsn 
        (mkAp tyField (tyArr tyVal tyAsn)
              (mkAp tyVal (tyArr tyField (tyArr tyVal tyAsn))
                    (mkConst (tyArr tyVal (tyArr tyField (tyArr tyVal tyAsn))) 
                             fPointsto)
                    (App fStackGet (mkVar x)))
              (mkConst tyField (mkField f)))
        e.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Subst.FMapSubst.
Require Import Coq.PArith.BinPos.

Definition goalD_aux tus tvs goal (us : HList.hlist typD tus) (vs : HList.hlist typD tvs) :=
  match goalD tus tvs goal with
    | Some e => Some (e us vs)
    | None => None
  end.
    
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
          Check app.

Set Printing Depth 200.

Ltac reify := 
  let name := fresh "e" in
  match goal with 
  | |- ?P => reify_aux P name;
	  let t := eval vm_compute in (typeof_expr nil nil name) in
	  let e := eval unfold name in name in
	  match t with
	  | Some ?t =>  
		  let e' := cbv_denote e t in
		  match e' with
		    | Some ?r => 
		      let r' := constr:(r HList.Hnil HList.Hnil) in 
		      	replace P with r' by exact eq_refl; clear name
		    | _ => idtac e'
		  end
      | _ => idtac 1
	  end
   end.

Definition run_tac tac goal :=
  runOnGoals tac nil nil 0 0 (CTop nil nil) 
    (ctx_empty (typ := typ) (expr := expr typ func)) goal.

Lemma run_rtac_More tac s goal P e e'
  (H : exprD nil nil e tyProp = Some P)
  (Hres : run_tac tac (GGoal e) = More_ s goal) 
  (Heval : goalD_aux nil nil goal HList.Hnil HList.Hnil = Some e')
  (Hsound : rtac_sound tac) :
  e' -> P.
Proof.
  intros He'.
  unfold run_tac in Hres.
  unfold rtac_sound in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound _ _ _ _ Hres H1 H2).
  destruct Hsound as [Hwfs [Hwfg Hsound]].
  simpl in Hsound.
  unfold propD, exprD'_typ0 in Hsound.
  unfold exprD in H. simpl in H. 
  
  Require Import ExtLib.Tactics.
  simpl in Hsound.
  forward; inv_all; subst; destruct Hsound as [Hsubst2 Hsound].
  inversion Hsubst2; subst.
  specialize (Hsound HList.Hnil HList.Hnil).
  simpl in Hsound.
  inv_all; subst.
  inversion Hwfs; subst.
  simpl in H3; inv_all; subst.
  apply Hsound.
  unfold goalD_aux in Heval. forward; inv_all; subst.
  assumption.
Qed.

Lemma run_rtac_Solved tac s P e
  (H : exprD nil nil e tyProp = Some P)
  (Hres : run_tac tac (GGoal e) = Solved s)
  (Hsound : rtac_sound tac) :
  P.
Proof.
  unfold run_tac in Hres.
  unfold rtac_sound in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound _ _ _ _ Hres H1 H2).
  destruct Hsound as [Hwfs Hsound].
  simpl in Hsound.
  unfold propD, exprD'_typ0 in Hsound.
  unfold exprD in H. simpl in H. 

  simpl in Hsound.
  forward; inv_all; subst; destruct Hsound as [Hsubst2 Hsound].
  inversion Hsubst2; subst.
  specialize (Hsound HList.Hnil HList.Hnil).
  simpl in Hsound.
  inv_all; subst.
  inversion Hwfs; subst.
  simpl in H3; inv_all; subst.
  apply Hsound.
Qed.

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
	              let Q := cbv_denote (goalD_aux nil nil g HList.Hnil HList.Hnil) in
	              match Q with
	                | Some ?Q' => 
	                  cut (Q' HList.Hnil HList.Hnil); [
		              let P := cbv_denote (exprD nil nil goal tyProp) in 
		              let H1 := fresh "H" in
		              let H2 := fresh "H" in
		              let H3 := fresh "H" in     
		              let H4 := fresh "H" in      
		              pose (H1 := @eq_refl (option Prop) P <: 
		              	exprD nil nil goal tyProp = P);
		              pose (H2 := @eq_refl (Result (CTop nil nil)) result <: 
		              	run_tac tac (GGoal goal) = result);
		              pose (H3 := @eq_refl (option (exprT nil nil Prop)) Q <:
		              	goalD_aux nil nil g HList.Hnil HList.Hnil = Q);
		              exact (@run_rtac_More tac _ _ _ _ _ H1 H2 H3 tac_sound) |]
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
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" result
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.

