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
Reify Declare Syntax reify_imp_typ :=
  { 
  	(@Patterns.CPatterns typ patterns_java_typ)
  }.

(*
Reify Declare Syntax reify_imp_typ :=
  { (@Patterns.CPatterns typ patterns_java_typ
     (@Patterns.CFail typ))
  }.


Definition eval2 : dexpr -> stack -> val := eval.
Definition pointsto2 : sval -> String.string -> sval -> asn := pointsto.
Definition subst2 : (stack -> sval) -> String.string -> @subst String.string _ := subst1.
Definition apply_subst2 (A : Type) : (stack -> A) -> @Subst.subst String.string SVal -> (stack -> A) := @apply_subst String.string _ A.
Definition field_lookup2 : Program -> String.string -> SS.t -> Prop := field_lookup.
Definition typeof2 (C : String.string) (x : sval) := typeof C x.
Definition method_spec2 : String.string -> String.string -> list String.string -> String.string -> sasn -> sasn -> spec := method_spec.
*)
(*
Notation "'ap_eq' '[' x ',' y ']'" := (ap (T := Fun stack) (ap (pure (@eq sval)) x) y).
Notation "'ap_pointsto' '[' x ',' f ',' e ']'" := 
	(ap (T := Fun stack) (ap (ap (pure pointsto2) (stack_get x)) (pure f)) e).
Notation "'ap_typeof' '[' e ',' C ']'" :=
	(ap (T := Fun stack) 
	    (ap (T := Fun stack) 
	        (pure (T := Fun stack) typeof2) 
	        (pure (T := Fun stack) C))
	    e).


Definition set_fold_fun (x f : String.string) (P : sasn) :=
	ap_pointsto [x, f, pure null] ** P.
*)

Reify Declare Typed Table term_table : BinNums.positive => reify_imp_typ.

Let Ext x := @ExprCore.Inj typ func (inl (inl (inl (inl (inl (inl (inl (inl x)))))))).

Check Ext.

Reify Declare Syntax reify_imp :=
  { (@Patterns.CFirst _
  		((@Patterns.CVar _ (@ExprCore.Var typ func)) ::
  	     (@Patterns.CPatterns _ patterns_java) ::
         (@Patterns.CApp _ (@ExprCore.App typ func)) ::
    	 (@Patterns.CAbs _ reify_imp_typ (@ExprCore.Abs typ func)) ::
    	 (@Patterns.CTypedTable _ _ _ term_table Ext) :: nil))
  }.

Let _Inj := @ExprCore.Inj typ func.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_java_typ += (@RImpl (?0) (?1)) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_java_typ += (!! asn)  => tyAsn.
Reify Pattern patterns_java_typ += (!! sasn) => tySasn.
Reify Pattern patterns_java_typ += (!! (@vlogic var _)) => tyPure.
Reify Pattern patterns_java_typ += (!! Prop) => tyProp.
Reify Pattern patterns_java_typ += (!! spec) => tySpec.

Reify Pattern patterns_java_typ += (!! @prod @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => tyPair x y).
Reify Pattern patterns_java_typ += (!! (@list String.string)) => tyVarList.
Reify Pattern patterns_java_typ += (!! (@list (@Open.expr (Lang.var) SVal))) => tyVarList.
Reify Pattern patterns_java_typ += (!! (@list (Lang.var * @Open.expr (Lang.var) SVal))) => tySubstList.
Reify Pattern patterns_java_typ += (!! (@substlist var _)) => tySubstList.
Reify Pattern patterns_java_typ += (!! nat) => tyNat.
Reify Pattern patterns_java_typ += (!! sval) => tyVal.
Reify Pattern patterns_java_typ += (!! field) => tyField.
Reify Pattern patterns_java_typ += (!! class) => tyClass.
Reify Pattern patterns_java_typ += (!! @Open.open var _ asn) => tySasn.
Reify Pattern patterns_java_typ += (!! @Open.open var _ Prop) => tyPure.
Reify Pattern patterns_java_typ += (!! (@val _)) => tyVal.
Reify Pattern patterns_java_typ += (!! var) => tyVar.
Reify Pattern patterns_java_typ += (!! String.string) => tyString.
Reify Pattern patterns_java_typ += (!! Prog_wf) => tyProg.
Reify Pattern patterns_java_typ += (!! stack) => tyStack.
Reify Pattern patterns_java_typ += (!! @Stack.stack var _) => tyStack.
Reify Pattern patterns_java_typ += (!! cmd) => tyCmd.
Reify Pattern patterns_java_typ += (!! SS.t) => tyFields.
Reify Pattern patterns_java_typ += (!! dexpr) => tyExpr.
Reify Pattern patterns_java_typ += (!! (@Open.expr var _)) => tyExpr.
Reify Pattern patterns_java_typ += (!! @Subst.subst (String.string) SVal) => tySubst.

Reify Pattern patterns_java_typ += (!! Fun @ ?0 @ ?1) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_java += (RHasType String.string (?0)) => (fun (s : id String.string) => mkString (func := func) (typ := typ) s).
Reify Pattern patterns_java += (RHasType field (?0)) => (fun (f : id field) => mkField f).
Reify Pattern patterns_java += (RHasType Lang.var (?0)) => (fun (f : id Lang.var) => mkVar f).
Reify Pattern patterns_java += (RHasType sval (?!0)) => (fun (v : id sval) => mkVal v).
Reify Pattern patterns_java += (RHasType (@val _) (?0)) => (fun (v : id (@val SVal)) => mkVal v).
Reify Pattern patterns_java += (RHasType cmd (?0)) => (fun (c : id cmd) => mkCmd c).
Reify Pattern patterns_java += (RHasType dexpr (?0)) => (fun (e : id dexpr) => mkDExpr e).
Reify Pattern patterns_java += (RHasType Prog_wf (?0)) => (fun (P : id Prog_wf) => mkProg P).
Reify Pattern patterns_java += (RHasType SS.t (?0)) => (fun (fs : id SS.t) => mkFields fs).
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

(** Special cases for Coq's primitives **)
Reify Pattern patterns_java += (!! True) => (mkTrue (func := func) tyProp).
Reify Pattern patterns_java += (!! False) => (mkFalse (func := func) tyProp).
Reify Pattern patterns_java += (!! and) => (fAnd (func := expr typ func) tyProp).

Reify Pattern patterns_java += (!! or) => (fOr (func := expr typ func) tyProp).

Reify Pattern patterns_java += (!! ex @ ?0) => (fun (x : function reify_imp_typ) => fExists (func := expr typ func) x tyProp).

Reify Pattern patterns_java += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (fForall (func := expr typ func) x tyProp) (ExprCore.Abs x y)).

Reify Pattern patterns_java += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => ExprCore.App (ExprCore.App (fImpl (func := expr typ func) tyProp) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_java += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (mkEmp (func := func) x)).

Reify Pattern patterns_java += (!! @Later.illater @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fLater (func := expr typ func) x)).

Reify Pattern patterns_java += (!! method_spec) => (fMethodSpec).

(** Program Logic **)

Definition stack_get (x : var) (s : stack) := s x.

Reify Pattern patterns_java += (!! triple) => (fTriple).
Reify Pattern patterns_java += (!! eval) => (fEval).
Reify Pattern patterns_java += (!! stack_get) => (fStackGet (typ := typ) (func := expr typ func)).
Reify Pattern patterns_java += (!! stack_add) => (fStackSet (typ := typ) (func := expr typ func)).

Reify Pattern patterns_java += (!! pointsto) => (fPointsto).
Reify Pattern patterns_java += (!! set_fold_fun) => (fSetFoldFun).
Reify Pattern patterns_java += (!! SS.fold @ ?0) => (fun (x : function reify_imp_typ) => (fSetFold x)).
Reify Pattern patterns_java += (!! prog_eq) => (fProgEq).
Reify Pattern patterns_java += (!! typeof) => (fTypeOf).

Reify Pattern patterns_java += (!! (@substl_trunc var _ _)) => (fTruncSubst (func := expr typ func) (typ := typ)).
Reify Pattern patterns_java += (!! (@substl var _ _)) => (fSubst (func := expr typ func) (typ := typ)).

Reify Pattern patterns_java += (!! @nil @ ?0) => (fun (x : function reify_imp_typ) => (fNil (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @cons @ ?0) => (fun (x : function reify_imp_typ) => (fCons (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @length @ ?0) => (fun (x : function reify_imp_typ) => (fLength (func := expr typ func) x)).
Reify Pattern patterns_java += (!! @zip @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fZip (func := expr typ func) x y)).
Reify Pattern patterns_java += (!! @map @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fMap (func := expr typ func) x y)).

Reify Pattern patterns_java += (!! (@apply_subst var _) @ ?0) => (fun (x : function reify_imp_typ) => fApplySubst (func := expr typ func) x).
Reify Pattern patterns_java += (!! @subst1 var _ _) => (fSingleSubst (func := expr typ func)).
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

Goal (forall (Pr : Prog_wf) (C : class) (v : val) (fields : SS.t), True).
  intros Pr C v fields.
  (* GREGORY: The three following commands show the problem *)
  reify_imp (typeof C v).
  (* This line above works fine *)
  reify_imp (field_lookup).
  (* So does this *)
  reify_imp (field_lookup Pr C fields).
  (* But this one places (field_lookup Pr) in the table *)
  
  Check @field_lookup.
  pose ((fun (_ : @Stack.stack var _) => null) : @Open.expr var _) as e2.
  pose ((fun (_ : stack) => null) : stack -> sval) as e3.


  reify_imp (pure (T := Fun stack) pointsto).

  reify_imp e2.

  reify_imp e3.
     
  reify_imp (ap (T := Fun stack) (ap (T := Fun stack) (pure (@eq sval)) e2) e2).

  pose (E_val (vint 3)) as d.

  reify_imp ((ap (ap (T := Fun stack) (pure (@eq sval)) (eval d)) (pure (vbool true)))).
  
  generalize String.EmptyString. intro c.
   reify_imp (ltrue |-- {[ ltrue ]} cread c c c {[ ltrue ]}).

  reify_imp cskip.

  reify_imp (forall P, P /\ P).

  reify_imp (forall x : nat, x = x).
  reify_imp (exists x : nat, x = x).
  reify_imp (@map nat nat).
  reify_imp (@subst1 var _ _).
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

