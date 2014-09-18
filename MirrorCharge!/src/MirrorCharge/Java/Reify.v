Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.

Require Import MirrorCharge.Java.Syntax.

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

Reify Declare Patterns patterns_imp_typ := Syntax.typ.

Reify Declare Patterns patterns_imp := (ExprCore.expr Syntax.typ Syntax.func).

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.


(*
Reify Declare Patterns const_for_cmd += ((RHasType cmd ?0) => (fun (c : id cmd) => mkCmd [c] : expr typ func)).
*)
Reify Declare Syntax reify_imp_typ :=
  { (@Patterns.CPatterns Syntax.typ patterns_imp_typ
     (@Patterns.CFail Syntax.typ))
  }.


Definition eval2 : dexpr -> stack -> val := eval.
Definition pointsto2 : sval -> String.string -> sval -> asn := pointsto.
Definition subst2 : (stack -> sval) -> String.string -> @subst String.string _ := subst1.
Definition apply_subst2 (A : Type) : (stack -> A) -> @Subst.subst String.string SVal -> (stack -> A) := @apply_subst String.string _ A.
Definition field_lookup2 : Program -> String.string -> SS.t -> Prop := field_lookup.
Definition typeof2 (C : String.string) (x : sval) := typeof C x.
Definition method_spec2 : String.string -> String.string -> list String.string -> String.string -> sasn -> sasn -> spec := method_spec.

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

Reify Declare Typed Table term_table : BinNums.positive => reify_imp_typ.

Let Ext x := @ExprCore.Inj Syntax.typ Syntax.func (inl (inl x)).

Check Ext.

Reify Declare Syntax reify_imp :=
  { (@Patterns.CVar _ (@ExprCore.Var Syntax.typ Syntax.func)
    (@Patterns.CPatterns _ patterns_imp
    (@Patterns.CApp _ (@ExprCore.App Syntax.typ Syntax.func)
    (@Patterns.CAbs _ reify_imp_typ (@ExprCore.Abs Syntax.typ Syntax.func)
    (@Patterns.CTypedTable _ _ _ term_table Ext
    (@Patterns.CFail (ExprCore.expr Syntax.typ Syntax.func)))))))
  }.

Let _Inj := @ExprCore.Inj Syntax.typ Syntax.func.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_imp_typ += (@RImpl (?0) (?1)) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_imp_typ += (!! asn)  => tyAsn.
Reify Pattern patterns_imp_typ += (!! sasn) => tySasn.
Reify Pattern patterns_imp_typ += (!! (@vlogic String.string _)) => tyPure.
Reify Pattern patterns_imp_typ += (!! Prop) => tyProp.
Reify Pattern patterns_imp_typ += (!! spec) => tySpec.

Reify Pattern patterns_imp_typ += (!! @prod @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => tyPair x y).
Reify Pattern patterns_imp_typ += (!! (@list String.string)) => tyVarList.
Reify Pattern patterns_imp_typ += (!! (@list (@Open.expr (Lang.var) SVal))) => tyVarList.
Reify Pattern patterns_imp_typ += (!! (@list (Lang.var * @Open.expr (Lang.var) SVal))) => tySubstList.
Reify Pattern patterns_imp_typ += (!! nat) => tyNat.
Reify Pattern patterns_imp_typ += (!! sval) => tyVal.
Reify Pattern patterns_imp_typ += (!! String.string) => tyString.
Reify Pattern patterns_imp_typ += (!! Prog_wf) => tyProg.
Reify Pattern patterns_imp_typ += (!! stack) => tyStack.
Reify Pattern patterns_imp_typ += (!! cmd) => tyCmd.
Reify Pattern patterns_imp_typ += (!! SS.t) => tyFields.
Reify Pattern patterns_imp_typ += (!! dexpr) => tyExpr.
Reify Pattern patterns_imp_typ += (!! @Subst.subst (String.string) SVal) => tySubst.

Reify Pattern patterns_imp_typ += (!! Fun @ ?0 @ ?1) => (fun (a b : function reify_imp_typ) => tyArr a b).

Reify Pattern patterns_imp += (RHasType String.string (?0)) => (fun (s : id String.string) => mkString [s] : expr typ func).
Reify Pattern patterns_imp += (RHasType field (?0)) => (fun (f : id field) => mkString [f] : expr typ func).
Reify Pattern patterns_imp += (RHasType Lang.var (?0)) => (fun (f : id Lang.var) => mkString [f] : expr typ func).
Reify Pattern patterns_imp += (RHasType sval (?!0)) => (fun (v : id sval) => mkVal [v] : expr typ func).
Reify Pattern patterns_imp += (RHasType Stack.val (?0)) => (fun (v : id Stack.val) => mkVal [v] : expr typ func).
Reify Pattern patterns_imp += (RHasType (@val SVal) (?0)) => (fun (v : id (@val SVal)) => mkVal [v] : expr typ func).
Reify Pattern patterns_imp += (RHasType cmd (?0)) => (fun (c : id cmd) => mkCmd [c] : expr typ func).
Reify Pattern patterns_imp += (RHasType dexpr (?0)) => (fun (e : id dexpr) => mkExpr [e] : expr typ func).
Reify Pattern patterns_imp += (RHasType Prog_wf (?0)) => (fun (P : id Prog_wf) => mkProg [P] : expr typ func).
Reify Pattern patterns_imp += (RHasType SS.t (?0)) => (fun (fs : id SS.t) => mkFields [fs] : expr typ func).
Reify Pattern patterns_imp += (RHasType class (?0)) => (fun (c : id class) => mkString [c] : expr typ func).
Reify Pattern patterns_imp += (RHasType (@list dexpr) (?0)) => (fun (es : id (@list dexpr)) => mkExprList [es] : expr typ func).
Reify Pattern patterns_imp += (RHasType (@list String.string) (?0)) => (fun (vs : id (@list String.string)) => mkVarList [vs] : expr typ func).
Reify Pattern patterns_imp += (!! (@eq) @ ?0) => (fun (x : function reify_imp_typ) => fEq [x] : expr typ func).

(** Intuitionistic Operators **)
Reify Pattern patterns_imp += (!! @ILogic.lentails @ ?0 @ #) => (fun (x : function reify_imp_typ) => fEntails [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.ltrue @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkTrue [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.lfalse @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkFalse [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.land @ ?0 @ #) => (fun (x : function reify_imp_typ) => fAnd [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.lor @ ?0 @ #) => (fun (x : function reify_imp_typ) => fOr [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.limpl @ ?0 @ #) => (fun (x : function reify_imp_typ) => fImpl [x] : expr typ func).
(*
Reify Pattern patterns_imp += (!! @ILogic.lexists @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fExists [x, y] : expr typ func).
*)
Reify Pattern patterns_imp += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fForall [x, y] : expr typ func).
(** Embedding Operators **)
Reify Pattern patterns_imp += (!! @ILEmbed.embed @ ?0 @ ?1 @ #) => (fun (x y : function reify_imp_typ) => fEmbed [x, y] : expr typ func).

(** Special cases for Coq's primitives **)
Reify Pattern patterns_imp += (!! True) => (mkTrue [tyProp] : expr typ func).
Reify Pattern patterns_imp += (!! False) => (mkFalse [tyProp] : expr typ func).
Reify Pattern patterns_imp += (!! and) => (fAnd [tyProp] : expr typ func).

Reify Pattern patterns_imp += (!! or) => (fOr [tyProp] : expr typ func).
(*
Reify Pattern patterns_imp += (!! ex @ ?0) => (fun (x : function reify_imp_typ) => fExists [tyProp, x] : expr typ func).
*)
Reify Pattern patterns_imp += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (fForall [tyProp, x]) (ExprCore.Abs x y)).

Reify Pattern patterns_imp += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => ExprCore.App (ExprCore.App (fImpl [tyProp]) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_imp += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar [x] : expr typ func)).
Reify Pattern patterns_imp += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (mkEmp [x] : expr typ func)).

Reify Pattern patterns_imp += (!! @Later.illater @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fLater [x] : expr typ func)).

Reify Pattern patterns_imp += (!! method_spec2) => (fMethodSpec : expr typ func).

(** Program Logic **)

Reify Pattern patterns_imp += (!! triple) => (fTriple : expr typ func).
Reify Pattern patterns_imp += (!! eval2) => (fEval : expr typ func).
Reify Pattern patterns_imp += (!! stack_get) => (fStackGet : expr typ func).
Reify Pattern patterns_imp += (!! stack_add) => (fStackSet : expr typ func).

Reify Pattern patterns_imp += (!! pointsto2) => (fPointsto : expr typ func).
Reify Pattern patterns_imp += (!! set_fold_fun) => (fSetFoldFun : expr typ func).
Reify Pattern patterns_imp += (!! SS.fold @ ?0) => (fun (x : function reify_imp_typ) => (fSetFold [x] : expr typ func)).
Reify Pattern patterns_imp += (!! prog_eq) => (fProgEq : expr typ func).
Reify Pattern patterns_imp += (!! typeof2) => (fTypeOf : expr typ func).

Reify Pattern patterns_imp += (!! substl_trunc) => (fTruncSubst : expr typ func).
Reify Pattern patterns_imp += (!! substl) => (fSubst : expr typ func).

Reify Pattern patterns_imp += (!! @nil @ ?0) => (fun (x : function reify_imp_typ) => (fNil [x] : expr typ func)).
Reify Pattern patterns_imp += (!! @cons @ ?0) => (fun (x : function reify_imp_typ) => (fCons [x] : expr typ func)).
Reify Pattern patterns_imp += (!! @length @ ?0) => (fun (x : function reify_imp_typ) => (fLength [x] : expr typ func)).
Reify Pattern patterns_imp += (!! @zip @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fZip [x, y] : expr typ func)).
Reify Pattern patterns_imp += (!! @map @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fMap [x, y] : expr typ func)).

Reify Pattern patterns_imp += (!! @apply_subst2 @ ?0) => (fun (x : function reify_imp_typ) => fApplySubst [x] : expr typ func).
Reify Pattern patterns_imp += (!! @subst2) => (fSingleSubst : expr typ func).
Reify Pattern patterns_imp += (!! @field_lookup2) => (fFieldLookup : expr typ func).
(** Applicative **)
Reify Pattern patterns_imp += (!! @Applicative.ap @ !! (Fun stack) @ # @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => fAp [x, y] : expr typ func).
Reify Pattern patterns_imp += (!! @Applicative.pure @ !! (Fun stack) @ # @ ?0) => (fun (x : function reify_imp_typ) => fConst [x] : expr typ func).
(*
(** Table Entries **)
Local Notation "a >> b" := (tyArr a b) (at level 31,right associativity).

Reify Seed Typed Table term_table += 1 => [ (tyLProp >> tyCmd >> tyLProp >> tySProp) , triple ].
Reify Seed Typed Table term_table += 2 => [ (tyCmd >> tyCmd >> tyCmd) , Seq ].
Reify Seed Typed Table term_table += 3 => [ (tyVariable >> tyExpr >> tyCmd) , Assign ].
Reify Seed Typed Table term_table += 4 => [ (tyVariable >> tyExpr >> tyCmd) , Read ].
Reify Seed Typed Table term_table += 5 => [ (tyExpr >> tyExpr >> tyCmd) , Write ].
Reify Seed Typed Table term_table += 6 => [ tyCmd , Skip ].
Reify Seed Typed Table term_table += 7 => [ (tyNat >> tyNat >> tyHProp) , PtsTo ].
Reify Seed Typed Table term_table += 8 => [ (tyVariable >> (tyNat >> tyLProp) >> (tyNat >> tyLProp) >> tySProp) , function_spec ].
*)




Let elem_ctor : forall x : Syntax.typ, typD x -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_imp e :=
  let k fs e :=
      pose e in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map_abs _ _ _ (list Type) _ term_table elem_ctor) => True) ]
             [ e ].

Goal True.
  reify_imp (forall P, P /\ P).
  reify_imp (forall x : nat, x = x).
  reify_imp (exists x : nat, x = x).
  reify_imp (exists x : nat, x = x).

  reify_imp (exists x : nat, x = x).
  reify_imp (@map nat nat).
  reify_imp subst2.
  reify_imp (cseq cskip cskip).
  reify_imp (ILogic.lentails True True).
  reify_imp ((True -> False) -> True).
  reify_imp (forall P Q, P /\ Q).
  reify_imp (forall P : sasn, ILogic.lentails ILogic.ltrue P).
  reify_imp (forall (G : spec) (P Q : sasn), ILogic.lentails G (triple P Q cskip)).
  generalize (String.EmptyString : String.string).
  intro x.
  reify_imp (stack_get x).
  reify_imp (x = x).
  exact I.
Defined.
