Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.

Require Import MirrorCharge.Java.Syntax.

Require Import Charge.Open.Stack.
Require Import Charge.Open.Subst.
Require Import Charge.Open.OpenILogic.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.
Require Import Java.Semantics.OperationalSemantics.

Reify Declare Patterns patterns_imp_typ := Syntax.typ.

Reify Declare Patterns patterns_imp := (ExprCore.expr Syntax.typ Syntax.func).

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

Reify Declare Typed Table term_table : BinNums.positive => reify_imp_typ.

Let Ext x := @ExprCore.Inj Syntax.typ Syntax.func (inl (inl x)).

Reify Declare Syntax reify_imp :=
  { (@Patterns.CPatterns _ patterns_imp
    (@Patterns.CApp _ (@ExprCore.App Syntax.typ Syntax.func)
    (@Patterns.CAbs _ reify_imp_typ (@ExprCore.Abs Syntax.typ Syntax.func)
    (@Patterns.CVar _ (@ExprCore.Var Syntax.typ Syntax.func)
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
Reify Pattern patterns_imp += (RHasType sval (?0)) => (fun (v : id sval) => mkVal [v] : expr typ func).
Reify Pattern patterns_imp += (RHasType Stack.val (?0)) => (fun (v : id Stack.val) => mkVal [v] : expr typ func).
Reify Pattern patterns_imp += (RHasType (@val SVal) (?0)) => (fun (v : id (@val SVal)) => mkVal [v] : expr typ func).
Reify Pattern patterns_imp += (RHasType cmd (?0)) => (fun (c : id cmd) => mkCmd [c] : expr typ func).
Reify Pattern patterns_imp += (RHasType dexpr (?0)) => (fun (e : id dexpr) => mkExpr [e] : expr typ func).

Reify Pattern patterns_imp += (!! (@eq) @ ?0) => (fun (x : function reify_imp_typ) => fEq [x] : expr typ func).

(** Intuitionistic Operators **)
Reify Pattern patterns_imp += (!! @ILogic.lentails @ ?0 @ #) => (fun (x : function reify_imp_typ) => fEntails [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.ltrue @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkTrue [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.lfalse @ ?0 @ #) => (fun (x : function reify_imp_typ) => mkFalse [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.land @ ?0 @ #) => (fun (x : function reify_imp_typ) => fAnd [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.lor @ ?0 @ #) => (fun (x : function reify_imp_typ) => fOr [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.limpl @ ?0 @ #) => (fun (x : function reify_imp_typ) => fImpl [x] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.lexists @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fExists [x, y] : expr typ func).
Reify Pattern patterns_imp += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => fForall [x, y] : expr typ func).

(** Embedding Operators **)
Reify Pattern patterns_imp += (!! @ILEmbed.embed @ ?0 @ ?1 @ #) => (fun (x y : function reify_imp_typ) => fEmbed [x, y] : expr typ func).

(** Special cases for Coq's primitives **)
Reify Pattern patterns_imp += (!! True) => (mkTrue [tyProp] : expr typ func).
Reify Pattern patterns_imp += (!! False) => (mkFalse [tyProp] : expr typ func).
Reify Pattern patterns_imp += (!! and) => (fAnd [tyProp] : expr typ func).
Reify Pattern patterns_imp += (!! or) => (fOr [tyProp] : expr typ func).
Reify Pattern patterns_imp += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (fForall [tyProp, x]) (ExprCore.Abs x y)).
Reify Pattern patterns_imp += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => ExprCore.App (ExprCore.App (fImpl [tyProp]) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_imp += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar [x] : expr typ func)).
Reify Pattern patterns_imp += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (mkEmp [x] : expr typ func)).

(** Program Logic **)

Reify Pattern patterns_imp += (!! triple) => (fTriple : expr typ func).
Reify Pattern patterns_imp += (!! eval2) => (fEval : expr typ func).
Reify Pattern patterns_imp += (!! stack_get) => (fStackGet : expr typ func).
Reify Pattern patterns_imp += (!! stack_add) => (fStackSet : expr typ func).

Reify Pattern patterns_imp += (!! pointsto2) => (fPointsto : expr typ func).

Reify Pattern patterns_imp += (!! @apply_subst2 @ ?0) => (fun (x : function reify_imp_typ) => fApplySubst [x] : expr typ func).
Reify Pattern patterns_imp += (!! @subst2) => (fSingleSubst : expr typ func).

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
Let elem_ctor : forall x : Syntax.typ, (forall ts : list Type, typD ts x) -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_imp e :=
  let k fs e :=
      pose e in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map_abs _ _ _ (list Type) _ term_table elem_ctor) => True) ]
             [ e ].
Check @pointsto.

Local Instance Applicative_Fun A : Applicative.Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Goal True.
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
