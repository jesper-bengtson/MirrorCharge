Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.TypesI.

Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.BaseType.

Section ReifyBase.

	Context {typ func : Type} {BT : BaseType typ} {BF: BaseFunc typ func}.
	Context {RType_typ : RType typ}.

	Reify Declare Patterns patterns_base_typ := typ.

	Reify Declare Patterns patterns_base := (expr typ func).

	Reify Declare Syntax reify_base_typ :=
    { 
  	  (@Patterns.CPatterns typ patterns_base_typ)
    }.

	Reify Declare Typed Table term_table : BinNums.positive => reify_base_typ.

	Reify Declare Syntax reify_base :=
  	{ 
  		(@Patterns.CFirst _
  		((@Patterns.CVar _ (@Var typ func)) ::
  	     (@Patterns.CPatterns _ patterns_base) ::
         (@Patterns.CApp _ (@App typ func)) ::
    	 (@Patterns.CAbs _ reify_base_typ (@Abs typ func)) ::nil))
  	}.
Print reify_base.
	Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
	Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
	Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
	Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
	Local Notation "'#'" := RIgnore (only parsing, at level 0).

	Reify Pattern patterns_base_typ += (!! nat) => tyNat.
	Reify Pattern patterns_base_typ += (!! bool) => tyBool.
	Reify Pattern patterns_base_typ += (!! String.string) => tyString.
	Reify Pattern patterns_base_typ += (!! (@pair) @ ?0 @ ?1) => (fun (x y : reify_base_typ) => tyPair x y).
	
	Reify Pattern patterns_base += (RHasType nat (?0)) => (fun (n : id nat) => mkNat (func := func) (typ := typ) n).
	Reify Pattern patterns_base += (RHasType bool (?0)) => (fun (b : id bool) => mkBool (func := func) (typ := typ) b).
	Reify Pattern patterns_base += (RHasType String.string (?0)) => (fun (s : id String.string) => mkString (func := func) (typ := typ) s).
	
	Reify Pattern patterns_base += (!! @pair @ ?0 @ ?1) => 
		(fun (x y : function reify_base_typ) => (fPair (func := expr typ func) x y)).
	Reify Pattern patterns_base += (!! @eq @ ?0) => 
		(fun (x : function reify_base_typ) => (fEq (func := expr typ func) x)).
	
	Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
	  @SymEnv.F _ _.
	
	Ltac reify_base e :=
	  let k fs e :=
	      pose e in
	  reify_expr reify_base k
	             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
	             [ e ].
	Goal True.
	  reify_base (5, 3).
	  reify_base (3, true).
	  reify_base (5 = 3).
	  
	  apply I.
	Defined.

End ReifyBase.

