Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.TypesI.

Require Import MirrorCharge.ModularFunc.ListFunc.
Require Import MirrorCharge.ModularFunc.ListType.

Section ReifyList.

	Context {typ func : Type} {LT : ListType typ} {LF : ListFunc typ func}.
	Context {RType_typ : RType typ}.
	
 	Reify Declare Patterns patterns_list_typ := typ.

	Reify Declare Patterns patterns_list := (expr typ func).

	Reify Declare Syntax reify_list_typ :=
    { 
  	  (@Patterns.CPatterns typ patterns_list_typ)
    }.

	Reify Declare Typed Table term_table : BinNums.positive => reify_list_typ.

	Reify Declare Syntax reify_list :=
  	{ (@Patterns.CFirst _
  		((@Patterns.CVar _ (@Var typ func)) ::
  	     (@Patterns.CPatterns _ patterns_list) ::
         (@Patterns.CApp _ (@App typ func)) ::
    	 (@Patterns.CAbs _ reify_list_typ (@Abs typ func)) :: nil))
  	}.

	Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
	Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
	Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
	Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
	Local Notation "'#'" := RIgnore (only parsing, at level 0).

	Reify Pattern patterns_list_typ += (!! (@list) @ ?0) => (fun (x : reify_list_typ) => tyList x).

	Reify Pattern patterns_list += (!! @nil @ ?0) => (fun (x : function reify_list_typ) => (fNil (func := expr typ func) x)).
	Reify Pattern patterns_list += (!! @cons @ ?0) => (fun (x : function reify_list_typ) => (fCons (func := expr typ func) x)).
	Reify Pattern patterns_list += (!! @length @ ?0) => (fun (x : function reify_list_typ) => (fLength (func := expr typ func) x)).
	Reify Pattern patterns_list += (!! @combine @ ?0 @ ?1) => (fun (x y : function reify_list_typ) => (fZip (func := expr typ func) x y)).
	Reify Pattern patterns_list += (!! @map @ ?0 @ ?1) => (fun (x y : function reify_list_typ) => (fMap (func := expr typ func) x y)).

End ReifyList.

