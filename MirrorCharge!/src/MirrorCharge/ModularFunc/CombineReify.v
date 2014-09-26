Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.TypesI.

Require Import MirrorCharge.ModularFunc.BaseReify.
Require Import MirrorCharge.ModularFunc.ListReify.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ListFunc.
Require Import MirrorCharge.ModularFunc.BaseType.
Require Import MirrorCharge.ModularFunc.ListType.

Section CombineFunc.
	Context {typ : Type} {BT : BaseType typ} {LT : ListType typ}.
	Context {RType_typ : RType typ}.

	Definition func := (@base_func typ + @list_func typ)%type.

	Reify Declare Patterns patterns_combine_typ := typ.

	Reify Declare Syntax reify_combine_typ :=
    { 
  	  (@Patterns.CPatterns typ patterns_combine_typ)
    }.

	Reify Declare Typed Table term_table : BinNums.positive => reify_combine_typ.

Definition my_inl (t : expr typ (@base_func typ)) : expr typ func.
Proof.
  admit.
Qed.

	Reify Declare Syntax reify_combine :=
	{
		(@Patterns.CMap (expr typ func) (expr typ (@base_func typ)) my_inl
         (@Patterns.CCall (expr typ (@base_func typ)) (@reify_base typ (expr typ (@base_func typ)))))
	}.
	
	Let elem_ctor : forall x : typ, typD x -> @SymEnv.function _ _ :=
	  @SymEnv.F _ _.
	
	Ltac reify_combine e :=
	  let k fs e :=
	      pose e in
	  reify_expr reify_combine k
	             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
	             [ e ].
	Goal True.
	  reify_combine  5.
	  reify_combine (5, 3).
	  reify_base (3, true).
	  reify_base (5 = 3).
	  
	  apply I.
	Defined.

End ReifyBase.
