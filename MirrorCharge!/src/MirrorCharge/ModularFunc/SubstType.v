Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.

Require Import MirrorCore.TypesI.

Require Import Charge.Open.Subst.
Require Import Charge.Open.Stack.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Class SubstType (typ : Type) := {
  tySubst : typ
}.

Section SubstTypeD.
	Context {typ : Type} {HT : SubstType typ} {HR : RType typ}.
	Context {d r : typ} {null : typD r}.
	
    Local Instance VN : ValNull := @Build_ValNull (typD r) null.

	Class SubstTypeD := {
	  stSubst : typD tySubst = @subst (typD d) VN
	}.
	
End SubstTypeD.
