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
  tyVar : typ;
  tyVal : typ;
  tySubst : typ
}.

Section SubstTypeD.
	Context {typ : Type} {HT : SubstType typ} {HR : RType typ}.
	Context {VN : ValNull (typD tyVal)}.

	Class SubstTypeD := {
	  stSubst : typD tySubst = @subst (typD tyVar) (typD tyVal)
	}.
	
End SubstTypeD.
