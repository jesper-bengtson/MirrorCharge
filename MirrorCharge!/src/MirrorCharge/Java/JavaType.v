Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.

Require Import MirrorCore.TypesI.

Require Import MirrorCharge.ModularFunc.BaseType.
Require Import MirrorCharge.ModularFunc.ListType.
Require Import MirrorCharge.ModularFunc.SubstType.


Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.
Require Import MirrorCharge.ModularFunc.LaterFunc.

Require Import Charge.Open.Subst.
Require Import Charge.Logics.ILInsts.
Require Import Charge.Logics.BILInsts.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.Later.

Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Language.Lang.
Require Import Java.Language.Program.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ : Type :=
| tyArr : typ -> typ -> typ
| tyList : typ -> typ
| tyPair : typ -> typ -> typ
| tyBool : typ
| tyVal : typ
| tyString : typ
| tyField : typ
| tyVar : typ
| tyClass : typ
| tyNat : typ
| tyProp : typ
| tySpec : typ
| tyAsn : typ
| tyProg : typ
| tyCmd : typ
| tyDExpr : typ
| tySubst : typ.

Notation "'tyStack'" := (tyArr tyVar tyVal).

Notation "'tyPure'" := (tyArr tyStack tyProp).
Notation "'tySasn'" := (tyArr tyStack tyAsn).
Notation "'tyExpr'" := (tyArr tyStack tyVal).
Notation "'tyFields'" := (tyList tyField).

Notation "'tyVarList'" := (tyList tyVar).
Notation "'tyDExprList'" := (tyList tyDExpr).
Notation "'tySubstList'" := (tyList (tyPair tyVar tyExpr)).

Fixpoint type_cast_typ (a b : typ) : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | tyProp , tyProp => Some eq_refl
    | tySpec , tySpec => Some eq_refl
    | tyVal, tyVal => Some eq_refl
    | tyBool, tyBool => Some eq_refl
    | tyProg, tyProg => Some eq_refl
    | tyNat, tyNat => Some eq_refl
    | tyArr x y , tyArr a b =>
      match type_cast_typ x a , type_cast_typ y b with
        | Some pf , Some pf' =>
          Some (match pf in _ = t
                    , pf' in _ = t'
                      return tyArr x y = tyArr t t'
                with
                  | eq_refl , eq_refl => eq_refl
                end)
        | _ , _ => None
      end
    | tyPair x y , tyPair a b =>
      match type_cast_typ x a , type_cast_typ y b with
        | Some pf , Some pf' =>
          Some (match pf in _ = t
                    , pf' in _ = t'
                      return tyPair x y = tyPair t t'
                with
                  | eq_refl , eq_refl => eq_refl
                end)
        | _ , _ => None
      end
    | tyList x, tyList y =>
    	match type_cast_typ x y with
          | Some pf =>
    		Some (match pf in _ = t return tyList x = tyList t with
    			    | eq_refl => eq_refl
    			  end)
          | None => None
       end
    | tyString, tyString => Some eq_refl
    | tyField, tyField => Some eq_refl
    | tyVar, tyVar => Some eq_refl
    | tyClass, tyClass => Some eq_refl
    | tyCmd, tyCmd => Some eq_refl
    | tyDExpr, tyDExpr => Some eq_refl
    | tyAsn, tyAsn => Some eq_refl
    | tySubst, tySubst => Some eq_refl

    | _, _ => None
  end.

Lemma type_cast_typ_sound (a b : typ) :
	(exists pf, type_cast_typ a b = Some pf) <->
	a = b.
Proof.
  split; intros H.
  + destruct a, b; destruct H as [x _]; inversion x; subst; reflexivity.
  + subst. exists eq_refl. induction b; try reflexivity.
    simpl. rewrite IHb1, IHb2. reflexivity.
    simpl. rewrite IHb. reflexivity.
    simpl. rewrite IHb1, IHb2. reflexivity.
Qed.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b => match type_cast_typ a b with
                          | None => false
                          | Some _ => true
                        end }.

Lemma type_cast_typ_refl (a : typ) : type_cast_typ a a = Some eq_refl.
Proof.
  induction a; simpl; try reflexivity.
  rewrite IHa1, IHa2; reflexivity.
  rewrite IHa. reflexivity.
  rewrite IHa1, IHa2; reflexivity.
Qed.

Instance RelDec_correct_typ : RelDec_Correct RelDec_eq_typ.
Proof.
	split; intros x y.
	destruct x, y; simpl; split; intro H; inversion H; subst; try reflexivity.
	+ remember (type_cast_typ x1 y1); destruct o; subst; [|inversion H].
	  remember (type_cast_typ x2 y2); destruct o; subst; [|inversion H].
	  reflexivity.
	+ do 2 rewrite type_cast_typ_refl; reflexivity.
	+ remember (type_cast_typ x y); destruct o; subst; [|inversion H].
	  reflexivity.
	+ rewrite type_cast_typ_refl. reflexivity.
	+ remember (type_cast_typ x1 y1); destruct o; subst; [|inversion H].
	  remember (type_cast_typ x2 y2); destruct o; subst; [|inversion H].
	  reflexivity.
	+ do 2 rewrite type_cast_typ_refl; reflexivity.
Qed.

Fixpoint typD (t : typ) : Type :=
  match t with
    | tyArr a b => typD a -> typD b
    | tyList a => @list (typD a)
    | tyPair a b => (typD a * typD b)%type
    | tyProp => Prop
    | tyNat => nat
    | tyBool => bool
    | tySpec => spec
    | tyAsn => asn
    | tyVal => val
    | tyString => string
    | tyField => field
    | tyVar => var
    | tyClass => class
    | tyProg => Program
    | tyCmd => cmd
    | tyDExpr => dexpr
    | tySubst => @subst var val
  end.

Inductive tyAcc_typ : typ -> typ -> Prop :=
| tyAcc_tyArrL : forall a b, tyAcc_typ a (tyArr a b)
| tyAcc_tyArrR : forall a b, tyAcc_typ a (tyArr b a).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc_typ
; type_cast := type_cast_typ
}.
Set Printing Universes.

Instance Typ2_Fun : Typ2 _ (fun x y : Type => x -> y) :=
{ typ2 := tyArr
; typ2_cast := fun _ _ => eq_refl
; typ2_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyArr a b => fun _ => tr a b
                    | _ => fun fa => fa
                  end
}.


Instance Typ0_Prop : Typ0 _ Prop :=
{ typ0 := tyProp
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyProp => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Instance Typ0Ok_Prop : Typ0Ok Typ0_Prop.
Proof.
    constructor.
    { reflexivity. }
    { destruct x; try solve [ right ; reflexivity ].
      { left. exists eq_refl. reflexivity. } }
    { destruct pf. reflexivity. }
Qed.

Instance RTypeOk_typ : @RTypeOk _ RType_typ.
Proof.
	split; intros.
	+ reflexivity.
	+ unfold well_founded.
	  intros. induction a; simpl; constructor; intros; inversion H; subst.
	  assumption. assumption.
	+ destruct pf; reflexivity.
	+ destruct pf1, pf2; reflexivity.
	+ apply type_cast_typ_refl.
	+ intro H1. inversion H1; subst.
	  rewrite type_cast_typ_refl in H. inversion H.
Qed.

Instance BaseType_typ : BaseType typ := {
  tyNat := tyNat;
  tyBool := tyBool;
  tyString := tyString;
  tyPair := tyPair
}.

Instance BaseTypeD_typ : BaseTypeD := {
	btNat := eq_refl;
	btBool := eq_refl;
	btString := eq_refl;
	btPair := fun _ _ => eq_refl
}.

Instance ListType_typ : ListType typ := {
	tyList := tyList
}.

Instance ListTypeD_typ : ListTypeD := {
	btList := fun _ => eq_refl
}.

Instance SubstType_typ : SubstType typ := {
	tyVar := tyVar;
	tyVal := tyVal;
	tySubst := tySubst
}.

Definition null' : TypesI.typD tyVal := null.

Program Instance SubstTypeD_typ : @SubstTypeD typ _ _ := {
	stSubst := eq_refl
}.

Definition should_not_be_necessary : ILogicOps (TypesI.typD tySpec).
Proof.
  simpl.
  apply _.
Qed.

Definition should_also_not_be_necessary : ILLOperators (TypesI.typD tySpec).
Proof.
  simpl.
  apply _.
Qed.

  Definition ilops : @logic_ops _ RType_typ :=
  fun t =>
    match t
          return option (ILogic.ILogicOps (TypesI.typD t))
    with
      | tyProp => Some _
      | tyAsn => Some _
      | tySasn => Some (@ILFun_Ops stack asn _)
      | tySpec => Some should_not_be_necessary
      | tyPure => Some ( @ILFun_Ops stack Prop _)
      | _ => None
    end.

  Definition bilops : @bilogic_ops _ RType_typ :=
  fun t =>
    match t
          return option (BILogic.BILOperators (TypesI.typD t))
    with
      | tyAsn => Some _
      | tySasn => Some (@BILFun_Ops stack asn _)
      | _ => None
    end.

Definition eops : @embed_ops _ RType_typ :=
  fun t u =>
    match t as t , u as u
          return option
                   (ILEmbed.EmbedOp (TypesI.typD t) (TypesI.typD u))
    with
      | tyPure, tySasn => Some _
      | _ , _ => None
    end.

Definition lops : @later_ops _ RType_typ :=
  fun t =>
    match t return option (ILLOperators (TypesI.typD t)) with
	  | tySpec => Some should_also_not_be_necessary
	  | _ => None
    end.