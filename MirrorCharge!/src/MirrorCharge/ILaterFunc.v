Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.Later.
Require Import MapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RelDec_typ_eq : RelDec (@eq typ).
  Variable RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq.

  Definition ilater_func := typ.

  Global Instance RelDec_ilfunc : RelDec (@eq ilater_func) :=
  { rel_dec := rel_dec }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor. eapply RelDecCorrect_typ_eq.
  Qed.

  (** TODO: Build an ordered map over types **)
  (** the canonical implementation doesn't work!
  Inductive tree : (typ -> Type) -> Type :=
  | Node : forall F, option (F tyProp) ->
           tree (fun t => tree (fun u => F (tyArr t u))) ->
           tree F
  | Empty : forall F, tree F.
  **)

  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD t)).
  Definition later_ops := forall (t : typ),
    option (ILLOperators (@typD _ RType_typ t)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | Some T => @ILogic _ T
                | None => True
              end.
  Definition later_opsOk (ls : logic_ops) (es : later_ops) : Prop :=
    forall t,
      match ls t , es t return Prop with
        | Some a , Some T => @ILLater _ a T
        | _ , _ => True
      end.

  Variable gs : logic_ops.
  Variable es : later_ops.

  Variable Typ2_tyArr : Typ2 _ Fun.
  Variable Typ0_tyProp : Typ0 _ Prop.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition typeof_func (f : ilater_func) : option typ :=
    match es f with
      | None => None
      | Some _ => Some (tyArr f f)
    end.

  Definition typ2_cast_bin (a b c : typ)
  : (typD a -> typD b -> typD c) -> typD (tyArr a (tyArr b c)) :=
    fun f =>
      match eq_sym (typ2_cast a (tyArr b c)) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast b c) in _ = t
                           return _ -> t with
                       | eq_refl => f
                     end
        end.

  Definition typ2_cast_quant (a b c : typ)
  : ((typD a -> typD b) -> typD c) -> typD (tyArr (tyArr a b) c) :=
    fun f =>
      match eq_sym (typ2_cast (tyArr a b) c) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast a b) in _ = t
                           return t -> _ with
                       | eq_refl => f
                     end
      end.

  Definition funcD (f : ilater_func) :
    match typeof_func f with
      | Some t => typD t
      | None => unit
    end :=
    match es f as x
          return (match match x with
			  | Some _ => Some (tyArr f f)
			  | None => None
			end with
		    | Some t0 => typD t0
		    | None => unit
		  end) with
      | Some t =>
        match eq_sym (typ2_cast f f) in _ = t
              return t with
          | eq_refl => @illater _ _
        end
      | None => tt
    end.

  Global Instance RSym_ilater : RSym ilater_func :=
  { typeof_sym := typeof_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_ilfunc : RSymOk RSym_ilater.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End typed.
