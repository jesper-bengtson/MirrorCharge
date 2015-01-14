Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
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

  Inductive iefunc :=
  | ief_embed (from to : typ).
(* | fref (fi : positive) *)

  Global Instance RelDec_iefunc : RelDec (@eq iefunc) :=
  { rel_dec := fun a b =>
	         match a, b with
		   | ief_embed a t, ief_embed a' t' => a ?[eq] a' && t ?[eq] t'
	         end
  }.

  Global Instance RelDec_Correct_iefunc : RelDec_Correct RelDec_iefunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
  Qed.

  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD t)).
  Definition embed_ops := forall (t u : typ),
    option (EmbedOp (typD t) (typD u)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | Some T => @ILogic _ T
                | None => True
              end.
  Definition embed_opsOk (ls : logic_ops) (es : embed_ops) : Prop :=
    forall t t',
      match ls t , ls t' , es t t' return Prop with
        | Some a , Some b , Some T => @Embed _ a _ _ T
        | _ , _ , _ => True
      end.

  Variable gs : logic_ops.
  Variable es : embed_ops.

  Variable Typ2_tyArr : Typ2 _ Fun.
  Variable Typ0_tyProp : Typ0 _ Prop.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition typeof_func (f : iefunc) : option typ :=
    match f with
      | ief_embed a b =>
        match es a b with
          | None => None
          | Some _ => Some (tyArr a b)
        end
    end.

  Definition typ2_cast_bin (a b c : typ)
  : (typD a -> typD b -> typD c) -> typD (tyArr a (tyArr b c)) :=
    fun f =>
      match eq_sym (typ2_cast a (tyArr b c)) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast  b c) in _ = t
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

  Definition funcD (f : iefunc) :
    match typeof_func f with
      | Some t => typD t
      | None => unit
    end.
  refine (
    match f as f
          return match typeof_func f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | ief_embed t u =>
        match es t u as x
              return match match x with
			     | Some _ => Some (tyArr t u)
			     | None => None
			   end with
		       | Some t0 => typD t0
		       | None => unit
		     end
        with
	  | Some t0 =>
            match eq_sym (typ2_cast t u) in _ = t return t
            with
              | eq_refl => @embed _ _ _
            end
	  | None => tt
        end
    end).
  Defined.

  Global Instance RSym_iefunc : RSym iefunc :=
  { typeof_sym := typeof_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_iefunc : RSymOk RSym_iefunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End typed.
