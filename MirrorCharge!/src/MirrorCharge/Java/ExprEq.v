Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.Lambda.Expr.

Section ExprEq.
  Context {typ func : Type}.
  Context {eq_typ : typ -> typ -> Prop} {RelDec_typ : RelDec eq_typ}.
  Context {eq_func : func -> func -> Prop} {RelDec_func : RelDec eq_func}.
 
  Context {RelDec_Correct_typ : RelDec_Correct RelDec_typ}.
  Context {RelDec_Correct_func : RelDec_Correct RelDec_func}.

  Set Implicit Arguments.
  Set Strict Implicit.

  Fixpoint expr_eq (e1 e2 : expr typ func) : Prop :=
  	match e1, e2 with
  	  | Var v1, Var v2 => v1 = v2
  	  | Inj f1, Inj f2 => eq_func f1 f2
  	  | App a b, App c d => expr_eq a c /\ expr_eq b d
  	  | Abs t a, Abs u b => eq_typ t u /\ expr_eq a b
  	  | UVar u1, UVar u2 => u1 = u2
  	  | _, _ => False
  	end.
  	
  Fixpoint expr_eqb (e1 e2 : expr typ func) : bool :=
  	match e1, e2 with
  	  | Var v1, Var v2 => v1 ?[ eq ] v2
  	  | Inj f1, Inj f2 => f1 ?[ eq_func ] f2
  	  | App a b, App c d => (expr_eqb a c && expr_eqb b d)%bool
  	  | Abs t a, Abs u b => (t ?[ eq_typ ] u && expr_eqb a b)%bool
  	  | UVar u1, UVar u2 => u1 ?[ eq ] u2
  	  | _, _ => false
  	end.

  Lemma expr_eqb_sound (e1 e2 : expr typ func) (H : expr_eqb e1 e2 = true) :
  	expr_eq e1 e2.
  Proof.
    generalize dependent e2; induction e1; intros;
    destruct e2; simpl in *; try intuition congruence.
    + apply rel_dec_correct; assumption.
    + apply rel_dec_correct; assumption.
	+ rewrite Bool.andb_true_iff in H; destruct H as [H1 H2].
	  split; [apply IHe1_1 | apply IHe1_2]; assumption.
	+ rewrite Bool.andb_true_iff in H; destruct H as [H1 H2].
      split; [apply rel_dec_correct | apply IHe1]; assumption.
    + apply rel_dec_correct; assumption.
  Qed.

  Lemma expr_eqb_complete (e1 e2 : expr typ func) (H : expr_eq e1 e2) :
  	expr_eqb e1 e2 = true.
  Proof.
    generalize dependent e2; induction e1; intros;
    destruct e2; simpl in *; try intuition congruence.
    + apply rel_dec_eq_true; [apply _ | assumption].
    + apply rel_dec_eq_true; assumption.
	+ rewrite Bool.andb_true_iff; destruct H as [H1 H2].
	  split; [apply IHe1_1 | apply IHe1_2]; assumption.
	+ rewrite Bool.andb_true_iff; destruct H as [H1 H2].
      split; [apply rel_dec_correct | apply IHe1]; assumption.
    + apply rel_dec_eq_true; [apply _ | assumption].
  Qed.

  Global Instance RelDec_expr : RelDec expr_eq := {
  	rel_dec := expr_eqb
  }.
  
  Global Instance RelDec_Correct_expr : RelDec_Correct RelDec_expr.
  Proof.
	split; destruct x, y; simpl; intros; try intuition congruence.
	+ consider (v ?[ eq ] v0); intuition congruence.
	+ consider (f ?[ eq_func] f0); intuition congruence.
	+ rewrite Bool.andb_true_iff. 
	  intuition; auto using expr_eqb_sound, expr_eqb_complete.
	+ rewrite Bool.andb_true_iff.
	  consider (t ?[ eq_typ ] t0);
	  intuition; auto using expr_eqb_sound, expr_eqb_complete.
    + consider (u ?[ eq ] u0); intuition congruence.
  Qed.	

End ExprEq.