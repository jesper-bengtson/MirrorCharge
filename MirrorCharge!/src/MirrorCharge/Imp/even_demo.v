Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.SymEvalLemmas.

Require Import MirrorCharge.Imp.incr_demo_stuff.

Require Import Even.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.

Definition EAUTO_using (depth : nat) (lems : list lemma) : imp_tac :=
  REC depth
      (fun rec : imp_tac =>
         FIRST (List.map (fun lem => SOLVE (THEN (EAPPLY lem) rec)) lems))
      IDTAC.

Theorem EAUTO_sound
: forall depth lems,
    Forall ProvableLemma lems ->
    rtac_sound (EAUTO_using depth lems).
Proof.
  intros. unfold EAUTO_using.
  rtac_derive_soundness_with.
  induction H.
  - constructor.
  - constructor; try auto.
    rtac_derive_soundness_with.
Qed.























Definition even_O_lemma : lemma.
reify_lemma even_O.
Defined.
Definition even_S_lemma : lemma.
reify_lemma even_S.
Defined.
Definition odd_S_lemma : lemma.
reify_lemma odd_S.
Defined.


Definition the_tactic : imp_tac :=
  (EAUTO_using 500 (even_S_lemma :: odd_S_lemma :: even_O_lemma :: nil)).

Goal even 400.
  Time repeat constructor.
Time Qed.

Goal even 400.
(*  Time run_tactic the_tactic. *)




Fixpoint make_nat (n : nat) : expr typ func :=
  match n with
    | 0 => fConst 0
    | S n => App fS (make_nat n)
  end.

Fixpoint convert_S (e : expr typ func) : expr typ func :=
  match e with
    | App l r => App (convert_S l) (convert_S r)
    | Abs t e => Abs t (convert_S e)
    | Inj (inl (inr (pNat n))) => make_nat n
    | _ => e
  end.

Definition convert_to_S : imp_tac :=
  fun _ _ _ _ _ sub g =>
    More_ sub (GGoal (convert_S g)).
(** Need to prove this sound... **)

Definition the_tactic' : imp_tac :=
  THEN convert_to_S
       (EAUTO_using 500 (even_S_lemma :: odd_S_lemma :: even_O_lemma :: nil)).

Time run_tactic the_tactic'.
Time Qed.
