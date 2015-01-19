Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.Goal.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.SymEvalLemmas.
Require MirrorCharge.Imp.STacCancel.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.RTacTauto.
Require Import Coq.Strings.String.

Require Import MirrorCharge.Imp.incr_demo_stuff.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.

Lemma land_apply
: forall P Q x,
    @ILogic.land Imp.lprop Imp.ILogicOps_lprop P Q x =
    @ILogic.land Imp.HProp Imp.ILogicOps_HProp (P x) (Q x).
Admitted.
Lemma get_upd_not
: forall x y x0 m,
    x <> y ->
    Imp.locals_get x (Imp.locals_upd y x0 m) =
    Imp.locals_get x m.
Admitted.
Lemma and_split
: forall G P Q : Imp.HProp,
    @ILogic.lentails Imp.HProp Imp.ILogicOps_HProp
     G P ->
    @ILogic.lentails Imp.HProp Imp.ILogicOps_HProp
     G Q ->
    @ILogic.lentails Imp.HProp Imp.ILogicOps_HProp
     G
     (@ILogic.land Imp.HProp Imp.ILogicOps_HProp P Q).
Admitted.
Lemma eq_trans_hyp
: forall a b c d: nat,
    a = c + 1 ->
    c = d ->
    d + 1 = b ->
    a = b.
Proof. intros; subst. reflexivity. Qed.
Lemma prove_Prop :
forall P : Prop,
  P ->
  @ILogic.lentails Imp.HProp Imp.ILogicOps_HProp
                   (@ILogic.ltrue Imp.HProp Imp.ILogicOps_HProp)
                   (@ILEmbed.embed Prop Imp.HProp Imp.EmbedOp_Prop_HProp P).
Proof. Admitted.

Fixpoint assign_linear from (ls : list string) : Imp.lprop :=
  match ls with
    | nil => (@ILogic.ltrue _ Imp.ILogicOps_lprop)
    | l :: nil => (fun mem => @ILEmbed.embed _ _ Imp.EmbedOp_Prop_HProp  (Imp.locals_get l mem = from))
    | l :: ls =>
      (@ILogic.land _ Imp.ILogicOps_lprop)
        (assign_linear (S from) ls)
        (fun mem => @ILEmbed.embed _ _ Imp.EmbedOp_Prop_HProp  (Imp.locals_get l mem = from))
  end.

Fixpoint increment_all (ls : list string) : Imp.icmd :=
  match ls with
    | nil => Imp.Skip
    | l :: nil => (Imp.Assign l (Imp.iPlus (Imp.iVar l) (Imp.iConst 1)))
    | l :: ls => Imp.Seq (Imp.Assign l (Imp.iPlus (Imp.iVar l) (Imp.iConst 1))) (increment_all ls)
  end.

Definition tonums (ls : list nat) : list string :=
  map (fun n => String (Ascii.ascii_of_nat (65 + n)) EmptyString) ls.

Fixpoint seq (n : nat) : list nat :=
  match n with
    | 0 => nil
    | S n => n :: seq n
  end.

Ltac reducer :=
  unfold seq, tonums, map, Ascii.ascii_of_nat, Ascii.ascii_of_N, plus, BinNat.N.of_nat, increment_all, Swap_n, assign_linear, Datatypes.length;
  simpl; unfold Ascii.ascii_of_pos; unfold Ascii.shift; unfold Ascii.one.

Create HintDb reduce_stuff.
Hint Rewrite Imp.locals_get_locals_upd Imp.eval_iexpr_iPlus
     Imp.eval_iexpr_iConst Imp.eval_iexpr_iVar land_apply : reduce_stuff.
Hint Rewrite get_upd_not using congruence : reduce_stuff.


Goal let lst := (tonums (seq 10)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Ltac ltac_solver :=
  repeat first [ apply Imp.triple_exL ; apply ILogic.lforallR ; intro
                  | apply Imp.Assign_seq_rule
                  | apply Imp.Skip_seq_rule
                  | apply Imp.Assign_tail_rule
                  | apply Imp.Skip_tail_rule ];
  eapply Imp.embed_ltrue;
  eapply Imp.go_lower_raw;
  intros;
  eapply ILogic.lexistsL; intros;
  autorewrite with reduce_stuff;
  repeat (eapply Imp.pull_embed_hyp; intros);
  eapply Imp.pull_embed_last_hyp; intros;
  subst;
  repeat eapply and_split; eapply prove_Prop; assumption.
Time ltac_solver.
Qed.


(** Try to use computaitonal reflection
 **)
Definition sym_eval_only (n : nat) (rest : imp_tac) : imp_tac :=
  REC n (fun rec : imp_tac =>
           let rec : imp_tac := THENS (simplify_tac :: rec :: nil) in
           TRY (FIRST (   EAPPLY_THEN triple_exL_lemma
                            (THEN INTRO_All rec)
                       :: EAPPLY_THEN Assign_seq_lemma rec
                       :: EAPPLY_THEN Skip_seq_lemma rec
                       :: EAPPLY_THEN Assign_tail_lemma rest
                       :: EAPPLY_THEN Skip_tail_lemma rest
                       :: nil)))
      IDTAC.


Hint Immediate Imp.SeqA_rule
     Imp.Assign_seq_rule Imp.Assign_tail_rule
     Imp.Read_seq_rule Imp.Read_tail_rule
     Imp.Write_seq_rule Imp.Write_tail_rule
     Imp.triple_exL Imp.Skip_seq_rule
     Imp.Assert_seq_rule
     Imp.Assert_tail_rule Imp.Skip_tail_rule
: the_hints.


Theorem sym_eval_only_sound
: forall n r, rtac_sound r -> rtac_sound (sym_eval_only n r).
Proof.
  intros. unfold sym_eval_only.
  rtac_derive_soundness_with.
Qed.






Definition PHASE1 : imp_tac :=
  sym_eval_only 100 IDTAC.

Theorem PHASE1_sound : rtac_sound PHASE1.
Proof. eapply sym_eval_only_sound; rtac_derive_soundness_with. Qed.

Goal let lst := (tonums (seq 10)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time (run_tactic PHASE1).
Ltac ltac_finish :=
  (intros; eapply Imp.embed_ltrue;
   eapply ILogic.lexistsL; intros;
   eapply Imp.go_lower_raw; intro;
   autorewrite with reduce_stuff;
   repeat (eapply Imp.pull_embed_hyp; intros);
   try (eapply Imp.pull_embed_last_hyp; intros);
   subst;
   repeat eapply and_split; eapply prove_Prop; assumption).

intros. ltac_finish.
Qed.


(** Need a few lemmas to finish things off **)
Definition andI_lemma : lemma.
reify_lemma and_split.
Defined.
Definition prove_Prop_lemma : lemma.
reify_lemma prove_Prop.
Defined.
Definition eq_trans_hyp_lemma : lemma.
reify_lemma eq_trans_hyp. (** specialization of [subst] **)
Defined.


(** Custom reflective procedure to redue [n + m] for constants [n] and [m]
 **)
Fixpoint nat_red (e : expr typ func) : expr typ func :=
  match e with
    | App (App (Inj (inl (inr natPlus))) (Inj (inl (inr (pNat l))))) (Inj (inl (inr (pNat r)))) =>
      Inj (inl (inr (pNat (l + r))))
    | _ => e
  end.

(** reduce and then check for equality **)
Definition prove_eq_tac : imp_tac :=
  fun _ _ _ _ _ sub e =>
    match e with
      | App (App (Inj (inl (inr (pEq t)))) L) R =>
        let l' := nat_red L in
        let r' := nat_red R in
        if l' ?[ eq ] r' then Solved sub
        else More_ sub (GGoal (App (App (Inj (inl (inr (pEq t)))) l') r'))
      | _ => Fail
    end.

(** Translate ltac_finish **)
Definition PHASE3 : imp_tac :=
  sym_eval_only 100
     (THENS (TRY (EAPPLY embed_ltrue_lemma) ::
            TRY (THENS (EAPPLY entails_exL_lemma ::
                        INTRO_All ::
                 BETA_REDUCE :: nil)) ::
            TRY (THENS (EAPPLY go_lower_raw_lemma ::
                        BETA_REDUCE :: INTRO_All ::
                        BETA_REDUCE :: nil)) ::
            SIMPLIFY :: SIMPLIFY ::
            REPEAT 200
               (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil)) ::
            TRY (THENS (EAPPLY pull_embed_last_lemma :: INTRO_Hyp :: nil)) ::
            REPEAT 1000 (EAPPLY andI_lemma) ::
             TRY (EAPPLY prove_Prop_lemma) ::
             TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                         TRY EASSUMPTION :: nil)) ::
             INSTANTIATE :: TRY prove_eq_tac :: nil)).

Goal let lst := (tonums (seq 20)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time run_tactic (PHASE3).
Time Qed.


Goal let lst := (tonums (seq 10)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time ltac_solver.
Undo.
Time (run_tactic PHASE1; ltac_finish).
Undo.
Time run_tactic (PHASE3).
Time Qed.



































Definition EAUTO_using (depth : nat) (lems : list lemma) : imp_tac :=
  REC depth
      (fun rec : imp_tac =>
         FIRST (List.map (fun lem => SOLVE (THEN (EAPPLY lem) rec)) lems))
      IDTAC.

Definition ProvableLemma (l : lemma) : Prop :=
  Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil l.

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




(** END OF FILE **)
