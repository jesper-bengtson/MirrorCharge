(** This file introduces a syntactic separation logic.
 **)
Require Import Morphisms.
Require Import ExtLib.Tactics.
Require Import BILogic ILogic Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import SepLogFold.

Set Implicit Arguments.
Set Strict Implicit.

Section syn_sep_log.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Variable SL : typ.

  Variable SLS : SepLogSpec sym.
  Variable ILO : ILogicOps (typD ts nil SL).
  Variable BILO : BILOperators (typD ts nil SL).
  Variable IL : @ILogic _ ILO.
  Variable BIL : @BILogic _ ILO BILO.

  (** TODO: This seems to be defined at the wrong level of abstraction
   ** It is the only piece here that requires that I be in [Ext.expr] rather
   ** than an arbitrary [expr].
   **)
  Variable slsok : SepLogSpecOk RSym_sym SL SLS ILO BILO.

  Record SynSepLog : Type :=
  { e_star : expr sym -> expr sym -> expr sym
  ; e_and : expr sym -> expr sym -> expr sym
  ; e_emp : expr sym
  ; e_true : expr sym
  }.

  Variable SSL : SynSepLog.

  Record SynSepLogOk : Type :=
  { e_empOk : forall us tvs,
              exists val,
                exprD' us tvs SSL.(e_emp) SL = Some val /\
                forall vs, val vs -|- empSP
  ; e_trueOk : forall us tvs,
               exists val,
                 exprD' us tvs SSL.(e_true) SL = Some val /\
                 forall vs, val vs -|- ltrue
  ; e_starOk : forall us tvs x y valx valy,
                 exprD' us tvs x SL = Some valx ->
                 exprD' us tvs y SL = Some valy ->
                 exists val,
                   exprD' us tvs (SSL.(e_star) x y) SL = Some val /\
                   forall vs, val vs -|- valx vs ** valy vs
  ; e_starValid : forall us tvs x y val,
                    exprD' us tvs (SSL.(e_star) x y) SL = Some val ->
                    exists valx valy,
                      exprD' us tvs x SL = Some valx /\
                      exprD' us tvs y SL = Some valy /\
                      forall vs, val vs -|- valx vs ** valy vs
  ; e_andOk : forall us tvs x y valx valy,
                exprD' us tvs x SL = Some valx ->
                exprD' us tvs y SL = Some valy ->
                exists val,
                  exprD' us tvs (SSL.(e_and) x y) SL = Some val /\
                  forall vs, val vs -|- valx vs //\\ valy vs
  ; e_andValid : forall us tvs x y val,
                   exprD' us tvs (SSL.(e_and) x y) SL = Some val ->
                   exists valx valy,
                     exprD' us tvs x SL = Some valx /\
                     exprD' us tvs y SL = Some valy /\
                     forall vs, val vs -|- valx vs //\\ valy vs
  }.

  Variable SSLO : SynSepLogOk.

  (*
    Local Instance PureOp_it : @PureOp _  := slsok.(_PureOp).
    Local Instance Pure_it : @Pure _ _ _ slsok.(_PureOp) := _Pure slsok.
    Hypothesis pure_ltrue : Pure.pure ltrue.
    Hypothesis pure_land : forall p q, Pure.pure p -> Pure.pure q -> Pure.pure (land p q).
   *)

  Ltac forward_ex_and :=
    repeat match goal with
             | H : exists x, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
           end.

  (** Primed versions **)
  Lemma exprD'_e_andOk_None1
  : forall us tvs x y,
      exprD' us tvs x SL = None ->
      exprD' us tvs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    eapply e_andValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_andOk_None2
  : forall us tvs x y,
      exprD' us tvs y SL = None ->
      exprD' us tvs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    eapply e_andValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_starOk_None1
  : forall us tvs x y,
      exprD' us tvs x SL = None ->
      exprD' us tvs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    eapply e_starValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_starOk_None2
  : forall us tvs x y,
      exprD' us tvs y SL = None ->
      exprD' us tvs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    eapply e_starValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_and_None
  : forall us tvs a b,
      exprD' us tvs (SSL.(e_and) a b) SL = None ->
      exprD' us tvs a SL = None \/ exprD' us tvs b SL = None.
  Proof.
    intros.
    consider (exprD' us tvs a SL); intros; auto.
    consider (exprD' us tvs b SL); intros; auto.
    exfalso.
    destruct (@e_andOk SSLO _ _ _ _ _ _ H0 H1).
    intuition; congruence.
  Qed.

  Lemma exprD'_e_star_None
  : forall us tvs a b,
      exprD' us tvs (SSL.(e_star) a b) SL = None ->
      exprD' us tvs a SL = None \/ exprD' us tvs b SL = None.
  Proof.
    intros.
    consider (exprD' us tvs a SL); intros; auto.
    consider (exprD' us tvs b SL); intros; auto.
    exfalso.
    destruct (@e_starOk SSLO _ _ _ _ _ _ H0 H1).
    intuition; congruence.
  Qed.

  (** Unprimed versions **)
  Lemma exprD_e_andOk_None1
  : forall us vs x y,
      exprD us vs x SL = None ->
      exprD us vs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_andValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD_e_andOk_None2
  : forall us vs x y,
      exprD us vs y SL = None ->
      exprD us vs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_andValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD_e_starOk_None1
  : forall us vs x y,
      exprD us vs x SL = None ->
      exprD us vs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_starValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD_e_starOk_None2
  : forall us vs x y,
      exprD us vs y SL = None ->
      exprD us vs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_starValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD_e_and_None
  : forall us vs a b,
      exprD us vs (SSL.(e_and) a b) SL = None ->
      exprD us vs a SL = None \/ exprD us vs b SL = None.
  Proof.
    intros.
    consider (exprD us vs a SL); intros; auto.
    consider (exprD us vs b SL); intros; auto.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    destruct (@e_andOk SSLO _ _ _ _ _ _ H0 H1).
    intuition; congruence.
  Qed.

  Lemma exprD_e_star_None
  : forall us vs a b,
      exprD us vs (SSL.(e_star) a b) SL = None ->
      exprD us vs a SL = None \/ exprD us vs b SL = None.
  Proof.
    intros.
    consider (exprD us vs a SL); intros; auto.
    consider (exprD us vs b SL); intros; auto.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    destruct (@e_starOk SSLO _ _ _ _ _ _ H0 H1).
    intuition; congruence.
  Qed.

  Lemma exprD_e_empOk
  : forall us vs,
    exists val : typD ts nil SL,
      exprD us vs SSL.(e_emp) SL = Some val /\
      (val -|- empSP).
  Proof.
    unfold exprD; intros; destruct (split_env vs).
    destruct (SSLO.(e_empOk) us x) as [ ? [ ? ? ] ].
    rewrite H. eauto.
  Qed.

  Lemma exprD_e_trueOk
  : forall us vs,
    exists val,
      exprD us vs SSL.(e_true) SL = Some val /\
      (val -|- ltrue).
  Proof.
    unfold exprD; intros; destruct (split_env vs).
    destruct (SSLO.(e_trueOk) us x) as [ ? [ ? ? ] ].
    rewrite H. eauto.
  Qed.

  Lemma exprD_e_starOk
  : forall us vs x y valx valy,
      exprD us vs x SL = Some valx ->
      exprD us vs y SL = Some valy ->
      exists val,
        exprD us vs (SSL.(e_star) x y) SL = Some val /\
        (val -|- valx ** valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs).
    forward.
    destruct (@e_starOk SSLO us x0 x y _ _ H H0) as [ ? [ ? ? ] ].
    rewrite H3. inv_all; subst. eauto.
  Qed.

  Lemma exprD_e_starValid
  : forall us vs x y val,
      exprD us vs (SSL.(e_star) x y) SL = Some val ->
      exists valx valy,
        exprD us vs x SL = Some valx /\
        exprD us vs y SL = Some valy /\
        (val -|- valx ** valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs).
    forward.
    edestruct (@e_starValid SSLO us x0 x) as [ ? [ ? [ ? [ ? ? ] ] ] ]; eauto.
    Cases.rewrite_all_goal.
    inv_all; subst. eauto.
  Qed.

  Lemma exprD_e_andOk
  : forall us vs x y valx valy,
      exprD us vs x SL = Some valx ->
      exprD us vs y SL = Some valy ->
      exists val,
        exprD us vs (SSL.(e_and) x y) SL = Some val /\
        (val -|- valx //\\ valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs).
    forward.
    destruct (@e_andOk SSLO us x0 x y _ _ H H0) as [ ? [ ? ? ] ].
    rewrite H3. inv_all; subst. eauto.
  Qed.

  Lemma exprD_e_andValid
  : forall us vs x y val,
      exprD us vs (SSL.(e_and) x y) SL = Some val ->
      exists valx valy,
        exprD us vs x SL = Some valx /\
        exprD us vs y SL = Some valy /\
        (val -|- valx //\\ valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs).
    forward.
    edestruct (@e_andValid SSLO us x0 x) as [ ? [ ? [ ? [ ? ? ] ] ] ]; eauto.
    Cases.rewrite_all_goal.
    inv_all; subst. eauto.
  Qed.

  Ltac go_crazy :=
    match goal with
      | H : exprD' _ _ _ _ = _ , H' : _ |- _ =>
        rewrite H in H'
      | H : exprD' _ _ _ _ = _ |- _ =>
        rewrite H
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ] =>
        destruct (@e_andOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ] =>
        destruct (@e_starOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ (SSL.(e_and) _ _) _ = _ |- _ =>
        eapply SSLO.(e_andValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
      | H : exprD' _ _ (SSL.(e_star) _ _) _ = _ |- _ =>
        eapply SSLO.(e_starValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
                   , H'' : context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ]
        |- _ =>
        destruct (@e_starOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
                   , H'' : context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ]
        |- _ =>
        destruct (@e_andOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ _ _ = None |- _ =>
        first [ erewrite (@exprD'_e_starOk_None1 _ _ _ _ H) in *
              | erewrite (@exprD'_e_starOk_None2 _ _ _ _ H) in *
              | erewrite (@exprD'_e_andOk_None1 _ _ _ _ H) in *
              | erewrite (@exprD'_e_andOk_None2 _ _ _ _ H) in * ]

      | H : exprD' _ _ _ _ = None |- _ =>
        first [ congruence
              | apply exprD'_e_star_None in H; destruct H; try congruence
              | apply exprD'_e_and_None in H; destruct H; try congruence ]
    end.

  Local Instance Reflexive_lentails : Reflexive lentails.
  Proof.
    destruct IL. destruct lentailsPre. auto.
  Qed.

  Require Import MirrorCore.Ext.ExprSem.

  Lemma Sem_equiv_e_and_assoc
  :forall us vs, forall a b c : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_and) a (SSL.(e_and) b c)) (SSL.(e_and) (SSL.(e_and) a b) c).
  Proof.
    clear - IL SSL SSLO. intros.
    red. intros.
    unfold exprD. destruct (split_env vs).
    consider (exprD' us x (SSL.(e_and) a (SSL.(e_and) b c)) SL);
      consider (exprD' us x (SSL.(e_and) (SSL.(e_and) a b) c) SL); intros; auto.
    { eapply e_andValid in H; eauto. eapply e_andValid in H0; eauto.
      do 2 destruct H; do 2 destruct H0.
      destruct H0. destruct H1. destruct H. destruct H3.
      eapply e_andValid in H; eauto. do 3 destruct H. destruct H5.
      eapply e_andValid in H1; eauto. do 3 destruct H1. destruct H7.
      rewrite H4. rewrite H2. rewrite H6. rewrite H8.
      rewrite H0 in *. rewrite H5 in *. rewrite H7 in *.
      inv_all; subst.
      symmetry. eapply landA. }
    { eapply e_andValid in H0; eauto.
      do 3 destruct H0. destruct H1.
      eapply e_andValid in H1; eauto.
      do 3 destruct H1. destruct H3.
      destruct (@e_andOk SSLO _ _ _ _ _ _ H0 H1). destruct H5.
      destruct (@e_andOk SSLO _ _ _ _ _ _ H5 H3). destruct H7.
      congruence. }
    { eapply e_andValid in H; eauto.
      do 3 destruct H. destruct H1.
      eapply e_andValid in H; eauto.
      do 3 destruct H. destruct H3.
      destruct (@e_andOk SSLO _ _ _ _ _ _ H3 H1). destruct H5.
      destruct (@e_andOk SSLO _ _ _ _ _ _ H H5). destruct H7.
      congruence. }
  Qed.

  Lemma Sem_equiv_e_star_assoc
  : forall us vs, forall a b c : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_star) a (SSL.(e_star) b c)) (SSL.(e_star) (SSL.(e_star) a b) c).
  Proof.
    clear - IL SSL SSLO BIL. intros.
    red. unfold exprD. destruct (split_env vs).
    consider (exprD' us x (SSL.(e_star) a (SSL.(e_star) b c)) SL);
      consider (exprD' us x (SSL.(e_star) (SSL.(e_star) a b) c) SL); intros; auto.
    { eapply e_starValid in H; eauto. eapply e_starValid in H0; eauto.
      do 2 destruct H; do 2 destruct H0.
      destruct H0. destruct H1. destruct H. destruct H3.
      eapply e_starValid in H; eauto. do 3 destruct H. destruct H5.
      eapply e_starValid in H1; eauto. do 3 destruct H1. destruct H7.
      rewrite H4. rewrite H2. rewrite H6. rewrite H8.
      rewrite H0 in *. rewrite H5 in *. rewrite H7 in *.
      inv_all; subst.
      symmetry. eapply sepSPA. }
    { eapply e_starValid in H0; eauto.
      do 3 destruct H0. destruct H1.
      eapply e_starValid in H1; eauto.
      do 3 destruct H1. destruct H3.
      destruct (@e_starOk SSLO _ _ _ _ _ _ H0 H1). destruct H5.
      destruct (@e_starOk SSLO _ _ _ _ _ _ H5 H3). destruct H7.
      congruence. }
    { eapply e_starValid in H; eauto.
      do 3 destruct H. destruct H1.
      eapply e_starValid in H; eauto.
      do 3 destruct H. destruct H3.
      destruct (@e_starOk SSLO _ _ _ _ _ _ H3 H1). destruct H5.
      destruct (@e_starOk SSLO _ _ _ _ _ _ H H5). destruct H7.
      congruence. }
  Qed.

  Lemma Sem_equiv_Proper_e_and
  : forall us vs,
      Proper (Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs) SSL.(e_and).
  Proof.
    unfold Sem_equiv. red. red. red.
    unfold exprD. intros.
    destruct (split_env vs).
    match goal with
      | |- match ?X with _ => _ end =>
        consider X; intros
    end; repeat go_crazy; forward; repeat go_crazy.
    { inv_all; subst.
      intros.
      forward.
      repeat go_crazy.
      inv_all; subst.
      Cases.rewrite_all.
      reflexivity. }
  Qed.

  Lemma Sem_equiv_Proper_e_star
  : forall us vs,
      Proper (Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs) SSL.(e_star).
  Proof.
    unfold Sem_equiv; do 3 red; simpl; intros.
    unfold exprD in *.
    destruct (split_env vs).
    match goal with
      | |- match ?X with _ => _ end =>
        consider X; intros
    end; repeat go_crazy; forward; repeat go_crazy.
    { inv_all; subst. forward.
      repeat go_crazy.
      inv_all; subst.
      Cases.rewrite_all.
      reflexivity. }
  Qed.

  Lemma ltrue_unitL : forall a, land ltrue a -|- a.
  Proof.
    clear - IL; intros.
    split.
    { eapply landL2. reflexivity. }
    { eapply landR; try reflexivity. eapply ltrueR. }
  Qed.

  Lemma ltrue_unitR : forall a, land a ltrue -|- a.
  Proof.
    clear - IL; intros.
    split.
    { eapply landL1. reflexivity. }
    { eapply landR; try reflexivity. eapply ltrueR. }
  Qed.

  Lemma empSPR : forall a, a ** empSP -|- a.
  Proof.
    clear - BIL IL; intros.
    rewrite sepSPC. rewrite empSPL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitLL
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs (SSL.(e_and) SSL.(e_true) a) a.
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_trueOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all_goal. clear - IL.
    rewrite ltrue_unitL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitLR
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs (SSL.(e_and) a SSL.(e_true)) a.
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_trueOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - IL.
    rewrite ltrue_unitR. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitRL
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs a (SSL.(e_and) SSL.(e_true) a).
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_trueOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - IL.
    rewrite ltrue_unitL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitRR
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs a (SSL.(e_and) a SSL.(e_true)).
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_trueOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - IL.
    rewrite ltrue_unitR. reflexivity.
  Qed.


  Lemma Sem_equiv_e_emp_e_star_unitLL
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs (SSL.(e_star) SSL.(e_emp) a) a.
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_empOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - BIL IL.
    rewrite empSPL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitLR
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs (SSL.(e_star) a SSL.(e_emp)) a.
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_empOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - BIL IL.
    rewrite empSPR. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitRL
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs a (SSL.(e_star) SSL.(e_emp) a).
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_empOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - BIL IL.
    rewrite empSPL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitRR
  : forall tus tvs, forall a : expr sym,
      Sem_equiv _ SL lequiv tus tvs a (SSL.(e_star) a SSL.(e_emp)).
  Proof.
    red; intros.
    unfold exprD. destruct (split_env tvs).
    destruct (SSLO.(e_empOk) tus x) as [ ? [ ? ? ] ].
    consider (exprD' tus x a SL); intros; repeat go_crazy; auto.
    inv_all; subst; intros.
    Cases.rewrite_all. clear - BIL IL.
    rewrite empSPR. reflexivity.
  Qed.

End syn_sep_log.

(** Ltac's local to a section are not re-introduced **)
Ltac go_crazy SSL SSLO :=
  match goal with
    | [ H : exprD' _ _ _ _ = _ , H' : _ |- _ ] =>
      rewrite H in H'
    | [ H : exprD' _ _ _ _ = _ |- _ ] =>
      rewrite H
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      |- context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ] ] =>
      destruct (@e_andOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      |- context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ] ] =>
      destruct (@e_starOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ (SSL.(e_and) _ _) _ = _ |- _ ] =>
      eapply SSLO.(e_andValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD' _ _ (SSL.(e_star) _ _) _ = _ |- _ ] =>
      eapply SSLO.(e_starValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      , H'' : context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@e_starOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      , H'' : context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@e_andOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ _ _ = None |- _ ] =>
      first [ erewrite (@exprD'_e_starOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD'_e_starOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD'_e_andOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD'_e_andOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in * ]
    | [ H : exprD' _ _ _ _ = None |- _ ] =>
      first [ congruence
            | apply (@exprD'_e_star_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence
            | apply (@exprD'_e_and_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence ]


    | [ H : exprD _ _ _ _ = _ , H' : _ |- _ ] =>
      rewrite H in H'
    | [ H : exprD _ _ _ _ = _ |- _ ] =>
      rewrite H
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      |- context [ exprD ?A ?B (SSL.(e_and) ?C ?D) ?T ] ] =>
      destruct (@exprD_e_andOk _ _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      |- context [ exprD ?A ?B (SSL.(e_star) ?C ?D) ?T ] ] =>
      destruct (@exprD_e_starOk _ _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD _ _ (SSL.(e_and) _ _) _ = _ |- _ ] =>
      eapply (@exprD_e_andValid _ _ _ _ _ _ _ _ SSLO) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD _ _ (SSL.(e_star) _ _) _ = _ |- _ ] =>
      eapply (@exprD_e_starValid _ _ _ _ _ _ _ _ SSLO) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      , H'' : context [ exprD ?A ?B (SSL.(e_star) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@exprD_e_starOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      , H'' : context [ exprD ?A ?B (SSL.(e_and) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@exprD_e_andOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]

    | [ H : exprD _ _ _ _ = None |- _ ] =>
      first [ erewrite (@exprD_e_starOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD_e_starOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD_e_andOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD_e_andOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in * ]

    | [ H : exprD _ _ _ _ = None |- _ ] =>
      first [ congruence
            | apply (@exprD_e_star_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence
            | apply (@exprD_e_and_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence ]
  end.