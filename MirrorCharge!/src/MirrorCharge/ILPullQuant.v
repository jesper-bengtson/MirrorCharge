Require Import ILogic ILInsts.
Require Import ILogicFunc.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.TypesI.
Require Import MapPositive.
Require Import MirrorCore.SymI.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Data.Positive.
Require Import MirrorCore.Lambda.ExprLift.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.EnvI.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import Relation_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
(*
Definition inhabited (ts : types)  := forall (t : typ),
  option (Inhabited (typD ts nil t)).
*)
Check logic_ops.

Check RSym_ilfunc.

Section PullQuant.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable Typ0_typ : Typ0 RType_typ Prop.

  Variable func : Type.
  Variable RSym_func : RSym func.

  Context (gs : logic_ops RType_typ).
  Context {gsOk : logic_opsOk gs}.
  
  Context {es : embed_ops RType_typ}.
  Context {esOk : embed_opsOk gs es}.
  
  Context {Req : RelDec (@eq typ)}.
  
(*
  Context (ts : typs) (funcs : fun_map ts).
  Context (gs : logic_ops ts) {gsOk : logic_opsOk gs}.
  Context {es : embed_ops ts} {esOk : embed_opsOk gs es}.
  Context {is : inhabited ts}.
*)
Check embed_ops.
  Definition TT := option (list typ * expr typ (ilfunc typ))%type.

  Local Instance RSym_sym : SymI.RSym (ilfunc typ) := RSym_ilfunc _ gs es _ _.

  Let T:Type := tenv typ -> tenv typ -> TT.
  Definition atomic (e : expr typ (ilfunc typ)) : T := fun _ _ => Some (nil, e).

  Definition pq_var (v : var) : T := atomic (Var v).
  Definition pq_uvar (u : uvar) : T := atomic (UVar u).
  Definition pq_inj (s : ilfunc typ) : T := atomic (Inj s).
  Definition pq_abs (x : typ) (e : expr typ (ilfunc typ)) (_ : T) : T :=
    atomic (Abs x e).

  Definition pq_app (f : expr typ (ilfunc typ)) (_ : T) (args : list (expr typ (ilfunc typ) * T)) : T :=
    fun us vs =>
    match f, args with
      | Inj (ilf_true t), nil => (atomic f) us vs
      | Inj (ilf_and t), (_, a)::(_, b)::nil =>
        match a us vs, b us vs with
          | Some (xs, a), Some (ys, b) => Some (xs ++ ys,
                                                App (App f (lift 0 (length ys) a))
                                                    (lift (length ys) (length xs) b))
          | _, _                       => None
        end
      | Inj (ilf_or t), (_, a)::(_, b)::nil =>
        match a us vs, b us vs with
          | Some (xs, a), Some (ys, b) => Some (xs ++ ys,
                                                App (App f (lift 0 (length ys) a))
                                                    (lift (length ys) (length xs) b))
          | _, _                       => None
        end
      | _, _ => None
    end.


  Definition pq_exists (t t_logic : typ) (_ : expr typ (ilfunc typ)) (a : T) : T :=
    fun us vs =>
      match a us (t :: vs) with
  	| Some (ts, a) => Some (t :: ts, a)
	| None => None
      end.

  Definition pqArgs : AppFullFoldArgs ilfunc TT :=
    @Build_AppFullFoldArgs ilfunc TT pq_var pq_uvar pq_inj pq_abs pq_app.

  Definition add_quants (xs : list typ) (t : typ) (e : expr ilfunc) :=
    fold_right (fun x a => App (Inj (ilf_exists x t))
                               (Abs x a)) e xs.

  Definition Teval (e : TT) (t : typ) :=
    match e with
      | Some (xs, a) =>
        Some (add_quants xs t a)
      | None         => None
    end.

  Definition TD (t : typ) (e : TT) (us : env (typD ts)) (vs : tenv typ) :=
    match Teval e t with
      | Some e => exprD' us vs e t
      | None   => None
    end.

  Definition Ttype (ts us : tenv typ) (e : TT) (t : typ) :=
    match Teval e t with
      | Some e => typeof_expr ts us e
      | None   => None
    end.

  Definition PQtype (e : expr ilfunc) (tt : TT) (us vs : tenv typ) :=
    match typeof_expr us vs e with
      | Some t =>
        match Ttype us vs tt t with
          | Some t' => t ?[eq] t' = true
          | None    => True
        end
      | None => True
    end.

  Definition PQR (t : typ) (e : expr ilfunc) (arg : TT) (us : env (typD ts)) (vs : tenv typ) :=
    match TD t arg us vs, exprD' us vs e t, gs t with
      | None, _, _ => True
      | _, _, None => True
      | Some p, Some q, Some _ => forall vs, (p vs) |-- (q vs)
      | _, _, _ => False
    end.

  Lemma ILogic_from_env (t : typ) (i : ILogicOps (typD ts nil t)) (pf : gs t = Some i)
  : @ILogic _ i.
  Proof.
    specialize (gsOk t).
    rewrite pf in *. assumption.
  Defined.
  Hint Extern 1 (@ILogic _ _) => (apply ILogic_from_env; [ assumption ]) : typeclass_instances.

  Lemma Refl_from_env (t : typ) (i : ILogicOps (typD ts nil t)) (pf : gs t = Some i)
  : Reflexive (@lentails _ i).
  Proof.
    specialize (gsOk t).
    rewrite pf in *.
    destruct gsOk. apply lentailsPre.
  Defined.
  Hint Extern 1 (Reflexive _) => (apply Refl_from_env; [ assumption ]) : typeclass_instances.

  Lemma Refl_from_env_lequiv (t : typ) (i : ILogicOps (typD ts nil t)) (pf : gs t = Some i)
  : Reflexive (@lequiv _ i).
  Proof.
    specialize (gsOk t).
    rewrite pf in *.
    destruct gsOk. red. red. intros.
    split; reflexivity.
  Defined.
  Hint Extern 1 (Reflexive _) => (apply Refl_from_env_lequiv; [ assumption ]) : typeclass_instances.

  Lemma Hatomic tus tvs t e (H : typeof_expr (typeof_env tus) tvs e = Some t) :
    PQR t e (atomic e (typeof_env tus) tvs) tus tvs.
  Proof.
    unfold atomic, PQR, TD; simpl. forward.
    reflexivity.
  Qed.

  Lemma Habs
  : forall tus tvs t t' e e_res,
      typeof_expr (typeof_env tus) tvs (Abs t e) = Some (tyArr t t') ->
      @PQR t' e (e_res (typeof_env tus) (t :: tvs)) tus (t :: tvs) ->
      @PQR (tyArr t t') (Abs t e) (pq_abs t e e_res (typeof_env tus) tvs) tus tvs.
  Proof.
    intros; apply Hatomic; assumption.
  Qed.

  Lemma Hex
  : forall (tus : env (typD ts)) (tvs : tenv typ) t t_logic e (e_res : T),
      typeof_expr (typeof_env tus) tvs (App (Inj (ilf_exists t t_logic)) (Abs t e)) = Some t_logic ->
      PQR t_logic e (e_res (typeof_env tus) (t :: tvs)) tus (t :: tvs) ->
      PQR t_logic
          (App (Inj (ilf_exists t t_logic)) (Abs t e))
          (@pq_exists t t_logic e e_res (typeof_env tus) tvs) tus tvs.
  Proof.
    intros.
    unfold PQR, pq_exists in *; simpl in *.
    red_exprD; forward; inv_all; subst.
    red_exprD; forward; inv_all; subst.
    red_exprD.
    unfold type_of_apply in H2; simpl in H2. forward. destruct H2; subst. inv_all; subst.
    remember (e_res (typeof_env tus) (t :: tvs)) as o; destruct o; [| compute in H4; congruence].
    destruct p; simpl in *.
    unfold TD in H4; simpl in H4. inv_all; subst.
    red_exprD; forward; inv_all. clear H12. revert H9; subst; intros.
    red_exprD; forward; inv_all; subst.
    simpl in *. forward. simpl in *. inv_all; subst.
    red_exprD. inv_all; subst.
    clear H2 H3.
    unfold TD, Teval in H1.
    forward. inv_all. subst.
    apply lexistsL; intro x. apply lexistsR with x.
    inv_all; subst. apply H3.
  Qed.

  Lemma typeof_expr_apps uvs vvs e lst (H: typeof_expr uvs vvs e = None) :
    typeof_expr uvs vvs (apps e lst) = None.
  Proof.
    generalize dependent e; induction lst; intros; simpl.
    + apply H.
    + apply IHlst; simpl; rewrite H; reflexivity.
  Qed.

  (** Note: [forward] will do this **)
  Ltac PQtype_elim :=
    match goal with
      | |- match ?o with | Some _ => _ | None => True end => destruct o; apply I
    end.

  Lemma exprD'_add_quants_cons_Some (Ty : typ) (IL_Ty : ILogicOps (typD ts nil Ty))
        (_ : gs Ty = Some IL_Ty)
  : forall tus tvs tm a b x,
      exprD' tus tvs (add_quants (a :: b) Ty tm) Ty = Some x ->
      exists y,
        exprD' tus (a :: tvs) (add_quants b Ty tm) Ty = Some y /\
        forall g, x g -|- lexists (fun v => y (HList.Hcons v g)).
  Proof.
    simpl.
    intros.
    red_exprD. forward. subst.
    revert H4. inv_all. subst Ty. subst i.
    intros. inv_all. subst p.
    revert H5. subst.
    red_exprD. forward. subst.
    inv_all. subst.
    eexists. split.
    { reflexivity. }
    { intros.
      unfold typeof_sym in *. simpl in *.
      rewrite H in *.
      red_exprD. uip_all.
      inv_all. subst.
      reflexivity. }
  Qed.

  Require Import ExtLib.Data.HList.

  Lemma exists_hlist_app (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty))
        (IL_Ty : ILogic (typD ts nil Ty))
  : forall xs ys (P : _ -> typD ts nil Ty),
      Exists v : HList.hlist (typD ts nil) (xs ++ ys), P v -|-
                                                         Exists v : HList.hlist (typD ts nil) xs,
    Exists v' : HList.hlist (typD ts nil) ys, P (HList.hlist_app v v').
  Proof.
    split.
    { apply lexistsL; intros.
      rewrite <- hlist_app_hlist_split with (h := x).
      eapply lexistsR.
      eapply lexistsR.
      reflexivity. }
    { do 2 (apply lexistsL; intros).
      eapply lexistsR.
      reflexivity. }
  Qed.

  Lemma lexists_iff_2 (Ty : Type) (ILO_Ty : ILogicOps Ty)
        (IL_Ty : ILogic Ty)
  : forall T U (P Q : T -> U -> Ty),
      (forall a b, P a b -|- Q a b) ->
      Exists x : T, Exists y : U, P x y -|-
                                    Exists y : U, Exists x : T, Q x y.
  Proof.
    split.
    { apply lexistsL; intros.
      apply lexistsL; intros.
      eapply lexistsR; eauto.
      eapply lexistsR; eauto. eapply H. }
    { apply lexistsL; intros.
      apply lexistsL; intros.
      eapply lexistsR; eauto.
      eapply lexistsR; eauto. eapply H. }
  Qed.

(* Why both lemmas? *)

  Lemma lexists_iff_2_rw (Ty : Type) (ILO_Ty : ILogicOps Ty)
        (IL_Ty : ILogic Ty)
  : forall T U (P Q : T -> U -> Ty),
      (forall a b, P a b -|- Q a b) ->
      Exists x : T, Exists y : U, P x y -|-
                                    Exists y : U, Exists x : T, Q x y.
  Proof.
    apply lexists_iff_2. apply _.
  Qed.

  Lemma exprD'_add_quants_rev_Some (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty))
        (_ : gs Ty = Some ILO_Ty) :
    forall tus xs tvs tm dtm,
      exprD' tus (rev xs ++ tvs) tm Ty = Some dtm ->
      exists dtm',
        exprD' tus tvs (add_quants xs Ty tm) Ty = Some dtm' /\
        forall vs, dtm' vs -|- lexists (fun vs' => dtm (HList.hlist_app vs' vs)).
  Proof.
    induction xs; simpl; intros.
    + exists dtm. split; [assumption|].
      intros. split.
      * apply lexistsR with Hnil. simpl. reflexivity.
      * apply lexistsL; intros. rewrite (hlist_eta x). simpl. reflexivity.
    + specialize (IHxs (a::tvs) tm).
      assert ((rev xs ++ a :: nil) ++ tvs = rev xs ++ a :: tvs).
      { rewrite app_ass. reflexivity. }
      rewrite exprD'_var_env with (H := H1) in IHxs.
      rewrite H0 in IHxs.
      specialize (IHxs (fun x => match H1 in _ = vs return hlist (typD ts nil) vs -> typD ts nil Ty with
                                   | eq_refl => dtm
                                 end x)).
      destruct IHxs.
      { clear.
        generalize dependent ((rev xs ++ a :: nil) ++ tvs).
        intros; subst. (** eta **) reflexivity. }
      { destruct H2.
        red_exprD.
        rewrite H.
        red_exprD.
        rewrite H.
        red_exprD.
        rewrite H2. eexists; split; eauto.
        simpl.
        intros.
        split.
        { apply lexistsL; intros.
          specialize (H3 (Hcons x0 vs)).
          rewrite H3.
          apply lexistsL; intros.
          eapply (lexistsR (hlist_app x1 (Hcons x0 Hnil))).
          change (Hcons x0 vs) with (hlist_app (Hcons x0 Hnil) vs).
          rewrite hlist_app_assoc; eauto with typeclass_instances.
          match goal with
            | |- _ ?X |-- _ match _ with eq_refl => ?Y end =>
              change Y with X; generalize X
          end.
          generalize (app_ass_trans (rev xs) (a :: nil) tvs).
          generalize H1. simpl. rewrite <- H1.
          uip_all. reflexivity. }
        { apply lexistsL; intros.
          rewrite <- (hlist_app_hlist_split _ _ x0).
          apply (lexistsR (hlist_hd (snd (hlist_split (rev xs) (a :: nil) x0)))).
          rewrite H3.
          apply (lexistsR (fst (hlist_split (rev xs) (a :: nil) x0))).
          rewrite hlist_app_assoc; eauto with typeclass_instances.
          rewrite (hlist_eta (snd (hlist_split (rev xs) (a :: nil) x0))).
          simpl.
          rewrite (hlist_eta (hlist_tl (snd (hlist_split (rev xs) (a :: nil) x0)))).
          simpl. intros.
          match goal with
            | |- _ match _ with eq_refl => ?X end |-- _ ?Y =>
              change Y with X; generalize X
          end.
          generalize (app_ass_trans (rev xs) (a :: nil) tvs).
          generalize H1. simpl. rewrite <- H1.
          uip_all. reflexivity. } }
  Qed.

  Lemma exprD'_add_quants_app_Some (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty))
        (_ : gs Ty = Some ILO_Ty)
  : forall tus a tvs tm b x,
      exprD' tus tvs (add_quants (a ++ b) Ty tm) Ty = Some x ->
      exists y,
        exprD' tus (rev a ++ tvs) (add_quants b Ty tm) Ty = Some y /\
        forall g, x g -|- lexists (fun v => y (HList.hlist_app v g)).
  Proof.
    induction a.
    { simpl.
      intros. eexists; split; eauto.
      intros.
      split.
      { eapply lexistsR. instantiate (1 := Hnil). reflexivity. }
      { apply lexistsL. intros. rewrite (hlist_eta x0). reflexivity. } }
    { simpl List.app.
      intros.
      eapply exprD'_add_quants_cons_Some in H0; eauto.
      destruct H0 as [ ? [ ? ? ] ].
      eapply IHa in H0.
      destruct H0 as [ ? [ ? ? ] ].
      generalize dependent x1.
      assert ((rev a0 ++ a :: nil) ++ tvs = rev a0 ++ a :: tvs).
      { rewrite app_ass. reflexivity. }
      intros.
      exists (fun z =>
                x1 match H0 in _ = t return HList.hlist (typD ts nil) t with
                     | eq_refl => z
                   end).
      generalize H.
      change (a :: tvs) with ((a :: nil) ++ tvs) in *.
      assert (forall g : HList.hlist (typD ts nil) tvs,
                x g -|- Exists v : HList.hlist (typD ts nil) (a :: nil), x0 (HList.hlist_app v g)).
      { intros. specialize (H1 g).
        rewrite H1.
        split.
        { apply lexistsL; intros.
          eapply lexistsR; intros.
          instantiate (1 := Hcons x2 Hnil). reflexivity. }
        { apply lexistsL; intros.
          eapply lexistsR. instantiate (1 :=  hlist_hd x2).
          rewrite (hlist_eta x2).
          rewrite (hlist_eta (hlist_tl x2)). reflexivity. } }
      clear H1.
      simpl rev.
      generalize dependent (a :: nil).
      intros.
      split.
      { generalize H0. rewrite H0. uip_all.
        reflexivity. (** eta **) }
      { intros.
        rewrite H4.
        rewrite exists_hlist_app; eauto with typeclass_instances.
        setoid_rewrite H3.
        eapply lexists_iff_2; eauto with typeclass_instances.
        intros.
        rewrite HList.hlist_app_assoc; eauto with typeclass_instances.
        uip_all. reflexivity. } }
  Qed.

  Lemma exprD'_add_quants_all_Some (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty))
        (_ : gs Ty = Some ILO_Ty)
  : forall tus a tvs tm x,
      exprD' tus tvs (add_quants a Ty tm) Ty = Some x ->
      exists y,
        exprD' tus (rev a ++ tvs) tm Ty = Some y /\
        forall g, x g -|- lexists (fun v => y (HList.hlist_app v g)).
  Proof.
    intros.
    rewrite <- (app_nil_r a) in H0.
    apply exprD'_add_quants_app_Some in H0; eauto.
  Qed.

  Local Existing Instance EqDec_typ.

  Lemma hlist_app_nil A F (xs : list A) (hnil : hlist F nil) (hys : hlist F xs) : hlist_app hnil hys = hys.
  Proof.
    assert (hnil = Hnil) by apply hlist_nil_eta.
    rewrite H. reflexivity.
  Qed.
  Lemma hlist_app_nil A F (xs : list A) (hnil : hlist F nil) (hys : hlist F xs) : hlist_app hnil hys = hys.
  Proof.
    assert (hnil = Hnil) by apply hlist_nil_eta.
    rewrite H. reflexivity.
  Qed.

  Lemma hlist_app_cons A F (xs ys : list A) (x : A) (el : F x) (hxs : hlist F xs) (hys : hlist F ys) :
    Hcons el (hlist_app hxs hys) = hlist_app (Hcons el hxs) hys.
  Proof.
    simpl. reflexivity.
  Qed.

  Lemma lift_entails tus xs ys zs e t de df (HILops : ILogicOps (typD ts nil t)) (HIL: ILogic (typD ts nil t))
	(He : exprD' tus (xs ++ ys ++ zs) (lift (length xs) (length ys) e) t = Some de)
	(Hf : exprD' tus (xs ++ zs) e t = Some df)
	(hxs : hlist (typD ts nil) xs)
	(hys : hlist (typD ts nil) ys)
	(hzs : hlist (typD ts nil) zs) :
    de (hlist_app hxs (hlist_app hys hzs)) |-- df (hlist_app hxs hzs).
  Proof.
    induction ys; intros; simpl in *.
    + rewrite hlist_app_nil.
      rewrite He in Hf. inversion Hf. reflexivity.
    + replace (S (length ys)) with (1 + length ys) in He by omega.
      rewrite <- lift_lift', <- lift_lift in He.
      pose proof (exprD'_lift RSym_sym tus xs (a::nil) (ys++zs) (lift (length xs) (length ys) e) t).
      simpl in *. forward; inv_all; subst.
      specialize (IHys t1).
      specialize (H1 hxs (Hcons (hlist_hd hys) Hnil) (hlist_app (hlist_tl hys) hzs)).
      simpl in H1.
      rewrite hlist_app_cons, <- hlist_cons_eta in H1.
      rewrite H1 at 1. apply IHys. reflexivity.
  Qed.

  Lemma add_quants_app tus tvs xs ys t p q d (IL : ILogicOps (typD ts nil t))
  	(H : exprD' tus tvs (add_quants (xs ++ ys) t (App (lift 0 (length ys) p) (lift (length ys) (length xs) q))) t = Some d) :
    exists tq dp dq,
      typeof_expr (typeof_env tus) (rev ys ++ tvs) q = Some tq /\
      exprD' tus tvs (add_quants xs (tyArr tq t) p) (tyArr tq t) = Some dp /\ exprD' tus tvs (add_quants ys tq q) tq = Some dq /\
      forall vs, d vs |-- (dp vs) (dq vs).
  Proof.
    eapply exprD'_add_quants_app_Some in H; eauto.
    destruct H as [ ? [ ? ? ] ].
    rewrite <- (app_nil_r ys) in H.
    eapply exprD'_add_quants_app_Some in H; eauto.
    destruct H as [ ? [ ? ? ] ].
    simpl in H.
    red_exprD; forward; inv_all; subst.
    rewrite app_nil_r in *.
    pose proof (exprD'_lift RSym_sym tus (rev ys) (rev xs) tvs q t1).
    repeat rewrite rev_length in H. forward; inv_all; subst. simpl.
    pose proof (exprD'_lift RSym_sym tus nil (rev ys) (rev xs ++ tvs) p (tyArr t1 t)).
    repeat rewrite rev_length in H4. simpl in H4. forward; inv_all; subst.
    assert (ILogicOps (typD ts nil (tyArr t1 t))) by admit.
    apply exprD'_add_quants_rev_Some in H7.
    destruct H7 as [? [? ?]].
    assert (ILogicOps (typD ts nil t1)) by admit.
    apply exprD'_add_quants_rev_Some in H5.
    destruct H5 as [? [? ?]].
    exists t1, x0, x1.
    split. admit.
    split. assumption. split. assumption.
    intros.
    assert (ILogic (typD ts nil t)) by admit.
    rewrite H0. apply lexistsL; intros.
    rewrite H1. apply lexistsL; intros.
    assert (t3 (hlist_app x3 (hlist_app x2 vs)) |-- x0 vs).
    assert (ILogic (typD ts nil t1 -> typD ts nil t)) by admit.
    rewrite H7. apply lexistsR with x2.
    specialize (H8 Hnil x3 (hlist_app x2 vs)).
    simpl in H8. rewrite H8. reflexivity.
    assert (t4 (hlist_app x3 (hlist_app x2 vs)) |-- x1 vs).
    assert (ILogic (typD ts nil t1)) by admit.
    rewrite H9. apply lexistsR with x3.
    specialize (H6 x3 x2 vs). rewrite H6. reflexivity.

  Lemma hlist_app_cons A F (xs ys : list A) (x : A) (el : F x) (hxs : hlist F xs) (hys : hlist F ys) :
    Hcons el (hlist_app hxs hys) = hlist_app (Hcons el hxs) hys.
  Proof.
    simpl. reflexivity.
  Qed.
  Abort.
  (* This lemma is true with a bit more help, the problem comes from the requirement to have ILogics for partially applied functions, which is more or less trivial,
 		   but an extra Proper requirement is also needed that allows us to prove (f p |-- g q) if (f |-- g) and (p |-- q). The problem here is also that these propers need
 		   to be preserved when the existential quantifiers are stripped. This is true, but requires lemmas such as exprD'_add_quants_app_Some to keep track of that information
 		   as well. The question is if we want a lemma that is as general as this one, or if we are happy with the special cases. *)

  Lemma lift_entails tus xs ys zs e t de df (HILops : ILogicOps (typD ts nil t)) (HIL: ILogic (typD ts nil t))
	(He : exprD' tus (xs ++ ys ++ zs) (lift (length xs) (length ys) e) t = Some de)
	(Hf : exprD' tus (xs ++ zs) e t = Some df)
	(hxs : hlist (typD ts nil) xs)
	(hys : hlist (typD ts nil) ys)
	(hzs : hlist (typD ts nil) zs) :
    de (hlist_app hxs (hlist_app hys hzs)) |-- df (hlist_app hxs hzs).
  Proof.
    induction ys; intros; simpl in *.
    + rewrite hlist_app_nil.
      rewrite He in Hf. inversion Hf. reflexivity.
    + replace (S (length ys)) with (1 + length ys) in He by omega.
      rewrite <- lift_lift', <- lift_lift in He.
      pose proof (exprD'_lift RSym_sym tus xs (a::nil) (ys++zs) (lift (length xs) (length ys) e) t).
      simpl in *. forward; inv_all; subst.
      specialize (IHys t1).
      specialize (H1 hxs (Hcons (hlist_hd hys) Hnil) (hlist_app (hlist_tl hys) hzs)).
      simpl in H1.
      rewrite hlist_app_cons, <- hlist_cons_eta in H1.
      rewrite H1 at 1. apply IHys. reflexivity.
  Qed.

  Lemma Happ
  : forall tus tvs l (l_res : T) rs t ts,
      typeof_expr (typeof_env tus) tvs (apps l (map fst rs)) = Some t ->
      let ft := fold_right tyArr t ts in
      PQR ft l (l_res (typeof_env tus) tvs) tus tvs ->
      Forall2 (fun t x =>
                    typeof_expr (typeof_env tus) tvs (fst x) = Some t
                 /\ PQR t (fst x) (snd x (typeof_env tus) tvs) tus tvs)
              ts rs ->
      PQR t (apps l (map fst rs)) (pq_app l l_res rs (typeof_env tus) tvs) tus tvs.
   Proof.
     intros; unfold PQR, TD, Teval in *.
     destruct l; simpl in *; try apply I.
     destruct i; simpl in *; try apply I.
     * red_exprD; forward; inv_all; subst; simpl in *.
       red_exprD; forward; inv_all; subst.
       rewrite H0 in H5. inversion H5; subst.
       reflexivity.
     * forward; inv_all; subst. simpl in *.
       forward; inv_all; subst; simpl in *.
       red_exprD; forward; inv_all; subst; simpl in *.
       forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       inversion H9; clear H9; simpl in *.
       revert H0. revert ft. subst. intros.
       inversion H10; clear H10; simpl in *.
       revert H0. revert ft. subst. intros. simpl in *.
       inversion H12; clear H12; revert H0; revert ft; subst; intros.
       simpl in *.
       destruct H8, H9.
       forward; inv_all; subst.
       rewrite H1 in H7; rewrite H2 in H4; inv_all;
       revert H0; revert ft; subst; intros.
       forward; inv_all; revert H0; revert ft; subst; intros.
       forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
	   red_exprD; forward; inv_all; subst.


       eapply exprD'_add_quants_app_Some in H3; eauto.
       destruct H3 as [ ? [ ? ? ] ].
       rewrite <- (app_nil_r l3) in H3.
       eapply exprD'_add_quants_app_Some in H3; eauto.
       destruct H3 as [ ? [ ? ? ] ].
       simpl in H3.
       red_exprD.
       rewrite H in *.
       forward. subst.
       rewrite app_nil_r in *.
       inv_all. subst.
       red_exprD.
       forward. inv_all. subst i. subst t.
       subst p. subst t5. rewrite x1 in H21.
       inv_all. clear H8. clear H6.
       red_exprD.
       simpl in H13. rewrite H in *.
       forward. inv_all. subst t. subst t9.
       inv_all. subst p.
       inversion x2. subst t8. revert H5. subst t4.
       inv_all. subst t0.
       repeat match goal with
                | H : ?X = ?X |- _ => clear H
              end.
       simpl in H16. forward.
       subst t7. revert H6. revert x2. clear H5.
       intro. rewrite (UIP_refl x2).
       clear x2.
       clear H0.
 		pose proof (exprD'_lift RSym_sym tus (rev l3) (rev l2) tvs e4 x0).
 		repeat rewrite rev_length in H0. forward; inv_all; subst. simpl.
 		pose proof (exprD'_lift RSym_sym tus nil (rev l3) (rev l2 ++ tvs) e3 x0).
 		repeat rewrite rev_length in H8. simpl in H8. forward; inv_all; subst.
        apply exprD'_add_quants_rev_Some in H12; eauto; destruct H12 as [? [? ?]].
        apply exprD'_add_quants_rev_Some in H3; eauto; destruct H3 as [? [? ?]].
        forward; inv_all; subst.
        assert (ILogic (typD ts nil x0)) by admit.
        rewrite H4. apply lexistsL; intros.
        rewrite H6. apply lexistsL; intros.
        apply landR.
        + apply landL1.
          rewrite <- H20. rewrite H15.
          apply lexistsR with x3.
          specialize (H13 Hnil x4 (hlist_app x3 vs)). simpl in H13. rewrite H13. reflexivity.
        + apply landL2.
          rewrite <- H18. rewrite H16. apply lexistsR with x4.
          rewrite H5. reflexivity.
    * forward; inv_all; subst. simpl in *.
       forward; inv_all; subst; simpl in *.
       red_exprD; forward; inv_all; subst; simpl in *.
       forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       inversion H9; clear H9; simpl in *.
       revert H0. revert ft. subst. intros.
       inversion H10; clear H10; simpl in *.
       revert H0. revert ft. subst. intros. simpl in *.
       inversion H12; clear H12; revert H0; revert ft; subst; intros.
       simpl in *.
       destruct H8, H9.
       forward; inv_all; subst.
       rewrite H1 in H7; rewrite H2 in H4; inv_all;
       revert H0; revert ft; subst; intros.
       forward; inv_all; revert H0; revert ft; subst; intros.
       forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
       red_exprD; forward; inv_all; subst.
	   red_exprD; forward; inv_all; subst.


       eapply exprD'_add_quants_app_Some in H3; eauto.
       destruct H3 as [ ? [ ? ? ] ].
       rewrite <- (app_nil_r l3) in H3.
       eapply exprD'_add_quants_app_Some in H3; eauto.
       destruct H3 as [ ? [ ? ? ] ].
       simpl in H3.
       red_exprD.
       rewrite H in *.
       forward. subst.
       rewrite app_nil_r in *.
       inv_all. subst.
       red_exprD.
       forward. inv_all. subst i. subst t.
       subst p. subst t5. rewrite x1 in H21.
       inv_all. clear H8. clear H6.
       red_exprD.
       simpl in H13. rewrite H in *.
       forward. inv_all. subst t. subst t9.
       inv_all. subst p.
       inversion x2. subst t8. revert H5. subst t4.
       inv_all. subst t0.
       repeat match goal with
                | H : ?X = ?X |- _ => clear H
              end.
       simpl in H16. forward.
       subst t7. revert H6. revert x2. clear H5.
       intro. rewrite (UIP_refl x2).
       clear x2.
       clear H0.
 		pose proof (exprD'_lift RSym_sym tus (rev l3) (rev l2) tvs e4 x0).
 		repeat rewrite rev_length in H0. forward; inv_all; subst. simpl.
 		pose proof (exprD'_lift RSym_sym tus nil (rev l3) (rev l2 ++ tvs) e3 x0).
 		repeat rewrite rev_length in H8. simpl in H8. forward; inv_all; subst.
        apply exprD'_add_quants_rev_Some in H12; eauto; destruct H12 as [? [? ?]].
        apply exprD'_add_quants_rev_Some in H3; eauto; destruct H3 as [? [? ?]].
        forward; inv_all; subst.
        assert (ILogic (typD ts nil x0)) by admit.
        rewrite H4. apply lexistsL; intros.
        rewrite H6. apply lexistsL; intros.
        apply lorL.
        + apply lorR1.
          rewrite <- H20. rewrite H15.
          apply lexistsR with x3.
          specialize (H13 Hnil x4 (hlist_app x3 vs)). simpl in H13. rewrite H13. reflexivity.
        + apply lorR2.
          rewrite <- H18. rewrite H16. apply lexistsR with x4.
          rewrite H5. reflexivity.
   Qed.

End PullQuant.

Section TestPullQuant.

  Context {A : Type} {ILO : ILogicOps A}.

  Context (logics_sound : forall g, match logics g with
                                  | Some T => @ILogic _ T
                                  | None => unit
                                end).

  Variable eq_nat : nat -> nat -> A.
  Definition ts : types := (default_type A)::(default_type nat)::nil.
  Variable es : embed_ops ts.
  Variable funcs : fun_map ts.
  Definition logics : logic_ops ts :=
    fun t => match t with
               | tyType 0 => Some ILO
               | tyProp => Some _
               | _ => None
             end.

  Definition test_fold := fun x => TD (es := es) (funcs) logics (tyType 0) (app_fold_args pqArgs x nil nil).

  Eval cbv - [land ltrue lexists] in test_fold inj_true nil nil.
  Eval cbv - [land ltrue lexists] in test_fold (inj_and inj_true inj_true) nil nil.
  Eval cbv - [land ltrue lexists] in test_fold
                   (inj_and (inj_exists (tyType 1) (inj_and inj_true (inj_exists (tyType 1) inj_true))) inj_true) nil nil.
  Eval cbv - [land ltrue lexists] in test_fold
                   (inj_and (inj_exists (tyType 0) (Var 0)) (inj_exists (tyType 0) (Var 0))) nil nil.
 Eval cbv - [land ltrue lexists] in test_fold
                   (inj_exists (tyType 1)
                                        (inj_exists (tyType 0) (Var 0))) nil nil.
  Eval compute in test_fold
                   (inj_and (inj_exists (tyType 1) (inj_and inj_true
                                                            (inj_exists (tyType 2) (Var 0))))
                            inj_true) nil nil.
Print inj_exists.
Definition test_fold := @setoid_fold _ _ _ (atomic (SRW_Algo_pull_quant logics)) (SetoidFold.app (SRW_Algo_pull_quant logics))
                   (SetoidFold.abs (SRW_Algo_pull_quant logics)) nil nil.

Eval compute in test_fold (Abs (tyType 1) inj_true) (Rpointwise (tyType 1) (Rinj ent)).
Eval compute in test_fold (Inj (ilf_exists (tyType 1) (tyType 0))) (Rfunctorial (Rpointwise (tyType 1) (Rinj ent)) (Rinj ent)).



Eval compute in
  Eval compute in
      @setoid_fold _ _ _ (atomic SRW_Algo_pull_quant) (SetoidFold.app SRW_Algo_pull_quant)
                   (SetoidFold.abs SRW_Algo_pull_quant) nil nil
                   (inj_and (inj_exists (tyType 1) (inj_eq_nat (Var 0) (Var 0))) inj_true)
                   (Rinj ent).
  simpl.
Check @setoid_fold.
  Eval compute in
      @setoid_fold _ _ _ _ _ properAt atomic app nil (Inj And) (tyProp :: nil)
                      (PRfunctorial (PRguess _ tyProp) (PRfunctorial (PRguess _ tyProp) (PRinj Impl))).

End TestPullQuant.

    Variable TT : Type.
    Let T := tenv typ -> tenv typ -> TT.

    Variable do_var : var -> T.
    Variable do_uvar : uvar -> T.
    Variable do_inj : sym -> T.
    Variable do_abs : typ -> expr sym -> T -> T.
    Variable do_app : expr sym -> T ->
                      list (expr sym * T) -> T.

    Definition semArgs : AppFullFoldArgs TT :=
      @Build_AppFullFoldArgs TT do_var do_uvar do_inj do_abs do_app.

    Variable R : forall t, typD ts nil t -> TT -> env (typD ts) -> env (typD ts) -> Prop.
    Hypothesis Hvar : forall us tvs t v val,
                        exprD' us tvs (Var v) t = Some val ->
                        forall vs,
                          R t (val vs) (do_var v (typeof_env us) tvs) us (join_env vs).
    Hypothesis Huvar : forall us tvs t v val,
                        exprD' us tvs (UVar v) t = Some val ->
                        forall vs,
                          R t (val vs) (do_uvar v (typeof_env us) tvs) us (join_env vs).
    Hypothesis Hinj : forall us tvs t v val,
                        exprD' us tvs (Inj v) t = Some val ->
                        forall vs,
                          R t (val vs) (do_inj v (typeof_env us) tvs) us (join_env vs).
    (** INTERESTING ONES **)
    Hypothesis Habs : forall us tvs t t' e e_res val,
                        exprD' us (t :: tvs) e t' = Some val ->
                        forall (vs : hlist (typD ts nil) tvs),
                          (forall x,
                             R t' (val (Hcons x vs)) (e_res (typeof_env us) (t :: tvs))
                               us ((@existT _ (typD ts nil) t x) :: join_env vs)) ->
                          R (tyArr t t') (fun x => val (Hcons x vs))
                            (do_abs t e e_res (typeof_env us) tvs) us (join_env vs).


Section Relation.
	Variable ts : types.
	Variable func : Type.
	Variable R : RSym (typD ts) func.
	Variable us vs : tenv typ.

	Definition is_relation_bool (t : typ) :=
		match t with
			| tyArr t (tyArr t' tyProp) => t ?[eq] t'
			| _                          => false
		end.

	Definition is_relation (e : expr func) (t : typ) :=
		WellTyped_expr us vs e (tyArr t (tyArr t tyProp)).

End Relation.

Section IsPreOrder.
	Variable ts : types.
	Variable func : Type.
	Variable us vs : env (typD ts).
	Variable R : RSym (typD ts) func.

	Variable is_preorder : expr func -> bool.

	Definition preorder_prop (e : expr func) (t : typ) :=
		forall v, exprD us vs e (tyArr t (tyArr t tyProp)) = Some v ->
		PreOrder v.

	Definition is_preorder_sound :=
	    forall e, is_preorder e = true -> forall t, preorder_prop e t.

End IsPreOrder.

Section PullExistsLeft.
  Context (ts : types) (funcs : fun_map ts) (gs : logic_ops ts).

  Local Instance RSym_sym : SymI.RSym (typD ts) ilfunc := RSym_ilfunc ts funcs gs.

  Variable us vs : env (typD ts).
  Definition T := (list typ * list typ * expr ilfunc)%type.

  Definition T_union (p q : T) : T :=
    match p, q with
        (a1, b1, c1), (a2, b2, c2) =>
        (a1 ++ a2, b1 ++ b2, App (lift 0 ((length a2) + (length b2)) c1) c2)
    end.

  Fixpoint T_to_expr_aux (vs qs : list typ) e t :=
    match vs, t with
      | nil, _ => Some (fold_right (fun v e => App (Inj (ilf_exists v t)) (Abs v e))
                                   e qs)
      | v::vs, tyArr a t =>
        match T_to_expr_aux vs qs e t, v ?[eq] a with
          | Some x, true => Some (Abs a x)
          | _, _ => None
        end
      | _, _ => None
    end.

  Definition T_to_expr (e : T) (t : typ) :=
    match e with
        (vs, qs, e) => T_to_expr_aux vs qs e t
    end.

  Inductive Rbase :=
    | Ent t : (exists v, gs' ts gs t = Some v) -> Rbase
    | Eq : Rbase.

  Fixpoint Rbase_eq (r1 r2 : Rbase) : bool :=
    match r1, r2 with
      | Ent t1 _, Ent t2 _ => t1 ?[eq] t2
      | Eq, Eq             => true
      | _, _               => false
    end.

  Instance RelDec_Rbase_eq : RelDec (@eq Rbase) := { rel_dec := Rbase_eq }.

  Definition typeForRbase r :=
    match r with
      | Ent t _ => t
      | Eq => tyProp
    end.

  Definition app (vs us : tenv typ) (pq p : T) (rpq rp : R Rbase) : option T :=
    match rpq with
      | Rinj (Ent t _) => Some (T_union pq p)
      | Rpointwise a (Rinj (Ent t _)) =>
        match pq, p with
          | ((tyArr a' t')::nil, a''::nil, Var 1), (a'''::ls, es, p) =>
            if a' ?[eq] a'' && a'' ?[eq] a''' then
              Some (ls, a''::es, p)
            else
              None
          | _, _ => None
        end
      | _ => None
    end.

  Definition abs (vs us : tenv typ) (t : typ) (p : T) (r : R Rbase) : option T :=
    Some (t :: fst (fst p), snd (fst p), snd p).

  Fixpoint unify (r : R Rbase) (p : PR Rbase) : bool :=
    match p with
      | PRguess => true
      | PRinj i => match r with
                     | Rinj i' => i ?[ eq ] i'
                     | _ => false
                   end
      | PRfunctorial a b =>
        match r with
          | Rfunctorial a' b' => andb (unify a' a) (unify b' b)
          | _ => false
        end
      | PRpointwise t a =>
        match r with
          | Rpointwise t' a' => andb (t ?[eq] t') (unify a' a)
          | _ => false
        end
    end.

  Definition proper_lookup (a : expr ilfunc)  (r : Rbase) : option (R Rbase) :=
    match a, r with
      | Inj (ilf_and t), Ent t' pr =>
        if t ?[eq] t' then
          Some (Rfunctorial (Rinj (Ent pr)) ((Rfunctorial (Rinj (Ent pr)) (Rinj (Ent pr)))))
        else
          None
      | Inj (ilf_exists a t), Ent t' pr =>
        if t ?[eq] t' then
          Some (Rfunctorial (Rpointwise a (Rinj (Ent pr))) (Rinj (Ent pr)))
        else
          None
      | Inj (ilf_true t), Ent t' pr => if t ?[eq] t' then Some (Rinj (Ent pr)) else None
(*      | _, Ent (tyType 0) pr => match @typeof_expr (@ILogicFunc.ts A) ilfunc (RSym_sym funcs logics) nil nil a with
                               | Some (tyType 0) => Some (Rinj (Ent pr))
                               | _ => None
                                end*)
      | _, _ => None
    end.



  Fixpoint get_proper_aux (e : expr ilfunc) (r : PR Rbase) : option (R Rbase) :=
    match r with
      | PRinj r => proper_lookup e r
      | PRfunctorial l r => get_proper_aux e r
      | PRpointwise t r => get_proper_aux e r
      | _ => None
    end.

  Definition get_unified_proper (e : expr ilfunc) (r : PR Rbase) : option (R Rbase) :=
    match get_proper_aux e r with
      | Some x => if unify x r then Some x else None
      | None => None
    end.

  Lemma unification_instantiates r r' (H : unify r' r = true) :
    instantiates r' r.
  Proof.

    generalize dependent r; induction r'; simpl; intros.
    + destruct r0; try congruence; [|apply Ins_guess]. admit.
    + destruct r; try congruence; [apply Ins_guess|].
      rewrite andb_true_iff in H. apply Ins_func; [apply IHr'1| apply IHr'2]; intuition.
    + destruct r; try congruence; [apply Ins_guess|].
      rewrite andb_true_iff in H.
      assert (t = t0) by admit; subst.
      apply Ins_point. apply IHr'; intuition.
  Qed.

  Definition atom (us vs : tenv typ) (e : expr ilfunc) (r : R Rbase) : option T :=
    match e with
      | Inj (ilf_exists a t) => Some ((tyArr a t)::nil, a::nil, Var 1)
      | _ => Some (nil, nil, e)
    end.

  Lemma atom_cases (tus tvs : tenv typ) (e : expr ilfunc) (r : R Rbase) (res : T)
    (H : atom tus tvs e r = Some res) :
    (exists a t, (e = Inj (ilf_exists a t) /\ (res =  ((tyArr a t)::nil, a::nil, Var 1)))) \/
    (res = (nil, nil, e)).
  Proof.
    destruct e; simpl in *; try (right; congruence).
    destruct i; simpl in *; try (right; congruence).
    left. exists t; exists t0. intuition congruence.
  Qed.

  Definition TD us vs (e : T) (t : typ) :=
    match (T_to_expr e t) with
      | Some x => exprD' us vs x t
      | None   => None
    end.


  Require Import FunctionalExtensionality.

  Lemma TD_abs uvs vvs avs a b c t x
    (H : TD uvs vvs (a::avs, b, c) t = Some x) :
      exists x, t = tyArr a x.
  Proof.
    unfold TD in H.
    destruct t; simpl in *; try congruence.
    forward; inv_all; subst. exists t2. reflexivity.
  Qed.

  Lemma TD_abs_list uvs vvs avs b c t x
    (H : TD uvs vvs (avs, b, c) t = Some x) :
      exists y, t = fold_right tyArr y avs.
  Proof.
    generalize dependent t; generalize dependent vvs.
    induction avs; intros; simpl in *.
    + exists t; reflexivity.
    + unfold TD, T_to_expr in H; simpl.
      red_exprD; forward; inv_all; subst.
      unfold TD, T_to_expr in IHavs.
      red_exprD; forward; inv_all; subst.
      specialize (IHavs _ _ t). rewrite H0 in IHavs.
      destruct (IHavs H1) as [y Hy].
      exists y. rewrite Hy. reflexivity.
  Qed.

  Lemma TD_abs_sem uvs vvs avs a b c t x :
    TD uvs vvs (a::avs, b, c) (tyArr a t) = Some x <->
    TD uvs (a::vvs) (avs, b, c) t = Some (fun g => x (HList.hlist_tl g) (HList.hlist_hd g)).
  Proof.
    split; intro H.
    + unfold TD, T_to_expr in H; simpl in H.
      red_exprD; forward; inv_all; subst.
      red_exprD; forward; inv_all; subst.
      rewrite x0.
      unfold TD, T_to_expr. rewrite H. rewrite H2.
      f_equal. apply functional_extensionality; intros x.
      rewrite <- HList.hlist_cons_eta. reflexivity.
    + unfold TD, T_to_expr in *; simpl in *.
      forward. red_exprD; forward. inv_all; subst.
      rewrite typ_cast_typ_refl.
      f_equal.
  Qed.

  Fixpoint typD_fold_right tvs uvs t avs :
    typD tvs uvs (fold_right tyArr t avs) -> HList.hlist (typD tvs uvs) avs ->
    typD tvs uvs t :=
    match avs with
      | nil => fun x _ => x
      | a::avs => fun f lst => typD_fold_right (f (HList.hlist_hd lst)) (HList.hlist_tl lst)
    end.
(*
  Lemma TD_abs_list_sem uvs vvs avs b c t x :
    (TD uvs vvs (avs, b, c) (fold_right tyArr t avs) = Some x) <->
    TD uvs ((rev avs) ++ vvs) (nil, b, c) t =
    Some (fun g => match HList.hlist_split (rev avs) vvs g with
                     | (a, b) => typD_fold_right (x b) a
                   end).
  Proof.
    split; intro H.
    + generalize dependent t; generalize dependent vvs.
      induction avs; simpl in *; intros.
      * rewrite H. f_equal.
      * apply TD_abs_sem in H.
        apply IHavs in H.
        admit.
    + generalize dependent t; generalize dependent vvs.
      induction avs; simpl in *; intros.
      * rewrite H. reflexivity.
      * admit.
  Qed.
*)

  Lemma TD_quant_sem_aux uvs vvs e t a (v : typD ts nil a) x :
    TD uvs (a::vvs) e t = Some x <->
    TD uvs vvs e t = Some (fun vs => x (HList.Hcons v vs)).
  Proof.
    split; intro H.
    + unfold TD in *; simpl in *; forward.
      pose proof (exprD'_lower RSym_sym us nil (a::nil) vvs e0).
      simpl in *.

      red_exprD.
      forward.
      pose proof (exprD'_lift RSym_sym us nil (a::nil) vvs e0 t).

      simpl in *.
      SearchAbout lift.
    simpl.




  Lemma TD_quant_sem_aux uvs vvs q qs c t x IL (a : typD ts nil q)
        (HIL : gs' ts gs t = Some IL)
        (H : TD uvs vvs (nil, q::qs, c) t = Some x) :
        exists f, x = (fun vs => lexists (f vs)) /\
                    TD uvs vvs (nil, qs, c) t = Some (fun vs => f vs a).
  Proof.
    unfold TD, T_to_expr in *; simpl in H.
    red_exprD; forward; inv_all; revert H4; generalize dependent t2; subst; intros.
    destruct x0. subst.
    red_exprD; forward; inv_all; subst.
    simpl in *. forward; inv_all; subst.
    exists (fun x a => t (HList.Hcons a x)).
    split. simpl.
    apply functional_extensionality; intros x1; simpl.
    uip_all. reflexivity.
    rewrite H2.
    destruct x0.
rewrite <- H7 in H5.
rewrite <- H7 in x0. rewrite H7 in H5.
    red_exprD; forward; inv_all; uip_all.
    rewrite HIL in *. rewrite <- H6 in *. rewrite H7 in *. rewrite x0 in *.
    red_exprD; forward; inv_all. simpl in *. forward. inv_all.
    red_exprD; forward; inv_all; revert H4; generalize dependent t2; subst; intros.
    rewrite typ_cast_typ_refl in H2.
    simpl.
    red_exprD; forward; inv_all.
    f_equal. generalize dependent t2; subst; intros.
    apply functional_extensionality; intros; simpl.
    red_exprD; forward; inv_all; subst; simpl in *.
    f_equal. apply functional_extensionality. intros; simpl.
    admit.
  Qed.

  Lemma TD_quant_sem uvs vvs q qs c il t f IL
        (HIL : gs' ts gs t = Some IL)
        (H : TD uvs (q::vvs) (nil, qs, c) il t = Some f) :
    TD uvs vvs (nil, qs, c) il t = Some (fun g => lexists (fun x => f (HList.Hcons x g))).
  Proof.
    unfold TD, T_to_expr in *.
    simpl in *. remember ((fold_right
           (fun (t : typ) (e : expr ilfunc) =>
            App (Inj (ilf_exists t il)) (Abs t e)) c qs)) as y.
    admit.
  Qed.



  Fixpoint RD (r : R Rbase) : (typD ts nil (typeForR typeForRbase r)) ->
                              (typD ts nil (typeForR typeForRbase r)) -> Prop :=
    match r with
      | Rfunctorial l r => fun f g => forall x y, @RD l x y -> @RD r (f x) (g y)
      | Rinj (Ent t _) =>
        fun a b => t ?[eq] typeForR typeForRbase r = true /\
                   exists ILO, gs' ts gs t = Some ILO /\ a |-- b
      | Rinj Eq => fun a b => a = b
      | Rpointwise t r => fun f g => forall x, @RD r (f x) (g x)
    end.

  Lemma RD_reflexive r a : @RD r a a.
  Proof.
    induction r.
    + simpl. destruct r; [|reflexivity].
      split. simpl. apply rel_dec_eq_true. apply _. reflexivity.
      destruct e. simpl in *.
      exists x. intuition. admit.
    + simpl; intros.
      admit. (* This is not true *)
    + simpl; intros.
      apply IHr.
  Qed.

  Definition TR us vs (r : R Rbase) (t : T) v : Prop :=
    match TD us vs t (typeForR typeForRbase r) with
      | Some x => forall vs, @RD r v (x vs)
      | None => False
    end.

  Theorem Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f result,
      app (typeof_env us) (typeof_env vs) r1 r2 t1 t2 = Some result ->
      exprD us vs f (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v1 ->
      @TR us (typeof_env vs) (Rfunctorial t1 t2) r1 v1 ->
      @TR us (typeof_env vs) t1 r2 v2 ->
      @TR us (typeof_env vs) t2 result (v1 v2).
  Proof.
    intros. simpl in *.
    destruct r1 as [[rv1 re1] r1], r2 as [[rv2 re2] r2]; simpl in *.
    unfold TR in *.
    forward. simpl in *.
Check TD.
    (f : typD ts nil r ->
     (H: TD us0 (typeof_env vs0) (r::rv1, re1, r1)
         (tyArr ) =
       Some t0)
       TD us0 (typeof_env vs0) (rv1, re1, r1)
         (tyArr (typeForR typeForRbase t1) (typeForR typeForRbase t2)) =
       Some f

    unfold TD in H1.



    destruct t1; simpl in *; try congruence.
    destruct r; simpl in *; try congruence.
    inv_all; subst. unfold T_union; simpl.
    unfold TR, TD, T_to_expr. simpl.
    forward.
    induction rv1. simpl. admit.
    simpl in *.
Eval compute in (typD ts nil (typeForR typeForRbase (Rpointwise a t2))).
    Lemma TR_abs t uvs vvs r a rvs es p (v : typD ts nil (typeForR typeForRbase t))
      (H : forall (x : typD ts nil a), exists f rd, f x = v /\ rd = Rpointwise a r /\ @TR uvs vvs (Rpointwise a r) (rvs, es, p) f) :
      @TR uvs vvs r (a :: rvs, es, p) v.
    Proof.
      admit.
    Qed.

    apply TR_abs.
    intros.

    apply TR_abs. apply IHrv1.

    inv_all; subst. unfold T_union; simpl.
    unfold TR in *.
    remember (TD us0 (typeof_env vs0) r1
           (typeForR typeForRbase (Rfunctorial t1 t2))) as o.
    destruct o; simpl in *; [|intuition].
    remember (TD us0 (typeof_env vs0) r2 (typeForR typeForRbase t1)) as o.
    destruct o; simpl in *; [|intuition].
    destruct t1; simpl in *; try congruence.
    destruct r; simpl in *; try congruence.
    induction rv1. simpl. admit.
    unfold TD, T_to_expr; simpl.
    SearchAbout exprD' Abs.
    red_exprD.
    destruct t2; simpl in *; try congruence.
    destruct r; simpl in *; try congruence.
    destruct t2; simpl in *; try congruence.
    unfold TD in IHrv1. simpl in *.
    apply IHrv1.
    remember (TD us0 (typeof_env vs0)
       (a :: rv1 ++ rv2, re1 ++ re2,
       App (lift 0 (length rv2 + length re2) r1) r2)
       (typeForR typeForRbase t2)) as o.
    destruct o; intros; simpl in *.
    unfold TD, T_to_expr in Heqo.
    simpl in Heqo.
    red_exprD. forward.
    unfold TR.
    unfold TD.
    unfold T_to_expr.
    simpl.
    unfold TR, TD, T_to_expr in H1; simpl in *.
    unfold exprD in H1.
    destruct vs0.
    remember (exprD' us0 tvs
            (Abs a
               (fold_right Abs
                  (fold_right
                     (fun (t0 : typ) (e : expr ilfunc) =>
                      App
                        (Inj
                           (ilf_exists t0
                              (tyArr t (typeForR typeForRbase t2))))
                        (Abs t0 e)) r1 re1) rv1))
            (tyArr t (typeForR typeForRbase t2))).
SearchAbout expr
    red_exprD.
    simpl in H1.
    red_exprD.
    simpl.
    simpl.

    simpl.
    simpl.

destruct H1RD as [_ H1RD].
    unfold app in H.
    unfold TD, T_to_expr in *; simpl in *.
    destruct t1; simpl in *; try congruence.
    destruct r; simpl in *; try congruence.
    unfold TD in H1.
    unfold app in H; simpl in *.
    simpl in *.


    Lemma TD_app us vs e1 e2 t1 t2 tr1 tr2 result
          (H1 : TD us vs e1 (tyArr t1 t2) = Some tr1)
          (H2 : TD us vs e2 t1 = Some tr2)
          (H3 : app (typeof_env us) (typeof_env vs) r1 r2 t1 t2 = Some result) :
      TD us vs result t2 = Some (tr1 tr2).


    unfold TD in *.

    specialize (H1RD _ _ H2RD). simpl in *.
    simpl in *.
    unfold TR.
    exists (v1 v2).
    split; [|admit].
    clear H1
    red_exprD.
    unfold TR.
    unfold TD in *.
    unfold T_to_expr in *.
    simpl in *.
  Theorem Hatomic
    : forall tus tvs e r r' result,
        get_unified_proper  e r = Some r' ->
        (atom tus tvs e r' = Some result) ->
        @setoid_fold_spec _ _ (RSym_sym) _ _ _ TR tus tvs e r result r'.
  Proof.
    intros; repeat split; intros.
    + apply unification_instantiates.
      unfold get_unified_proper in H.
      destruct (get_proper_aux e r); try congruence.
      remember (unify r0 r) as b; destruct b; congruence.
    + unfold get_unified_proper in H.
      remember (get_proper_aux e r) as o; destruct o; try congruence.
      remember (unify r0 r) as b; destruct b; try congruence.
      inv_all; subst.
      Print pr_type.
  Lemma proper_lookup_type tus tvs e r r' r'' t
        (H : unify r' r = true)
        (H1 : proper_lookup e r'' = Some r')
        (H2 : typeof_expr tus tvs e = Some t) :
      typeForR typeForRbase r' = t.
  Proof.
    destruct e; simpl in *; try congruence;
    destruct i; simpl in *; try congruence;
    destruct r''; simpl in *; try congruence;
    destruct e as [v ILV];
    remember (t0 ?[ eq ] t1) as b;
    destruct b; try congruence;
    assert (t0 = t1) by admit; subst;
    try rewrite ILV in H2; inv_all; subst; simpl; try reflexivity.
    remember (t1 ?[eq] t2) as b.
    destruct b; try congruence.
    inv_all; subst; simpl in *.
    destruct r; simpl in *; try congruence.
    assert (t1 = t2) by admit; subst.
    rewrite ILV in H2; inv_all.
    assumption.
    destruct r1; simpl in *; try congruence.
    assert (t1 = t2) by admit; subst.
    rewrite ILV in H2; inv_all.
    destruct r2; simpl in *; try congruence.
    rewrite andb_true_iff in H; destruct H as [H H1].
    rewrite andb_true_iff in H; destruct H as [H H0].
    assert (t1 = t2) by admit; subst.
    rewrite ILV in H2; inv_all. assumption.
    admit.
  Qed.

  Lemma unification_type tus tvs e r r' r'' t (H : unify r' r = true)
    (H1 : get_proper_aux e r'' = Some r')
    (H2 : pr_type typeForRbase r t)
    (H3 : typeof_expr tus tvs e = Some t) : typeForR typeForRbase r' = t.
  Proof.
    generalize dependent r; generalize dependent r'; induction r''; simpl; intros;
    try congruence.
    eapply proper_lookup_type; eauto.
    eapply IHr''2; eauto.
    eapply IHr''; eauto.
  Qed.


  eapply unification_type; eauto.
    + remember (exprD' us0 tvs e (typeForR typeForRbase r')).
      destruct o; [|apply I].
      intros.
      apply atom_cases in H0; destruct H0 as [[a [t1 [He Hres]]] | H0].
      subst; unfold TR.
      unfold TD, T_to_expr; simpl.
      red_exprD; forward; inv_all; subst; simpl in *.
      assert (exists IL, gs' ts gs t1 = Some IL) by admit.
      destruct H4 as [IL H4].
      rewrite H4 in H0. rewrite H4 in H2. inv_all; simpl in *.
      subst; red_exprD.
      remember (typ_cast_typ ts nil (tyArr (tyArr a t1) t1)
           (typeForR typeForRbase r')) as o.
      destruct o; try congruence.
      symmetry in Heqo.
      apply typ_cast_typ_eq in Heqo; subst.
      exists t2.
      split.
      inv_all; subst.
      unfold exprD.
      rewrite split_env_join_env.
      red_exprD.

      uip_all.
      rewrite <- Heqo.
      simpl.
      uip_all.
      red_exprD.
      simpl.
      red_exprD.
      eexists.

Check typ_cast_typ_eq.
rewrite typ_cast_typ_eq in Heqo.
      SearchAbout typ_cast_typ.
      red_exprD.
      assert (t = tyArr (tyArr a t1) t1) by admit.
      simpl.
      subst.
      unfold TR.
      exists (t0 vs0).
      split. unfold TD. simpl.
      unfold exprD; simpl.
      rewrite split_env_join_env.
      unfold T_to_expr; simpl.
      remember (exprD' us0 tvs e (typeForR typeForRbase r')).
      destruct o; inv_all; subst; [reflexivity|congruence].
      apply RD_reflexive.
  Qed.

  Definition SRW_Algo_pull_quant :=
    @SRW_Algo_properAt ilfunc T Rbase get_unified_proper atom app abs.

End PullExistsLeft.

Section demo.
  Context {A : Type} {ILO : ILogicOps A}.

  Context (logics_sound : forall g, match logics g with
                                  | Some T => @ILogic _ T
                                  | None => unit
                                end).

  Existing Instance ILFun_ILogic.

  Lemma gs'_sound : forall g, match gs' ts logics g with
                                | Some T => @ILogic _ T
                                | None => unit
                              end.
  Proof.
    intros g; induction g; simpl; try apply tt.
    simpl. remember (gs' ts logics g2) as o; destruct o; [apply _ | apply tt].
    destruct n; [|apply tt]; simpl in *.
    specialize (logics_sound (tyType 0)); simpl in *.
    apply logics_sound.
  Qed.

  Program Definition ent := @Ent _ logics (tyType 0) _.
  Next Obligation.
    exists ILO. reflexivity.
  Defined.

Print setoid_fold_spec.
(*
Check @exprD'.
Print setoid_fold_spec.
  Definition TR us vs (r : R (Rbase logics)) (t : T) v : Prop :=
    exists v', TD us vs t (typeForR typeForRbase r) = Some v' /\ @RD us vs r v v'.


  Theorem Hatomic
    : forall tus tvs e r r' result,
        (get_unified_proper get_proper)  e r = Some r' ->
        (atom tus tvs e r' = Some result) ->
        @setoid_fold_spec _ _ (RSym_sym funcs logics) _ _ _ TR tus tvs e r result r'.
  Proof.
    intros.
    unfold atom in H0. inv_all; subst.
    red; intros.
    split. admit.
    split. admit.
    intros.
    remember (exprD' us tvs e (typeForR typeForRbase r')) as o.
    destruct o; [|apply I].
    intros.
    unfold TR. exists (t0 vs).
    split.
    unfold TD.
    unfold exprD.
    simpl.
    simpl.





  Check SRW_AlgoOk_properAt.
*)
  Eval compute in
      @setoid_fold _ _ _ (atomic (SRW_Algo_pull_quant logics)) (SetoidFold.app (SRW_Algo_pull_quant logics))
                   (SetoidFold.abs (SRW_Algo_pull_quant logics)) nil nil
                   inj_true
                   (Rinj ent).

  Eval compute in
      @setoid_fold _ _ _ (atomic (SRW_Algo_pull_quant logics)) (SetoidFold.app (SRW_Algo_pull_quant logics))
                   (SetoidFold.abs (SRW_Algo_pull_quant logics)) nil nil
                   (inj_and inj_true inj_true)
                   (Rinj ent).

  Eval compute in
      @setoid_fold _ _ _ (atomic (SRW_Algo_pull_quant logics)) (SetoidFold.app (SRW_Algo_pull_quant logics))
                   (SetoidFold.abs (SRW_Algo_pull_quant logics)) nil nil
                   (inj_and (inj_exists (tyType 1) (inj_and inj_true (inj_exists (tyType 2) inj_true))) inj_true)
                   (Rinj ent).

Definition test_fold := @setoid_fold _ _ _ (atomic (SRW_Algo_pull_quant logics)) (SetoidFold.app (SRW_Algo_pull_quant logics))
                   (SetoidFold.abs (SRW_Algo_pull_quant logics)) nil nil.

Eval compute in test_fold (Abs (tyType 1) inj_true) (Rpointwise (tyType 1) (Rinj ent)).
Eval compute in test_fold (Inj (ilf_exists (tyType 1) (tyType 0))) (Rfunctorial (Rpointwise (tyType 1) (Rinj ent)) (Rinj ent)).



Eval compute in
  Eval compute in
      @setoid_fold _ _ _ (atomic SRW_Algo_pull_quant) (SetoidFold.app SRW_Algo_pull_quant)
                   (SetoidFold.abs SRW_Algo_pull_quant) nil nil
                   (inj_and (inj_exists (tyType 1) (inj_eq_nat (Var 0) (Var 0))) inj_true)
                   (Rinj ent).
  simpl.
Check @setoid_fold.
  Eval compute in
      @setoid_fold _ _ _ _ _ properAt atomic app nil (Inj And) (tyProp :: nil)
                      (PRfunctorial (PRguess _ tyProp) (PRfunctorial (PRguess _ tyProp) (PRinj Impl))).


Check @SRW_Algo_properAt.

  Check inj_true.

Check @inj_true.

  Axiom eq_nat : nat -> nat -> T.

  Definition eq_nat_emb := F ts (tyArr (tyType 1) (tyArr (tyType 1) (tyType 0))) (eq_nat).

  Definition inj_and (p q : expr ilfunc) : expr ilfunc := App (App (Inj (ilf_and (tyType 0))) p) q.

  Lemma

  Definition inj_true : expr ilfunc := Inj (ilf_true (tyType 0)).
  Definition inj_false : expr ilfunc := Inj (ilf_false (tyType 0)).
  Definition inj_exists (a : typ) (f : expr ilfunc) : expr ilfunc :=
  	App (Inj (ilf_exists a (tyType 0))) (Abs a f).
  Definition inj_forall (a : typ) (f : expr ilfunc) : expr ilfunc :=
  	App (Inj (ilf_forall a (tyType 0))) (Abs a f).
  Definition inj_eq_nat (a b : expr ilfunc) : expr ilfunc :=
    App (App (Inj (fref (1%positive))) a) b.



  Definition tm : expr ilfunc := inj_and inj_true inj_true.
  Definition tm2 : expr ilfunc := inj_forall (tyType 1) (inj_eq_nat (Var 0) (Var 0)).
  Require Import MirrorCore.Ext.ExprD.

  (** TODO: Here we run into a problem because the [expr] type is
   ** fixed to the [typ] defined in [MirrorCore.Ext.Types].
   ** - To solve this problem, we need to abstract [expr] with respect to
   **   types.
   **)

  Eval cbv beta iota zeta delta - [ltrue land] in @exprD ts _ (RSym_ilfunc ts funcs logics) nil nil tm (tyType 0).
  Eval cbv beta iota zeta delta - [ltrue land lforall] in @exprD ts _ (RSym_ilfunc ts funcs logics) nil nil tm2 (tyType 0).

  Check setoid_fold.

End demo.



  Lemma T_to_expr_app pq p tpq tp vp vpq r
  	(Hpq : TD pq (tyArr tp tpq) = Some vpq)
  	(Hp : TD p tp = Some vp) :
  	TD (app pq p r r) tpq = Some (vpq vp).
    clear gs_sound.
    Set Printing All.
clear gs.





  Definition T_to_expr (t : T) (il : typ) : expr ilfunc :=
    fold_right Abs (fold_right (fun t e => App (Inj (ilf_exists t il))
                                               (Abs t e)) (snd t) (snd (fst t)))
               (fst (fst t)).

  Definition T_app (p q : T) : option T :=
    match p, q with
      | (l::vp, tp, ep), (nil, tq, eq) =>
        Some (vp, tp ++ tq, App (lift 0 (length tq)  ep) eq)
      | _, _ => None
    end.





  Definition Rbase := (typ * expr ilfunc)%type.

  Definition typeForRbase (r : Rbase) : typ := fst r.

  Definition app (p q : T) : T := T_union p q.



  Definition T := (list typ * list typ * expr ilfunc)%type.

  Definition T_to_expr (t : T) (il : typ) : expr ilfunc :=
    fold_right Abs (fold_right (fun t e => App (Inj (ilf_exists t il))
                                               (Abs t e)) (snd t) (snd (fst t)))
               (fst (fst t)).

  Definition T_app (p q : T) : option T :=
    match p, q with
      | (l::vp, tp, ep), (nil, tq, eq) =>
        Some (vp, tp ++ tq, App (lift 0 (length tq)  ep) eq)
      | _, _ => None
    end.



  Definition T_union (p q : T) : T :=
  	(fst p ++ fst q, App (lift 0 (length (fst q)) (snd p)) (snd q)).

  Definition Rbase := (typ * expr ilfunc)%type.

  Definition typeForRbase (r : Rbase) : typ := fst r.

  Definition app (p q : T) : T := T_union p q.




   Fixpoint RD (r : R Rbase) : (typD ts nil (typeForR typeForRbase r)) ->
   (typD ts nil (typeForR typeForRbase r)) -> Prop :=
  	match r with
  		| Rfunctorial l r => fun f g => forall x y, @RD l x y -> @RD r (f x) (g y)
  		| Rinj t => fun a b => exists v, exprD us vs (snd t) (tyArr (fst t) (tyArr (fst t) tyProp)) = Some v /\ v a b
  		| Rpointwise t r => fun f g => forall x, @RD r (f x) (g x)
  	end.
(*
  Lemma RD_refl (r : R Rbase) a : @RD r a a.
  Proof.
  	induction r.
  	+ simpl.
  	  Require Import FunctionalExtensionality.
  	  apply functional_extensionality.
  	destruct a.
  	induction a.
.*)
  Lemma T_to_expr_app_wt p q tpq tq
  	(Hp : WellTyped_expr (typeof_env us) (typeof_env vs) (T_to_expr p (tyArr tq tpq)) (tyArr tq tpq))
  	(Hq : WellTyped_expr (typeof_env us) (typeof_env vs) (T_to_expr q tq) tq) :
  	WellTyped_expr (typeof_env us) (typeof_env vs) (T_to_expr (app p q) tpq) tpq.
  Proof.
  	admit.
  Qed.

  Lemma T_to_expr_app pq p tpq tp vp vpq
  	(Hpq : exprD us vs (T_to_expr pq (tyArr tp tpq)) (tyArr tp tpq) = Some vpq)
  	(Hp : exprD us vs (T_to_expr p tp) tp = Some vp) :
  	exprD us vs (T_to_expr (app pq p) tpq) tpq = Some (vpq vp).
  Proof.
  	unfold T_to_expr in *; simpl in *.
  	rewrite fold_right_app.
  	destruct p as [vps p], pq as [vpqs pq]; simpl in *.
  	induction vps; simpl in *.
  	SearchAbout exprD lift.
  	+ generalize dependent vs. clear vs. induction vpqs; simpl in *; intros.
  	  * rewrite exprD_App.
  	    assert (typeof_expr (typeof_env us) (typeof_env vs) pq = Some (tyArr tp tpq)) by admit.
  	    rewrite H0. rewrite Hpq. rewrite Hp.
  	    rewrite typ_cast_typ_refl. reflexivity.
  	  * simpl in *.
  	    red_exprD. forward; subst; inv_all; revert Hpq; subst; intros.
  	    assert (exists ILTemp, gs tpq = Some ILTemp) by admit.
  	    destruct H0. rewrite H0.
  	    red_exprD. forward. inv_all; subst.
  	    rewrite typ_cast_typ_refl.
  	    rewrite typ_cast_typ_refl.
  	    SearchAbout exprD Abs.
  	    unfold exprD. simpl.
  	    destruct vs; simpl in *.
  	    rewrite exprD'_Abs. rewrite typ_cast_typ_refl.
  	    assert (va : typD ts nil a). admit.

  	    specialize (IHvpqs (fun typD => (existT (typD ts nil) a va)::nil)).
  	    specialize (IHvpqs (a::nil)).
  	    Print sigT.
  	    Check HList.Hnil (typD ts nil).
  	    specialize (IHvpqs HList.Hnil).
  	    Print env.
  	    unfold exprD in IHvpqs. simpl in *.
  	    SearchAbout env.
  	    Check @HList.Hnil.
  	    Check @join_env.
  	    specialize (IHvpqs (@join_env _ _ (a::nil) (HList.Hnil))).
  	    rewrite IHvpqs.
  	    SearchAbout Abs exprD.
  	    Print Ltac red_exprD.
  	    SearchAbout Abs.
  	    Print exprD_rw.
  	    autorewrite with exprD_rw.
  	    rewrite exprD_Abs_is_arr.
  	    simpl in x2.
  	    red_exprD.
  	    SearchAbout exprD Inj.
  	    Print expr.
  	    rewrite exprD_Inj.
  	    red_exprD.
  	    generalize dependent gs.
  	  Check exprD_Abs.
  	  SearchAbout exprD Abs.
  	  rewrite exprD_Abs.
  	    simpl.
  	  SearchAbout typ_cast_typ.
  	  rewrite typeof_expr_exprD_same_type.
  	  SearchAbout exprD typeof_expr.
SearchAbout exprD App.
  	 apply Hp.
  Qed.

  Definition TR (us vs : env (typD ts)) (r : R Rbase) (t : T) v: Prop :=
  exists v',
    exprD us vs (T_to_expr t (typeForR typeForRbase r)) (typeForR typeForRbase r) = Some v' /\
    @RD r v v'.

Lemma typeof_expr_exprDR (e : expr ilfunc) (t : typ) v
     (Hexpr : exprD us vs e t = Some v) :
     WellTyped_expr (typeof_env us) (typeof_env vs) e t.
Proof.
	apply typeof_expr_exprD. exists v. apply Hexpr.
Qed.

  Lemma Happ : forall t1 t2 r1 r2 v1 f,
  exprD us vs f (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v1 ->
       @TR us vs (Rfunctorial t1 t2) r1 ->
       @TR us vs t1 r2 ->
       @TR us vs t2 (app r1 r2).
  Proof.
  	intros t1 t2 r1 r2 f v1 Hexpr [v2 [H1expr H1RD]] [v3 [H2expr H2RD]].
	simpl in H1RD.
	specialize (H1RD _ _ H2RD).
	exists (v2 v3). split; [|apply H1RD].
	apply T_to_expr_app. assumption. assumption.
	rewrite <- H2expr.
	apply H2expr.
	simpl.
  	apply typeof_expr_exprDR in H1expr.
  	apply typeof_expr_exprDR in H2expr.
  	pose proof (T_to_expr_app_wt H1expr H2expr) as Hexpr3.
  	apply typeof_expr_exprD in Hexpr3. destruct Hexpr3 as [v Hexpr3].
  	exists v. split. apply Hexpr3.
	simpl in H1RD.
	specialize (H1RD _ _ H2RD).
	Lemma exprD_RD_app e1 e2 e12 t12 t1 t2 v12 v1 v2 v12' v1'
	    (H12 : exprD us vs (T_to_expr e12 t12) (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v12)
		(HRD12 : @RD (Rfunctorial t1 t2) v12 v12')
		(HRD1 : @RD t1 v1 v1')
	    (H1 : exprD us vs (T_to_expr e1 (typeForR typeForRbase t1)) (typeForR typeForRbase t1) = Some v1)
		(H2 : exprD us vs (T_to_expr (app e1 e2) (typeForR typeForRbase t2)) (typeForR typeForRbase t2) = Some v2) :
		@RD t2 (v12 v1) v2.

  	generalize dependent v'1.

  	exists vpq.
  	split. apply H3.
  	eexists. split. apply H3.

    Lemma RD_functorial t1 t2 r1 r2 f g
    	(H1 : @RD (Rfunctorial t1 t2) r2) (Hr2 : r2 f g) (H2 : @RD t1 r1) :
    	@RD t2 (fun a b => forall x y, r1 x y -> a = (f x) /\ b = (g y)).
    Proof.
    	eapply H1. eassumption.
    	specialize (H1 (fun a b => forall x y, r1 x y -> a = (f x) /\ b = (g y)) f g Hr2).
   	    apply H1. simpl. in
  	eexists.




  Fixpoint pull_exists_left (p : expr ilfunc) : (list typ * expr ilfunc) :=
  	match p with
  	  | App (App (Inj (ilf_and t)) p) q =>
  	  	let (vsp, ep) := pull_exists_left p in
  	  	let (vsq, eq) := pull_exists_left q in
  	  		(vsp ++ vsq, App (App (Inj (ilf_and t)) (lift 0 (length vsq) ep)) eq)
  	  | App (App (Inj (ilf_or t)) p) q =>
  	  	let (vsp, ep) := pull_exists_left p in
  	  	let (vsq, eq) := pull_exists_left q in
  	  		(vsp ++ vsq, App (App (Inj (ilf_or t)) (lift 0 (length vsq) ep)) eq)
  	  | App (Inj (ilf_exists a _)) (Abs _ f) =>
  	  		let (vs, e) := pull_exists_left f in (a::vs, e)
  	  | _ => (nil, p)
    end.

    Fixpoint apply_exists_aux (t : typ) (vs : list typ)  (e : expr ilfunc) :=
    match vs with
    	| nil => e
		| v :: vs => App (Inj (ilf_exists v t)) (Abs v (apply_exists_aux t vs e))
	end.

	Definition apply_exists (t : typ) (x : list typ * expr ilfunc) :=
		apply_exists_aux t (fst x) (snd x).

  	Lemma sound_aux us vs e t v x (H2 : exprD us vs e t = Some v) (ILO : ILogicOps (typD ts nil t))
  	(_ : gs t = Some ILO)
  	(_ : exprD us vs e t = Some x) :
  	v |-- x.
  	Proof.
  		unfold apply_exists in H1; simpl in *.
  		specialize (H t); rewrite H0 in H.
  		rewrite H1 in H2; inv_all; subst.
  		Require Import Setoid.
  		admit.
  	Qed.
	Hint Extern 0 (Injective (typ_cast_typ ?A ?B ?C ?D ?E = Some ?F)) =>
	  eapply (Injective_typ_cast_typ_hetero_Some A B C D E F) : typeclass_instances.

  Lemma exists_pull_left_sound us (t : typ) (ILO : ILogicOps (typD ts nil t))
    (_ : gs t = Some ILO) (p : expr ilfunc) : forall vs v x
    (_ : exprD us vs p t = Some v)
  	(_ : exprD us vs (apply_exists t (pull_exists_left p)) t = Some x),
  	@lentails (typD ts nil t) ILO v x.
  Proof.
  	apply expr_strong_ind with (e := p); clear p; intros.
  	destruct e; simpl in *; eauto using sound_aux.
  	destruct e1; simpl in *; eauto using sound_aux.
  	destruct i; simpl in *; eauto using sound_aux.
  	destruct e2; simpl in *; eauto using sound_aux.
  	progress (repeat autorewrite with exprD_rw in H2); simpl in H2.
  	forward. inv_all; revert H9; subst; intros.
  	red_exprD. unfold funcAs in H6; simpl in H6. forward.
  	simpl in *. inv_all; subst.
  		  repeat (match goal with
	  		   | H : exists x, _ |- _ => destruct H; intuition; subst
	  		  end).
	  		  uip_all.
	Check exprD_App.
	rewrite (@exprD_App ts ilfunc RSym_ilfunc us vs (tyArr t0 t) t2 e2) in H7.
	rewrite exprD_App with (RSym_func := RSym_ilfunc) in H7.
	Check exprD_App.
	Check RSym_ilfunc.
	Check RSym_func.
	rewrite exprD_App in H7.
	+ red. solve_expr_acc_trans.
	+
	setoid_rewrite <- pull_exists_left.
  	red_exprD.
  	unfold apply_exists. simpl. exists v. intuition. admit.
  	unfold apply_exists. simpl. exists v. intuition. admit.
    destruct
  Qed.

End PullExistsLeft.

Section PullForallRight.
  Context {ts : types} {is : inhabited ts}.

  Fixpoint pull_forall_right (p : expr ilfunc) : (list typ * expr ilfunc) :=
  	match p with
  	  | App (App (Inj (ilf_and t)) p) q =>
  	  	let (vsp, ep) := pull_forall_right p in
  	  	let (vsq, eq) := pull_forall_right q in
  	  		(vsp ++ vsq, App (App (Inj (ilf_and t)) (lift 0 (length vsq) ep)) eq)
  	  | App (Inj (ilf_forall a _)) (Abs b f) =>
  	    if a ?[eq] b then
  	    	match is a with
  	  		| Some _ => let (vs, e) := pull_forall_right f in (a::vs, e)
  	  		| None => (nil, p)
  	  		end
  	  	else
  	  		(nil, p)
  	  | _ => (nil, p)
    end.

    Fixpoint apply_forall (vs : list typ) (t : typ) (e : expr ilfunc) :=
    match vs with
    	| nil => e
		| v :: vs => App (Inj (ilf_forall v t)) (Abs v (apply_forall vs t e))
	end.

End PullForallRight.
*)