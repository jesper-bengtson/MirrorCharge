Require Import ILogic ILInsts.
Require Import ILogicFunc.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MapPositive.
Require Import MirrorCore.SymI.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Data.Positive.
Require Import Ext.ExprLift.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import MirrorCore.EnvI.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import Ext.SetoidFold.
Require Import Relation_Definitions.
Require Import MirrorCore.Ext.AppFull.
Require Import ILFFold SepLogFold. 

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Definition inhabited (ts : types)  := forall (t : typ),
  option (Inhabited (typD ts nil t)).

Section PullQuant.
  Context (ts : types) (funcs : fun_map ts).
  Context (gs : logic_ops ts) {gsOk : logic_opsOk gs}.
  Context {es : embed_ops ts} {esOk : embed_opsOk gs es}.
  Context {is : inhabited ts}.
  Variable slspec : SepLogSpec ilfunc.

  Definition TT := option (list typ * expr ilfunc)%type.

  Local Instance RSym_sym : SymI.RSym (typD ts) ilfunc := RSym_ilfunc funcs gs es.

  Let T:Type := tenv typ -> tenv typ -> TT.
  Definition atomic (e : expr ilfunc) : T := fun _ _ => Some (nil, e).

  Definition pq_var (v : var) : T := atomic (Var v).
  Definition pq_uvar (u : uvar) : T := atomic (UVar u).
  Definition pq_inj (s : ilfunc) : T := atomic (Inj s).
  Definition pq_abs (x : typ) (e : expr ilfunc) (_ : T) : T :=
    atomic (Abs x e).

  Definition pq_app (f : expr ilfunc) (_ : T) (args : list (expr ilfunc * T)) : T :=
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
      | Inj f, (_, a)::(_, b)::nil =>
      	if slspec.(is_star) f then
	        match a us vs, b us vs with
	          | Some (xs, a), Some (ys, b) => Some (xs ++ ys,
	                                                App (App (Inj f) (lift 0 (length ys) a))
	                                                    (lift (length ys) (length xs) b))
	          | _, _                       => None
	        end
	    else 
	    	None
      | _, _ => None
    end.

  Definition pq_exists (t t_logic : typ) (_ : expr ilfunc) (a : T) : T :=
    fun us vs =>
      match a us (t :: vs) with
  	| Some (ts, a) => Some (t :: ts, a)
	| None => None
      end.

  Definition pq_forall (t t_logic : typ) (f : expr ilfunc) (a : T) : T := atomic (Abs t f).

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

  Definition TD (t : typ) (e : TT) (us vs : tenv typ) :=
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

  Definition PQR (t : typ) (e : expr ilfunc) (arg : TT) (us vs : tenv typ) :=
    match TD t arg us vs, exprD' us vs e t, gs t with
      | None, _, _ => True
      | _, _, None => True
      | Some p, Some q, Some _ => forall us vs, (p us vs) |-- (q us vs)
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

  Lemma Hatomic tus tvs t e (H : typeof_expr tus tvs e = Some t) :
    PQR t e (atomic e tus tvs) tus tvs.
  Proof.
    unfold atomic, PQR, TD; simpl. forward.
    reflexivity.
  Qed.

  Lemma Habs
  : forall tus tvs t t' e e_res,
      typeof_expr tus tvs (Abs t e) = Some (tyArr t t') ->
      @PQR t' e (e_res tus (t :: tvs)) tus (t :: tvs) ->
      @PQR (tyArr t t') (Abs t e) (pq_abs t e e_res tus tvs) tus tvs.
  Proof.
    intros; apply Hatomic; assumption.
  Qed.

  Lemma Hex
  : forall (tus tvs : tenv typ) t t_logic e (e_res : T),
      typeof_expr tus tvs (App (Inj (ilf_exists t t_logic)) (Abs t e)) = Some t_logic ->
      PQR t_logic e (e_res tus (t :: tvs)) tus (t :: tvs) ->
      PQR t_logic
          (App (Inj (ilf_exists t t_logic)) (Abs t e))
          (@pq_exists t t_logic e e_res tus tvs) tus tvs.
  Proof.
    intros.
    unfold PQR, pq_exists in *; simpl in *.
    red_exprD; forward; inv_all; subst.
    red_exprD; forward; inv_all; subst.
    red_exprD.
    unfold type_of_apply in H2; simpl in H2. forward. destruct H2; subst. inv_all; subst.
    remember (e_res tus (t :: tvs)) as o; destruct o; [| compute in H4; congruence].
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
        forall u g, x u g -|- lexists (fun v => y u (HList.Hcons v g)).
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
        forall us vs, dtm' us vs -|- lexists (fun vs' => dtm us (HList.hlist_app vs' vs)).
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
      specialize (IHxs (fun x => match H1 in _ = vs return hlist (typD ts nil) tus -> hlist (typD ts nil) vs -> typD ts nil Ty with
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
          specialize (H3 us (Hcons x0 vs)).
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
        forall us g, x us g -|- lexists (fun v => y us (HList.hlist_app v g)).
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
      exists (fun us z =>
                x1 us match H0 in _ = t return HList.hlist (typD ts nil) t with
                       | eq_refl => z
                      end).
      generalize H.
      change (a :: tvs) with ((a :: nil) ++ tvs) in *.
      assert (forall us, forall g : HList.hlist (typD ts nil) tvs,
                x us g -|- Exists v : HList.hlist (typD ts nil) (a :: nil), x0 us (HList.hlist_app v g)).
      { intros. specialize (H1 us g).
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
        forall us g, x us g -|- lexists (fun v => y us (HList.hlist_app v g)).
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

  Lemma hlist_app_cons A F (xs ys : list A) (x : A) (el : F x) (hxs : hlist F xs) (hys : hlist F ys) :
    Hcons el (hlist_app hxs hys) = hlist_app (Hcons el hxs) hys.
  Proof.
    simpl. reflexivity.
  Qed.

  Lemma lift_entails tus xs ys zs e t de df us (HILops : ILogicOps (typD ts nil t)) (HIL: ILogic (typD ts nil t))
	(He : exprD' tus (xs ++ ys ++ zs) (lift (length xs) (length ys) e) t = Some de)
	(Hf : exprD' tus (xs ++ zs) e t = Some df)
	(hxs : hlist (typD ts nil) xs)
	(hys : hlist (typD ts nil) ys)
	(hzs : hlist (typD ts nil) zs) :
    de us (hlist_app hxs (hlist_app hys hzs)) |-- df us (hlist_app hxs hzs).
  Proof.
    induction ys; intros; simpl in *.
    + rewrite hlist_app_nil.
      rewrite He in Hf. inversion Hf. reflexivity.
    + replace (S (length ys)) with (1 + length ys) in He by omega.
      rewrite <- lift_lift', <- lift_lift in He.
      pose proof (exprD'_lift RSym_sym tus xs (a::nil) (ys++zs) (lift (length xs) (length ys) e) t).
      simpl in *. forward; inv_all; subst.
      specialize (IHys t1).
      specialize (H1 us hxs (Hcons (hlist_hd hys) Hnil) (hlist_app (hlist_tl hys) hzs)).
      simpl in H1.
      rewrite hlist_app_cons, <- hlist_cons_eta in H1.
      rewrite H1 at 1. apply IHys. reflexivity.
  Qed.
(*
  Lemma add_quants_app tus tvs xs ys t p q d (IL : ILogicOps (typD ts nil t))
  	(H : exprD' tus tvs (add_quants (xs ++ ys) t (App (lift 0 (length ys) p) (lift (length ys) (length xs) q))) t = Some d) :
    exists tq dp dq,
      typeof_expr tus (rev ys ++ tvs) q = Some tq /\
      exprD' tus tvs (add_quants xs (tyArr tq t) p) (tyArr tq t) = Some dp /\ exprD' tus tvs (add_quants ys tq q) tq = Some dq /\
      forall us vs, d us vs |-- (dp us vs) (dq us vs).
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
*)


  Lemma Happ
  : forall tus tvs l (l_res : T) rs t ts,
      typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
      let ft := fold_right tyArr t ts in
      PQR ft l (l_res tus tvs) tus tvs ->
      Forall2 (fun t x =>
                    typeof_expr tus tvs (fst x) = Some t
                 /\ PQR t (fst x) (snd x tus tvs) tus tvs)
              ts rs ->
      PQR t (apps l (map fst rs)) (pq_app l l_res rs tus tvs) tus tvs.
   Proof.
    admit.
    (*
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
          specialize (H13 us Hnil x4 (hlist_app x3 vs)). simpl in H13. rewrite H13. reflexivity.
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
          specialize (H13 us Hnil x4 (hlist_app x3 vs)). simpl in H13. rewrite H13. reflexivity.
        + apply lorR2.
          rewrite <- H18. rewrite H16. apply lexistsR with x4.
          rewrite H5. reflexivity.
   *)
   Qed.

End PullQuant.
