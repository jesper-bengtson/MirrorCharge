Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".
Add Rec LoadPath "/Users/jebe/git/mirror-core/src/" as MirrorCore.
Add Rec LoadPath "/Users/jebe/git/mirror-core/coq-ext-lib/theories" as ExtLib.
Add Rec LoadPath "/Users/jebe/git/MirrorCharge/MirrorCharge!/bin".

Require Import ILogic ILInsts ILogicFunc.
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

Set Implicit Arguments. 
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Definition inhabited (ts : types)  := forall (t : typ),
  option (Inhabited (typD ts nil t)).
  
Section PullQuant.
  Context (ts : types) (funcs : fun_map ts) (gs : logic_ops ts).
  Context {es : embed_ops ts}.

  Definition TT := option (list typ * expr ilfunc)%type.

  Local Instance RSym_sym : SymI.RSym (typD ts) ilfunc := RSym_ilfunc funcs gs es.

  Let T := tenv typ -> tenv typ -> TT.
  Definition atomic (e : expr ilfunc) : T := fun _ _ => Some (nil, e).

  Definition pq_var (v : var) : T := atomic (Var v).
  Definition pq_uvar (u : uvar) : T := atomic (UVar u).
  Definition pq_inj (s : ilfunc) : T := atomic (Inj s).
  Definition pq_abs (x : typ) (e : expr ilfunc) (t : T) : T := 
    fun us vs => t us (x::vs).

  Definition pq_app (f : expr ilfunc) (_ : T) (args : list (expr ilfunc * T)) : T :=
    fun us vs =>
    match f, args with
      | Inj (ilf_true t), nil => (atomic f) us vs
      | Inj (ilf_and t), (_, a)::(_, b)::nil =>
        match a us vs, b us vs with
          | Some (xs, a), Some (ys, b) => Some (xs ++ ys, App (App f a) (lift 0 (length xs) b))
          | _, _                       => None
        end
      | Inj (ilf_exists x t), (_, f)::nil =>
        match f us vs with
          | Some (ys, f) => Some (x::ys, f) 
          | _            => None
        end
      | _, _ => None
    end.

    Definition pqArgs : AppFullFoldArgs ilfunc TT :=
      @Build_AppFullFoldArgs ilfunc TT pq_var pq_uvar pq_inj pq_abs pq_app.

    Definition Teval (e : TT) (t : typ) :=
      match e with
          | Some (xs, a) => 
            Some (fold_right (fun x a => App (Inj (ilf_exists x t)) 
                                             (Abs x a)) a xs)
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

    Definition PQR (t : typ) {HIL : ILogicOps (typD ts nil t)} (e : expr ilfunc) (arg : TT) (us : env (typD ts)) (vs : tenv typ) :=
      match TD t arg us vs, exprD' us vs e t with
        | None, _ => True
        | Some p, Some q => forall vs, (p vs) |-- (q vs)
        | _, _ => False
      end.

  Lemma Habs
    : forall tus tvs t t' e e_res {HIL : ILogicOps (typD ts nil t')} {HIL' : ILogicOps (typD ts nil (tyArr t t'))},
        typeof_expr (typeof_env tus) tvs (Abs t e) = Some (tyArr t t') ->
        @PQR t' _ e (e_res (typeof_env tus) (t :: tvs)) tus (t :: tvs) ->
        @PQR (tyArr t t') HIL' (Abs t e) (pq_abs t e e_res (typeof_env tus) tvs) tus tvs.
  Proof.
    intros.
    unfold PQR, pq_abs in *; simpl in *.
    remember (exprD' tus tvs (Abs t e) (tyArr t t')) as o; destruct o.
    rewrite exprD'_Abs in Heqo. rewrite typ_cast_typ_refl in Heqo.
    remember (exprD' tus (t :: tvs) e t') as o; destruct o; [|inversion Heqo].
    inv_all; subst.
    unfold TD, Teval in *; simpl in *.
    remember (e_res (typeof_env tus) (t :: tvs)) as o; destruct o; [|apply I].
    destruct p; simpl in *.
    induction l; simpl in *.

    SearchAbout exprD' tyArr.
    red_exprD.
    admit.

    Lemma Hatomic
    : forall tus tvs v,
            PQtype (Var v) (pq_var v tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             PQR (Var v) (pq_var v tus tvs) us vs.
    Proof.
      intros.
      split.
      unfold PQtype, pq_var, atomic, Ttype.
      simpl.
      remember (nth_error tvs v).
      destruct e; [apply rel_dec_correct; reflexivity | apply I].
      intros.
      unfold PQR. simpl.
      remember (nth_error (typeof_env vs) v).
      destruct e; [|apply I].

      unfold TD. remember (Teval (pq_var v tus tvs) t) as o; destruct o.
      simpl in *. inv_all; subst. reflexivity.
      simpl in *. inversion Heqo.
    Qed.
(*
      Lemma typeof_expr_fold_cons uvs t t' vvs (f : typ -> expr ilfunc -> typ -> expr ilfunc) (e : expr ilfunc) l
            (H : typeof_expr uvs (t::vvs) (fold_right (fun x e => f x e t') e l) = Some t') :
            typeof_expr uvs vvs (fold_right (fun x e => f x e (tyArr t t')) e l) = Some (tyArr t t').
        induction l; simpl in *.
        induction e; simpl in *.
*)

    Lemma typeof_expr_apps uvs vvs e lst (H: typeof_expr uvs vvs e = None) :
      typeof_expr uvs vvs (apps e lst) = None.
    Proof.
      generalize dependent e; induction lst; intros; simpl.
      + apply H.
      + apply IHlst; simpl; rewrite H; reflexivity.
    Qed.

    Ltac PQtype_elim :=
    match goal with 
      | |- match ?o with | Some _ => _ | None => True end => destruct o; apply I
    end.

    Lemma Happ
    : forall tus tvs l l_res rs,
        PQtype l (l_res tus tvs) tus tvs ->
        List.Forall (fun x => PQtype (fst x) (snd x tus tvs) tus tvs) rs ->
           PQtype (apps l (map fst rs)) (pq_app l l_res rs tus tvs) tus tvs
        /\ forall us vs,
             PQR l (l_res tus tvs) us vs ->
             List.Forall (fun x => PQR (fst x) (snd x tus tvs) us vs) rs ->
             PQR (apps l (map fst rs))
                 (pq_app l l_res rs tus tvs)
                 us vs.
      Proof.
        intros; split.
        + unfold PQtype in *.
          remember (typeof_expr tus tvs l) as o; destruct o.
          - destruct l; simpl; try PQtype_elim.
            destruct i; simpl; try PQtype_elim.
            * destruct rs; simpl; try PQtype_elim.
              remember (gs t0) as o; destruct o; [|apply I].
              unfold atomic, Ttype; simpl. rewrite <- Heqo0.
              apply rel_dec_correct. reflexivity.
            * destruct rs; simpl; try PQtype_elim.
              destruct p; simpl in *.
              destruct rs; simpl; try PQtype_elim. 
              destruct p; simpl in *.
              destruct rs; simpl; try PQtype_elim.
              destruct (gs t0); [|apply I].
              inv_all; subst.
              simpl.
              inversion H0; subst; clear H0.
              inversion H4; subst; clear H4.
              simpl in *. clear H5.
              remember (typeof_expr tus tvs e) as o; destruct o; [|apply I].
              remember (typ_eqb t0 t) as b; destruct b; [|apply I].
              remember (typeof_expr tus tvs e0) as o; destruct o; [|apply I].
              simpl. 
              remember (typ_eqb t0 t3) as b; destruct b; [|apply I].
              remember (t1 tus tvs) as o; destruct o; [|apply I]; destruct p; simpl.
              remember (t2 tus tvs) as o; destruct o; [|apply I]; destruct p; simpl.
              remember (Ttype tus tvs
                              (Some
                                 (l ++ l0, App (App (Inj (ilf_and t0)) e1) 
                                               (lift 0 (length l) e2)))
                              t0) as o; destruct o; [|apply I].
              symmetry in Heqb; symmetry in Heqb0.
              apply typ_eqb_true in Heqb; apply typ_eqb_true in Heqb0; do 2 subst.
              clear -Heqo3 Heqo Heqo0.
              induction l. simpl in *.
              induction l0; simpl in *.
              unfold Ttype in *; simpl in *.
              destruct (gs t3); [|congruence].
              rewrite <- Heqo0.
              admit.
              remember (t2 tus tvs) as o; destruct o; [|apply I]; destruct p; simpl.
              simpl.
              Set Printing All.
              rewrite <- Heqo1.
              admit.
              remember (typ_eqb t0 tx) as b; destruct b.
inversion H0; subst. destruct p; simpl in *.
              
            simpl.
            remember (typeof_expr tus tvs (apps (Var v) (map fst rs))) as o; destruct o; apply I.
            admit.
            intuition.
            unfold Ttype; simpl.
            remember (map fst rs).clear Heql.
            destruct rs; simpl in *.

             Print List.Forall.
            induction l. simpl.
            simpl.
          - rewrite typeof_expr_apps; intuition.
          
          Eval compute in apps (Var 0) (Var 1::Var 2::Var 3::nil).

        unfold PQtype in *; destruct l; simpl.
        destruct rs. simpl.
        admit. simpl. destruct p; simpl.
        unfold apps. simpl.
        unfold pq_app.
        destruct l.
        split.
Print apps.
        unfold PQtype in *.
        simpl in *.
        unfold PQtype in *.v

    Lemma Habs : forall tus tvs t e e_res,
        PQtype e (e_res tus (t :: tvs)) tus (t :: tvs) ->
           PQtype (Abs t e) (pq_abs t e e_res tus tvs) tus tvs
        /\ forall us vs,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             (forall x,
                PQR e (e_res tus (t :: tvs)) us (@existT _ _ t x :: vs)) ->
             PQR (Abs t e) (pq_abs t e e_res tus tvs) us vs.
    Proof.
      intros.
      split.
      unfold PQtype, pq_abs in *.
      simpl. remember (typeof_expr tus (t :: tvs) e) as o; destruct o; [|apply I].
      unfold Ttype, Teval in *; simpl in *.
      remember (e_res tus (t :: tvs)) as o; destruct o; [|destruct H].
      destruct p.
      
      
      remember (typeof_expr tus (t::tvs) (fold_right
          (fun (x : typ) (a : expr ilfunc) =>
           App (Inj (ilf_exists x t0)) (Abs x a)) e0 l)) as o.
      destruct o; [|destruct H].


Print typeof_expr.
        simpl.

      SearchAbout typeof_expr.
      pose proof (typeof_expr_lift RSym_sym tus nil (t::nil) tvs
                                   ((fold_right
               (fun (x : typ) (a : expr ilfunc) =>
                App (Inj (ilf_exists x (tyArr t t0))) (Abs x a)) e0 l))).
      simpl in H0. rewrite <- H0. clear H0.
      
      
      remember 
      admit.
      forward.
      simpl in *.
      simpl.
      

      remember (typeof_expr tus tvs (Abs t e)) as o; destruct o; [|apply I].
      simpl in *.
      red_exprD.



    Lemma Hatomic : forall us tvs t e val,
                   exprD' us tvs e t = Some val ->
                   forall vs,
                     @PQR t (val vs) (atomic e (typeof_env us) tvs) us (join_env vs).    
    Proof.
      intros; unfold PQR; simpl. 
      match goal with 
        | |- ?x = _ => let x' := eval red in x in change x with x'
      end;
      rewrite split_env_join_env, H; reflexivity.
    Qed.

    Definition PQvar us tvs t v val := @Hatomic us tvs t (Var v) val.
    Definition PQuvar us tvs t u val := @Hatomic us tvs t (UVar u) val.
    Definition PQinj us tvs t i val := @Hatomic us tvs t (Inj i) val.

    Require Import ExtLib.Data.HList.

    Lemma PQabs : forall us tvs t t' e e_res val,
                        exprD' us (t :: tvs) e t' = Some val ->
                        forall (vs : hlist (typD ts nil) tvs),
                          (forall x,
                             @PQR t' (val (Hcons x vs)) (e_res (typeof_env us) (t :: tvs))
                               us ((@existT _ (typD ts nil) t x) :: join_env vs)) ->
                          @PQR (tyArr t t') (fun x => val (Hcons x vs))
                            (pq_abs t e e_res (typeof_env us) tvs) us (join_env vs).
    Proof.
      intros.
      unfold PQR, TD, pq_abs in *.

      forward.
      SearchAbout exprD' cons.
      simpl in *. unfold pq_abs.
      assert (tvs <> nil). {
        intros Htvs.
        remember (e_res (typeof_env us) (t :: tvs)) as o.
        destruct o; simpl in *.
        admit.
        rewrite Htvs in *.        
      }.
      assert (~(length tvs = 0)). {
        intro Htvs.
        assert (tvs = nil).
      assert (length tvs > 0).
      destruct o; simpl in *; try congruence.
      destruct p; simpl in *.
      admit. 
      Check e_res.
      unfold e_res in Heqo.
      Print 
specialize (
      forward.
    Qed.

    Lemma PQapp
    : forall us tvs l l_res (rs : list (expr ilfunc * T)) t
             (tvals : list {t : typ & hlist (typD ts nil) tvs -> typD ts nil t}) val,
        exprD' us tvs l (fold_left (fun x y => tyArr y x) (map (@projT1 _ _) tvals) t) = Some val ->
        Forall2 (fun e tval => exprD' us tvs (fst e) (projT1 tval) = Some (projT2 tval))
                rs
                tvals ->
        forall vs : hlist (typD ts nil) tvs,
          @PQR (fold_left (fun x y => tyArr y x) (map (@projT1 _ _) tvals) t)
             (val vs) (l_res (typeof_env us) tvs) us (join_env vs) ->
          Forall2 (fun x (t : {t : typ & hlist (typD ts nil) tvs -> typD ts nil t}) =>
                     @PQR (projT1 t) (projT2 t vs) (snd x (typeof_env us) tvs) us (join_env vs))
                  rs
                  tvals ->
          @PQR t (@apply ts _ vs tvals t (val vs))
             (pq_app l l_res rs (typeof_env us) tvs)
             us (join_env vs).
    Proof.
      admit.
    Qed.

      Check @semArgsOk ts ilfunc RSym_sym TT pq_var pq_uvar pq_inj pq_abs pq_app (@PQR)
            (@PQvar) (@PQuvar) (@PQinj) (@PQabs) (@PQapp).


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

