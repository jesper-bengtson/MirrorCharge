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

Set Implicit Arguments. 
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Definition inhabited (ts : types)  := forall (t : typ),
  option (Inhabited (typD ts nil t)).
  
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
  Definition T := (list type * list typ * expr ilfunc)%type.

  Definition T_union (p q : T) : T :=
  	(fst (fst p) ++ fst (fst q), snd (fst p) ++ snd (fst q),
         App (lift 0 (length (fst (fst q))) (snd p)) (snd q)).

  Definition T_to_expr (t : T) (il : typ) := 
    fold_right (fun t e => App (Inj (ilf_exists t il)) (Abs t e)) (snd t) (fst t).

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
      | Rinj (Ent t _) =>
        Some (fst pq ++ fst p, App (lift 0 (length (fst p)) (snd pq)) (snd p))
      | Rpointwise t (Ent t' _) => 
      | _ => None
    end.

  Definition abs (vs us : tenv typ) (t : typ) (p : T) (r : R Rbase) : option T :=
    Some (t :: fst p, snd p).

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

  Definition atom (us vs : tenv typ) (e : expr ilfunc) (r : R Rbase) : option T := Some (nil, e).

  Definition TD us vs (t : T) (il : typ) := exprD us vs (T_to_expr t il) il.

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
    exists v', TD us vs t (typeForR typeForRbase r) = Some v' /\ @RD r v v'.
(*
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
      clear H1; clear Heqb.
      generalize dependent r'.
      induction r; intros; simpl in *.
      
      
  Lemma unification_type r r' t (H : unify r' r = true) 
    (H1 : pr_type typeForRbase r t) : typeForR typeForRbase r' = t.
  Proof.
    generalize dependent r; induction r'; simpl; intros.
    + destruct r0; try congruence.
      - assert (r0 = r) by admit; subst. 
        inversion H1; reflexivity.
      - 
  Qed.
 
Print pr_type.
    + remember (exprD' us0 tvs e (typeForR typeForRbase r')).
      destruct o; [|apply I].
      intros. unfold atom in H0. inversion H0; subst.
      unfold TR.
      clear H0. exists (t0 vs0).
      split. unfold TD. simpl.
      unfold exprD; simpl.
      rewrite split_env_join_env.
      unfold T_to_expr; simpl.
      remember (exprD' us0 tvs e (typeForR typeForRbase r')).
      destruct o; inv_all; subst; [reflexivity|congruence].
      apply RD_reflexive.
  Qed.
*)
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
                   (inj_exists (tyType 1) inj_true)
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

