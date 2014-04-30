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
  Check logic_ops.
 
  Inductive variance := CoVariant | ContraVariant.
  Inductive pull_type := PAll | PExists.

  Definition TT := variance -> pull_type -> list typ * expr ilfunc.

  Local Instance RSym_sym : SymI.RSym (typD ts) ilfunc := RSym_ilfunc funcs gs es.

  Let T:Type := tenv typ -> tenv typ -> TT.
  Definition atomic (e : expr ilfunc) : T := fun _ _ _ _ => (nil, e).

  Definition pq_var (v : var) : T := atomic (Var v).
  Definition pq_uvar (u : uvar) : T := atomic (UVar u).
  Definition pq_inj (s : ilfunc) : T := atomic (Inj s).
  Definition pq_abs (x : typ) (e : expr ilfunc) (_ : T) : T :=
    atomic (Abs x e).
    
  Definition pq_env := ilfunc -> variance -> pull_type -> list (option (variance * pull_type)).

  Fixpoint pq_app_aux (us vs : tenv typ) (ats : list (option (variance * pull_type))) (f : list typ * expr ilfunc) (args : list (expr ilfunc * T)) : list typ * expr ilfunc :=
  match ats, args with
  	| Some (var, pt)::ats, (_, t)::args =>
  	  match f, t us vs var pt with
  	  	| (xs, f'), (ys, a) => pq_app_aux us vs ats (ys ++ xs, App (lift 0 (length ys) f') (lift (length xs) (length ys) a)) args
  	  end
  	| None::ats, (e, _)::args => 
  	  match f with
  	    | (xs, f') => pq_app_aux us vs ats (xs, App f' (lift 0 (length xs) e)) args
  	  end
  	| _, _ => match f with
  			  | (xs, f') => (xs, apps f' (map fst args))
  			  end
  end.
  
  Definition pq_app (e : pq_env) (f : expr ilfunc) (_ : T) (args : list (expr ilfunc * T)) : T :=
  	fun us vs var pt => 
  		match f with
  			| Inj f => pq_app_aux us vs (e f var pt) (nil, Inj f) args
  			| _     => (nil, f)
  		end.
 
  Definition pq_exists (t t_logic : typ) (f : expr ilfunc) (a : T) : T :=
    fun us vs vm pt =>
      match pt with
      	| PExists => let (ts, a) := a us (t :: vs) vm pt in (t::ts, a)
      	| _       => (nil, App (Inj (ilf_exists t t_logic)) (Abs t f)) 
      	
      end.

  Definition pqArgs (e : pq_env) : AppFullFoldArgs ilfunc TT :=
    @Build_AppFullFoldArgs ilfunc TT pq_var pq_uvar pq_inj pq_abs (pq_app e).

  Definition get_quant (pt : pull_type) :=
  	match pt with
  	  | PAll => ilf_forall
  	  | Pexists => ilf_exists
  	end.

  Definition add_quant (pt : pull_type) (t : typ) (x : typ) (e : expr ilfunc) :=
    App (Inj ((get_quant pt) x t)) (Abs x e).

  Definition add_quants (pt : pull_type) (t : typ) (xs : list typ) (e : expr ilfunc) :=
    fold_right (fun x a => add_quant pt t x a) e xs.
 
 Definition pt_quant (pt : pull_type) := 
 	match pt with
 	  | PExists => @lexists
 	  | PForall => @lforall
    end.
    
  Require Import Morphisms.

Section pt_quant_morphisms.

  Context {A : Type} `{HIL : ILogic A}.

  Global Instance pt_quant_lentails_m T (pt : pull_type):
    Proper (pointwise_relation T lentails ++> lentails) (pt_quant pt _).
  Proof.
    destruct pt; simpl; [apply @lforall_lentails_m | apply @lexists_lentails_m]; apply _.
  Qed.

  Global Instance pt_quant_lequiv_m T (pt : pull_type):
    Proper (pointwise_relation T lequiv ++> lequiv) (pt_quant pt _).
  Proof.
    destruct pt; simpl; [apply @lforall_lequiv_m | apply @lexists_lequiv_m]; apply _.
  Qed.

End pt_quant_morphisms.
  
	 Fixpoint ILogic_Ops_fold_fun (t : typ) (ILOps : ILogicOps (typD ts nil t)) (typs : list typ) : ILogicOps (typD ts nil (fold_right tyArr t typs)) :=
	 	match typs with
	 		| nil      => ILOps
	 		| t'::typs => @ILFun_Ops (typD ts nil t') (typD ts nil (fold_right tyArr t typs)) (@ILogic_Ops_fold_fun t ILOps typs)
	 	end.
       
     Fixpoint ILogic_fold_fun (t : typ) (ILOps : ILogicOps (typD ts nil t)) (IL : ILogic (typD ts nil t)) (typs : list typ) : ILogic (typD ts nil (fold_right tyArr t typs)) :=
     	match typs with
     		| nil      => _
     		| t'::typs => @ILFun_ILogic (typD ts nil t') (typD ts nil (fold_right tyArr t typs)) (@ILogic_Ops_fold_fun t ILOps typs) (@ILogic_fold_fun t ILOps IL typs)
     	end.
     
     Local Existing Instance ILogic_Ops_fold_fun.
     Local Existing Instance ILogic_fold_fun.
  
  
  Local Existing Instance ILFun_Ops.
  
  Require Import Program.Basics.
  
  Definition var_entail (var : variance) (A : Type) (ILOps: ILogicOps A) :=
  	match var with
  	  | CoVariant => (@lentails A ILOps)
  	  | ContraVariant => (flip lentails)
    end.
  Check @lequiv.
  
  Inductive valid_arg (pt : pull_type) (var : variance) (t : typ) (ILOps : ILogicOps (typD ts nil t)) (A : Type) : 
    forall typs : list typ,  (A -> typD ts nil (fold_right tyArr t typs)) -> list (option (variance * pull_type)) -> Prop :=
    | ve_nil f : @valid_arg pt var t ILOps A nil f nil
    | ve_none te typs (f : A -> typD ts nil te -> typD ts nil (fold_right tyArr t typs)) args : 
      (forall (e : typD ts nil te), (var_entail var _) (((pt_quant pt) _ _ f) e) ((pt_quant pt) _ _ (fun x => (f x) e))) ->
      (forall e, @valid_arg pt var t ILOps A typs (fun x => (f x) e) args) ->
      @valid_arg pt var t ILOps A (te::typs) f (None::args)
    | ve_some te typs (f : A -> typD ts nil te -> typD ts nil (fold_right tyArr t typs)) pt' var' args :
      forall B (e : B -> typD ts nil te) (ILOps' : ILogicOps (typD ts nil te)), 
             (var_entail var _) (((pt_quant pt) _ _ f) ((pt_quant pt') _ _ e)) ((pt_quant pt) _ _ (fun x => (pt_quant pt) _ _ (fun y => (f x) (e y)))) ->
      @valid_arg pt var t ILOps ((A * B)%type) typs (fun x => (f (fst x)) (e (snd x))) args ->       
      @valid_arg pt var t ILOps A (te::typs) f ((Some (var', pt'))::args).

  Definition valid_env (tus tvs : tenv typ) (xs : list typ) (pt : pull_type) (var : variance) (t : typ) (ILOps : ILogicOps (typD ts nil t)) (typs : list typ)
                       (f : expr ilfunc) modes :=
                       forall df, exprD' tus (rev xs ++ tvs) f (fold_right tyArr t typs) = Some df ->
                       forall us vs, @valid_arg pt var t ILOps (HList.hlist _ (rev xs)) typs (fun x => df us (HList.hlist_app x vs)) modes.
  

  Lemma valid_arg_none_inv (pt : pull_type) (var : variance) (t te : typ) (ILOps : ILogicOps (typD ts nil t)) (A : Type) 
    (typs : list typ) (f : A -> typD ts nil te -> typD ts nil (fold_right tyArr t typs)) (modes : list (option (variance * pull_type))) 
    (H : @valid_arg pt var t ILOps A (te::typs) f (None::modes)) : 
      (forall (e : typD ts nil te), (var_entail var _) (((pt_quant pt) _ _ f) e) ((pt_quant pt) _ _ (fun x => (f x) e))) /\
      (forall e, @valid_arg pt var t ILOps A typs (fun x => (f x) e) modes).
  Proof.
    change (typD ts nil te -> typD ts nil (fold_right tyArr t typs)) with (typD ts nil (fold_right tyArr t (te::typs))) in f.
    inversion H. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H3. subst.
    intuition.
  Qed.

  Definition Teval (pt : pull_type) (e : list typ * expr ilfunc) (t : typ) :=
    let (xs, a) := e in add_quants pt t xs a.
        
  Definition TD (pt : pull_type) (t : typ) (e : list typ * expr ilfunc) (us vs : tenv typ) :=
    exprD' us vs (Teval pt e t) t.
(*
  Definition Ttype (var : variance) (pt : pull_type) (ts us : tenv typ) (e : TT) (t : typ) :=
    typeof_expr ts us (Teval pt e t).

  Definition PQtype (var : variance) (pt : pull_type) (e : expr ilfunc) (tt : TT) (us vs : tenv typ) :=
    match typeof_expr us vs e with
      | Some t =>
        match Ttype var pt us vs tt t with
          | Some t' => t ?[eq] t' = true
          | None    => True
        end
      | None => True
    end.
    *)
Check @TD.
  Definition PQR_aux var pt (t : typ) 
                     (arg : list typ * expr ilfunc)
                     (e : expr ilfunc) (us vs : tenv typ) 
                      :=
   
    match (TD pt t arg) us vs, exprD' us vs e t, gs t, var with
      | None, _, _, _ => True
      | _, _, None, _ => True
      | Some p, Some q, Some _, CoVariant     => forall us vs, (p us vs) |-- (q us vs)
      | Some p, Some q, Some _, ContraVariant => forall us vs, (q us vs) |-- (p us vs)
      | _, _, _, _ => False
    end.
    
  Definition PQR (t : typ) (e : expr ilfunc) (arg : TT) (us vs : tenv typ) :=
  	forall var pt, PQR_aux var pt t (arg var pt) e us vs.

  Lemma ILogic_from_env (t : typ) (i : ILogicOps (typD ts nil t)) (pf : gs t = Some i)
  : @ILogic _ i.
  Proof.
    specialize (gsOk t).
    rewrite pf in *. intros. assumption.
  Defined.
  Hint Extern 1 (@ILogic _ _) => (apply ILogic_from_env; [ assumption ]) : typeclass_instances.

  Lemma Refl_from_env (t : typ) (i : ILogicOps (typD ts nil t)) (pf : gs t = Some i)
  : Reflexive (@lentails _ i).
  Proof.
    specialize (gsOk t).
    rewrite pf in *. intros.
    apply lentailsPre.
  Defined.
  Hint Extern 1 (Reflexive _) => (apply Refl_from_env; [ assumption ]) : typeclass_instances.

  Lemma Refl_from_env_lequiv (t : typ) (i : ILogicOps (typD ts nil t)) (pf : gs t = Some i)
  : Reflexive (@lequiv _ i).
  Proof.
    specialize (gsOk t).
    rewrite pf in *.
    intros. split; reflexivity.
  Defined.
  Hint Extern 1 (Reflexive _) => (apply Refl_from_env_lequiv; [ assumption ]) : typeclass_instances.

  Lemma Hatomic tus tvs t e (H : typeof_expr tus tvs e = Some t) :
    PQR t e (atomic e tus tvs) tus tvs.
  Proof.
    unfold atomic, PQR, PQR_aux, TD, Teval; simpl; intros. 
    forward. 
    destruct var, pt; forward; simpl in *; forward; inv_all; subst; reflexivity.
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
    unfold PQR; intros. 
    specialize (H0 var pt).
    destruct pt; simpl in *; unfold PQR_aux, TD, Teval in *; simpl in *.
    + red_exprD; forward; inv_all; subst. 
      destruct var; intros; uip_all; reflexivity.
    + red_exprD; forward; simpl in *; inv_all; simpl in *; subst. unfold add_quant in H5; simpl in H5.
      red_exprD; forward; simpl in *; inv_all; simpl in *. revert H10. subst.  intros. destruct H3; subst.
      red_exprD; forward; simpl in *; inv_all; simpl in *; subst.
      red_exprD; forward; inv_all; simpl in *; subst.
      uip_all. subst.
      destruct var; intros; setoid_rewrite H8; reflexivity.
  Qed.

  Lemma typeof_expr_apps uvs vvs e lst (H: typeof_expr uvs vvs e = None) :
    typeof_expr uvs vvs (apps e lst) = None.
  Proof.
    generalize dependent e; induction lst; intros; simpl.
    + apply H.
    + apply IHlst; simpl; rewrite H; reflexivity.
  Qed.

  (* Note: [forward] will do this *)
  Ltac PQtype_elim :=
    match goal with
      | |- match ?o with | Some _ => _ | None => True end => destruct o; apply I
    end.

  Lemma pqapp_nil pq_env l l_res tus tvs pt vars : 
  	pq_app pq_env l l_res nil tus tvs pt vars = (nil, l).
  Proof.
    unfold pq_app.
    destruct l; try reflexivity.
    destruct (pq_env i pt vars); [reflexivity|]. simpl. destruct o; try reflexivity.
    destruct p; reflexivity.
  Qed.

  Lemma pqapp_cons_cases pq_env a ats l l_res tus tvs pt vars xs e 
  	(H : pq_app pq_env l l_res (a :: ats) tus tvs pt vars = (xs, e)) :
  	(xs = nil /\ e = l) \/
  	(exists f, l = Inj f /\ pq_app_aux tus tvs (pq_env f pt vars) (nil, Inj f) (a :: ats) = (xs, e)).
  Proof.
    destruct l; simpl in *; inv_all; subst; try (left; split; reflexivity).
    right. exists i. firstorder.
Qed.
  (*
  Lemma PQR_app_inj pt vars t pq_env l xs l_res tus tvs 
    (H : forall f, l = Inj f -> PQR pt vars t l (pq_app pq_env l l_res xs tus tvs) tus tvs) :
  	PQR pt vars t l (pq_app pq_env l l_res xs tus tvs) tus tvs.
  Proof.
    destruct l; try (clear H; unfold PQR, TD, Teval, add_quant; simpl; forward; destruct vars; forward; inv_all; subst; destruct pt; reflexivity).
    eapply H. reflexivity.
  Qed.
*)
  Lemma PQR_app_nil t pq_env l l_res tus tvs :
  	PQR t l (pq_app pq_env l l_res nil tus tvs) tus tvs.
  Proof.
    unfold PQR, PQR_aux, TD, Teval, add_quant; intros.
    simpl. forward.
    rewrite pqapp_nil in H. inv_all; subst; simpl in *.
    destruct var, pt; forward; inv_all; subst; reflexivity.
  Qed.

 Lemma PQR_atomic vars pt t xs f tus tvs : PQR_aux vars pt t (xs, f) (add_quants pt t xs f) tus tvs.
 Proof.
   unfold PQR_aux, TD, Teval.
   forward. destruct vars; intros; reflexivity.
 Qed.

     Lemma lift_app (sym : Type) x y (f e : expr sym) :
     	lift x y (App f e) = App (lift x y f) (lift x y e).
     Proof.
       repeat rewrite lift_lift'; simpl; reflexivity.
     Qed.

 Lemma lift_apps (sym : Type) x y (f : expr sym) args :
 	lift x y (apps f args) = apps (lift x y f) (map (lift x y) args).
 Proof.
   generalize dependent f. induction args; intros.
   + simpl. reflexivity.
   + simpl. rewrite IHargs, lift_app; reflexivity.
 Qed.

       	  Lemma PQR_atom tus tvs vars pt xs t f g (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
       	    (Hg : typeof_expr tus tvs g = Some t)
       	    (Heq : forall df dg, exprD' tus tvs (add_quants pt t xs f) t = Some df -> exprD' tus tvs g t = Some dg -> forall us vs, df us vs -|- dg us vs) :
       	    PQR_aux vars pt t (xs, f) g tus tvs.
       	  Proof.
       	    unfold PQR_aux, TD, Teval.
       	    apply typeof_expr_exprD'_impl in Hg. destruct Hg.
        	    forward; inv_all; subst.
       	    destruct vars; intros.
       	    rewrite Heq; reflexivity.
       	    rewrite <- Heq; reflexivity.
		  Qed.

    Lemma PQR_typeof vars pt t xs f g tus tvs (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
        (Hf : typeof_expr tus tvs (add_quants pt t xs f) = Some t)
     	(H : PQR_aux vars pt t (xs, f) g tus tvs) :
     	typeof_expr tus tvs g = Some t.
     Proof.
       	unfold PQR_aux, TD, Teval in H. 
       	apply typeof_expr_exprD'_impl in Hf.
        destruct Hf. forward. inv_all; subst.
        SearchAbout typeof_expr exprD'.
        eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof; eassumption.
Qed.

  
 Lemma exprD'_add_quants_cons_Some (pt : pull_type) (Ty : typ) (IL_Ty : ILogicOps (typD ts nil Ty))
        (_ : gs Ty = Some IL_Ty)
  : forall tus tvs tm a b x,
      exprD' tus tvs (add_quants pt Ty (a :: b) tm) Ty = Some x ->
      exists y,
        exprD' tus (a :: tvs) (add_quants pt Ty b tm) Ty = Some y /\
        forall us vs , x us vs -|- (pt_quant pt) _ _ (fun v => y us (HList.Hcons v vs)).
  Proof.
    simpl.
    intros.
    unfold add_quant in H0.
    destruct pt; simpl in *.
    + red_exprD. forward. subst.
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
    + red_exprD. forward. subst.
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
 
  Lemma forall_hlist_app (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty))
        (IL_Ty : ILogic (typD ts nil Ty))
  : forall xs ys (P : _ -> typD ts nil Ty),
      Forall v : HList.hlist (typD ts nil) (xs ++ ys), P v -|-
                                                         Forall v : HList.hlist (typD ts nil) xs,
    Forall v' : HList.hlist (typD ts nil) ys, P (HList.hlist_app v v').
  Proof.
    split.
    { do 2 (apply lforallR; intros).
      eapply lforallL; reflexivity. }
    { apply lforallR; intros.
      rewrite <- hlist_app_hlist_split with (h := x).
      do 2 (eapply lforallL); reflexivity. }
  Qed.

  Lemma pt_hlist_app (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty)) pt
        (IL_Ty : ILogic (typD ts nil Ty))
  : forall xs ys (P : _ -> typD ts nil Ty),
      (pt_quant pt) _ _ (fun v : HList.hlist (typD ts nil) (xs ++ ys) => P v) -|-
                                                         (pt_quant pt) _ _ (fun v : HList.hlist (typD ts nil) xs =>
      (pt_quant pt) _ _ (fun v' : HList.hlist (typD ts nil) ys => P (HList.hlist_app v v'))).
  Proof.
    destruct pt; simpl; [apply forall_hlist_app | apply exists_hlist_app]; assumption.
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

   Lemma lforall_iff_2 (Ty : Type) (ILO_Ty : ILogicOps Ty)
        (IL_Ty : ILogic Ty)
  : forall T U (P Q : T -> U -> Ty),
      (forall a b, P a b -|- Q a b) ->
      Forall x : T, Forall y : U, P x y -|-
                                    Forall y : U, Forall x : T, Q x y.
  Proof.
    split.
    { apply lforallR; intros.
      apply lforallR; intros.
      eapply lforallL; eauto.
      eapply lforallL; eauto. eapply H. }
    { apply lforallR; intros.
      apply lforallR; intros.
      eapply lforallL; eauto.
      eapply lforallL; eauto. eapply H. }
     Qed.
     
   Lemma pt_iff_2 (Ty : Type) (ILO_Ty : ILogicOps Ty) pt
        (IL_Ty : ILogic Ty)
  : forall T U (P Q : T -> U -> Ty),
      (forall a b, P a b -|- Q a b) ->
      (pt_quant pt) _ _  (fun x : T => (pt_quant pt) _ _ (fun y : U => P x y)) -|-
                                    (pt_quant pt) _ _ (fun y : U => (pt_quant pt) _ _ (fun x : T => Q x y)).
   Proof.
     destruct pt; [apply lforall_iff_2 | apply lexists_iff_2]; apply _.
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
 
   Lemma exprD'_add_quants_rev_Some (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty)) pt
        (_ : gs Ty = Some ILO_Ty) :
    forall tus xs tvs tm dtm,
      exprD' tus (rev xs ++ tvs) tm Ty = Some dtm ->
      exists dtm',
        exprD' tus tvs (add_quants pt Ty xs tm) Ty = Some dtm' /\
        forall us vs, dtm' us vs -|- (pt_quant pt) _ _ (fun vs' => dtm us (HList.hlist_app vs' vs)).
  Proof.
    induction xs; simpl; intros.
    + exists dtm. split; [assumption|].
      intros. split; destruct pt; simpl.
      * apply lforallR; intros. rewrite (hlist_eta x). simpl. reflexivity.
      * apply lexistsR with Hnil. simpl. reflexivity.
      * apply lforallL with Hnil; simpl; reflexivity.
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
      { destruct H2. destruct pt; simpl in *;
        unfold add_quant; simpl.
	    + red_exprD.
	        rewrite H.
	        red_exprD.
	        rewrite H.
	        red_exprD.
	        rewrite H2. eexists; split; eauto.
	        simpl.
	        intros.
	        split.
	         { apply lforallR; intros.
	          rewrite <- (hlist_app_hlist_split _ _ x0).
	          apply (lforallL (hlist_hd (snd (hlist_split (rev xs) (a :: nil) x0)))).
	          rewrite H3.
	          apply (lforallL (fst (hlist_split (rev xs) (a :: nil) x0))).
	          rewrite hlist_app_assoc; eauto with typeclass_instances.
	          rewrite (hlist_eta (snd (hlist_split (rev xs) (a :: nil) x0))).
	          simpl.
	          rewrite (hlist_eta (hlist_tl (snd (hlist_split (rev xs) (a :: nil) x0)))).
	          simpl.
	          match goal with
	            | |- _ ?X |-- _ match _ with eq_refl => ?Y end =>
	              change Y with X; generalize X
	          end.
	          generalize (app_ass_trans (rev xs) (a :: nil) tvs).
	          generalize H1. simpl. rewrite <- H1.
	          uip_all. reflexivity. } 
	        { apply lforallR; intros.
	          specialize (H3 us (Hcons x0 vs)).
	          rewrite H3.
	          apply lforallR; intros.
	          eapply (lforallL (hlist_app x1 (Hcons x0 Hnil))).
	          change (Hcons x0 vs) with (hlist_app (Hcons x0 Hnil) vs).
	          rewrite hlist_app_assoc; eauto with typeclass_instances.
	          match goal with
	            | |- _ match _ with eq_refl => ?X end |-- _ ?Y =>
	              change Y with X; generalize X
	          end.
	          generalize (app_ass_trans (rev xs) (a :: nil) tvs).
	          generalize H1. simpl. rewrite <- H1.
	          uip_all. reflexivity. }
	    + red_exprD.
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
    de us (hlist_app hxs (hlist_app hys hzs)) -|- df us (hlist_app hxs hzs).
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

  Lemma exprD'_add_quants_app_Some (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty)) pt
        (_ : gs Ty = Some ILO_Ty)
  : forall tus a tvs tm b x,
      exprD' tus tvs (add_quants pt Ty (a ++ b) tm) Ty = Some x ->
      exists y,
        exprD' tus (rev a ++ tvs) (add_quants pt Ty b tm) Ty = Some y /\
        forall us g, x us g -|- (pt_quant pt) _ _ (fun v => y us (HList.hlist_app v g)).
  Proof.
    induction a.
    { simpl.
      intros. eexists; split; eauto.
      intros.
      destruct pt; split; simpl in *.
      { apply lforallR; intros; rewrite (hlist_eta x0); reflexivity. }
      { apply lforallL with Hnil; reflexivity. }
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
                x us g -|- (pt_quant pt) _ _ (fun v : HList.hlist (typD ts nil) (a :: nil) => x0 us (HList.hlist_app v g))).
      { intros. specialize (H1 us g).
        rewrite H1.
        destruct pt; split; simpl.
        { apply lforallR; intros.
          apply lforallL with (hlist_hd x2).
          rewrite (hlist_eta x2).
          rewrite (hlist_eta (hlist_tl x2)). reflexivity. }
        { apply lforallR; intros.
          apply lforallL with (Hcons x2 Hnil); reflexivity. }
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
        reflexivity. (* eta *) }
      { intros.
        rewrite H4.
        rewrite pt_hlist_app; [|apply _].
        setoid_rewrite H3. 
        eapply pt_iff_2; [apply _|].
        intros.
        rewrite HList.hlist_app_assoc; [|apply _].
        uip_all. reflexivity. } }
  Qed.

  Lemma exprD'_add_quants_all_Some (Ty : typ) (ILO_Ty : ILogicOps (typD ts nil Ty)) pt
        (_ : gs Ty = Some ILO_Ty)
  : forall tus a tvs tm x,
      exprD' tus tvs (add_quants pt Ty a tm) Ty = Some x ->
      exists y,
        exprD' tus (rev a ++ tvs) tm Ty = Some y /\
        forall us g, x us g -|- (pt_quant pt) _ _ (fun v => y us (HList.hlist_app v g)).
  Proof.
    intros.
    rewrite <- (app_nil_r a) in H0.
    apply exprD'_add_quants_app_Some in H0; eauto.
  Qed.
 
     
    			  
    
   
   

 
  Lemma Happ pq_env
  : forall tus tvs l (l_res : T) rs t ts,
      typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
      let ft := fold_right tyArr t ts in
      PQR ft l (l_res tus tvs) tus tvs ->
      Forall2 (fun t x =>
                    typeof_expr tus tvs (fst x) = Some t
                 /\ PQR t (fst x) (snd x tus tvs) tus tvs)
              ts rs ->
      PQR t (apps l (map fst rs)) (pq_app pq_env l l_res rs tus tvs) tus tvs.
   Proof.
     intros.
     intros vars pt. simpl.
     assert (exists ILOps, (gs t) = Some ILOps) by admit. destruct H2.
     assert (exists f, l = Inj f) by admit. destruct H3 as [f H3]. subst.
     unfold pq_app.
     specialize (H0 vars pt). 
     assert (typeof_expr tus tvs (Inj f) = Some ft).
     clear H0. generalize dependent (Inj f). generalize dependent ts0.
     induction rs; simpl in *; intros.
	 inversion H1. simpl. apply H.
	 inversion H1; subst. simpl.
	 specialize (IHrs _ H6 _ H).
	 destruct H5 as [H5 _].
	 SearchAbout typeof_expr.
	 simpl in *. forward; inv_all; subst. simpl in *.
	 f_equal.
	 SearchAbout type_of_apply.
	 unfold type_of_apply in IHrs.
	 destruct t0; try congruence.
	 forward.
	 (*
	 Lemma exprD'_pull_empty tus tvs pt xs t f e df (ILOps : ILogicOps (typD ts nil t)) (IL : ILogic (typD ts nil t)) te
	   (He : typeof_expr tus tvs e = Some te)
	   (Hf : typeof_expr tus (rev xs ++ tvs) f = Some (tyArr te t))
	   (H : exprD' tus tvs (add_quants pt t xs (App f (lift 0 (length xs) e))) t = Some df) :
	   exists df', exprD' tus tvs (App (add_quants pt (tyArr te t) xs f) e) t = Some df' /\ forall us vs, df us vs -|- df' us vs.
	 Proof.
	   apply exprD'_add_quants_all_Some in H.
	   destruct H as [de [H1 H2]].
	   red_exprD; forward; inv_all; simpl in *. clear H7. revert H2. subst. intros.
	 Lemma add_quants_typeof_expr tus tvs xs f pt t (ILOps : ILogicOps (typD ts nil t)) (HIL : gs t = Some ILOps) :
	 	typeof_expr tus (rev xs ++ tvs) f = Some t <-> typeof_expr tus tvs (add_quants pt t xs f) = Some t.
	 Proof.
	   generalize dependent tvs. generalize dependent f.
	   induction xs; intros.
	   + simpl in *; reflexivity.
	   + simpl in *. rewrite <- app_assoc. simpl in *.
	     rewrite IHxs; destruct pt; simpl in *; forward; inv_all; subst; simpl; forward.
	 Qed.
	   assert (gs (tyArr te t) = Some (@ILFun_Ops (typD ts nil te) (typD ts nil t) ILOps)) by admit.
	   rewrite add_quants_typeof_expr with (pt := pt) in H0; [|eassumption].
	   setoid_rewrite H0.
	   pose proof (@exprD'_add_quants_rev_Some (tyArr te t)).
	   specialize (H4 (@ILFun_Ops (typD ts nil te) (typD ts nil t) ILOps) pt H tus xs tvs _ _ H1).
	   destruct H4 as [? [? ?]].
	   rewrite H4.
	   rewrite typ_cast_typ_refl.
	   pose proof (exprD'_lift RSym_sym tus nil (rev xs) tvs e te).
	   simpl in H6. rewrite rev_length in H6. forward.
	   eexists.
	   split. reflexivity. intros. rewrite H2.
	   inv_all; subst.
	   
	   inv_all; subst.
	   rewrite <- H8.
	    rewrite H5.
	   rewrite H3 in H6.
	   simpl in H6. forward.
	   edestruct H as [? ?].
	   edestruct H5.
	   erewrite H6.
	   destruct H as [? [? ?]].
	   Check ILFun_Ops.
	   apply exprD'_add_quants_rev_Some in H1.
	 apply add_quants_typeof_expr in H3.
	     simpl. forward. destruct H2; [congruence|].
	     
	    rewrite <- app_assoc. simpl.
	     destruct pt; simpl. 
	     forward; inv_all; subst.
	     split; intros. 
	     rewrite <- IHxs.
	     rewrite <- IHxs.
	     rewrite H.
	     forward; inv_all; subst.
	     simpl.
	     forward.
	     rewrite <- IHxs in H1. rewrite H1.
	     rewrite IHxs. rewrite <- IHxs in H1.
	     simpl. forward. inv_all; subst.
	     destruct H2; [congruence|].
	     rewrite <- IHxs. rewrite H1. c
	   rewrite IHxs.
	     destruct pt. simpl. forward; simpl in *. inv_all; subst.
	     remember (typ_eqb a a). destruct b.
	     simpl in *. unfold add_quants in H1. simpl in H1. simpl in *.
	     unfold add_quant in H1. simpl in *.
	     SearchAbout typ_eqb.
	     rewrite refl_typ_eqb.
	     inv_all; subst. 
	     unfold type_of_apply.
	   simpl in *; intros. subst.
	   pose proof (exprD'_lift RSym_sym tus nil (rev xs) tvs).
	   simpl in H. rewrite rev_length in H. forward.
	   revert de H1 H2.
	   replace (rev xs ++ tvs) with (nil ++ rev xs ++ tvs) by reflexivity.
	   red_exprD.
	   admit.
    Qed.
    (*
	   generalize dependent tvs; generalize dependent e; induction xs; intros.
	   + simpl in *. exists df. split; [|reflexivity].
	     destruct pt; simpl in *; assumption.
	   + simpl in *.
	     destruct pt.
	     unfold add_quant in *. simpl in *.
	     red_exprD; forward; simpl in *; inv_all. clear H7. revert H4. subst. intros.
	     red_exprD; forward; simpl in *; inv_all; subst.
	     red_exprD; forward; simpl in *; inv_all; subst.
         red_exprD; forward; simpl in *; inv_all; subst.
         replace (S (length xs)) with (length xs + 1) in H2 by omega.
         rewrite <- lift_lift', <- lift_lift in H2.
         rewrite <- app_assoc in Hf. simpl in Hf.
         assert (typeof_expr tus (nil++(a::nil)++tvs) (lift (length (@nil typ)) (length (a::nil)) e) = Some te).
         rewrite typeof_expr_lift. simpl. assumption.
         simpl in *. rewrite <- lift_lift' in H0.
         specialize (IHxs _ _ _ H0 Hf H2).
         destruct IHxs as [df [H4 H5]].
         Check HList.hlist_tl.
         exists (fun us vs => Forall x : typD ts nil a, df us (HList.Hcons x vs)).
         red_exprD; forward; simpl in *; inv_all; subst.
         assert (typ_eqb t (tyArr t2 t) = true). admit. forward.
         red_exprD; forward; simpl in *; inv_all; revert H1. subst.
         red_exprD; forward; simpl in *; inv_all; subst.
         forward.
         red_exprD; forward; simpl in *; inv_all; subst.
         assert (typ_eqb t (tyArr t2 t) = false) by admit.
         forward.
         *)
     *)

     Lemma Happ_aux tus tvs pt vars f rs t modes xs typs (ILOps : ILogicOps (typD ts nil t)) (IL : ILogic (typD ts nil t)) (Hgs : gs t = Some ILOps)
        (Hf : typeof_expr tus (rev xs ++ tvs) f = Some (fold_right tyArr t typs))
        (Hrs : Forall2
		       (fun (t : typ) (x : expr ilfunc * (tenv typ -> tenv typ -> TT)) =>
		        typeof_expr tus tvs (fst x) = Some t /\
		        PQR t (fst x) (snd x tus tvs) tus tvs) typs rs)
        (Henv : @valid_env tus tvs xs pt vars t ILOps typs f modes) :
     	PQR_aux vars pt t (pq_app_aux tus tvs modes (xs, f) rs)
     	                  (apps (add_quants pt (fold_right tyArr t typs) xs f) (map fst rs)) tus tvs.
     Proof.
        generalize dependent typs. generalize dependent f.
       	induction rs; intros.
       	+ admit.
       	+ destruct typs; [inversion Hrs|].
       	  destruct modes; [admit|].
       	  inversion Hrs; clear Hrs; subst. destruct H2.
       	  destruct o; simpl. destruct p, a; simpl.
       	  admit. destruct a. simpl.
       	    
     Lemma PQR_aux_rewrite tus tvs e1 e2 t vars pt e3 (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps) (IL : ILogic (typD ts nil t))
        (H : forall de2, exprD' tus tvs e2 t = Some de2 -> exists de3, exprD' tus tvs e3 t = Some de3 /\ forall us vs, de2 us vs -|- de3 us vs)
     	(He2 : PQR_aux vars pt t e1 e2 tus tvs) :
     	PQR_aux vars pt t e1 e3 tus tvs.
     Proof.
       	unfold PQR_aux, TD, Teval in *.
       	forward; inv_all; subst.
       	specialize (H2 t1 eq_refl).
       	destruct H2. destruct H0.
       	forward; inv_all; subst.
       	destruct vars; intros.
       	+ rewrite He2, H2; reflexivity.
       	+ rewrite <- He2, H2; reflexivity.
     Qed.
       
     
       
     Lemma apps_rewrite tus tvs e1 e2 rs t dea1 (ILOps : ILogicOps (typD ts nil t))
        (He: forall ts de1, exprD' tus tvs e1 (fold_right tyArr t ts) = Some de1 -> 
        	                exists de2, exprD' tus tvs e2 (fold_right tyArr t ts) = Some de2 /\ forall us vs, de1 us vs -|- de2 us vs)
        (H : exprD' tus tvs (apps e1 rs) t = Some dea1) :
        exists dea2, exprD' tus tvs (apps e2 rs) t = Some dea2 /\ forall us vs, dea1 us vs -|- dea2 us vs.
     Proof.
       generalize dependent e1; generalize dependent e2; induction rs; simpl in *; intros.
       + specialize (He nil). simpl in *. apply He. apply H.
       + eapply IHrs; [|eassumption].
         intros.
         red_exprD; forward; inv_all; subst. clear IHrs.
         specialize (He (t1::ts0) _ H2).
         destruct He as [de2 [He1 He2]].
         simpl in *.
         SearchAbout exprD' typeof_expr.
         assert (typeof_expr tus tvs e2 = Some (tyArr t1 (fold_right tyArr t ts0))) by admit.
         forward; inv_all; subst.
         forward; inv_all; subst.
         rewrite typ_cast_typ_refl.
         eexists. split; [reflexivity|]. intros.
         simpl. 
         assert (@lequiv (typD ts nil (fold_right tyArr t (t1::ts0))) _ (t3 us vs) (de2 us vs)). apply He2.
         Local Transparent ILFun_Ops.
         split; apply H5.
    Qed.

    apply (PQR_aux_rewrite (e2 := apps (add_quants pt (fold_right tyArr t typs) xs (App f (lift 0 (length xs) e))) (map fst rs))).
    assumption.
    assumption.
    intros.
    apply (apps_rewrite (e1 := add_quants pt (fold_right tyArr t typs) xs (App f (lift 0 (length xs) e)))); [|assumption].
    intros.
    replace xs with (xs ++ nil) in H2.
    Check exprD'_add_quants_app_Some.
    assert (gs (fold_right tyArr t typs) = Some _) by admit.
    assert (ts0 = typs) by admit; subst. simpl in *.
    pose proof (exprD'_add_quants_app_Some H3 H2).
    simpl in H5.
    destruct H5 as [de3 [Hde3 Heq]].
    red_exprD; forward; inv_all; revert Heq; subst; intros.
    
     Lemma add_quants_typeof_expr tus tvs xs f pt t (ILOps : ILogicOps (typD ts nil t)) (HIL : gs t = Some ILOps) :
	 	typeof_expr tus (rev xs ++ tvs) f = Some t <-> typeof_expr tus tvs (add_quants pt t xs f) = Some t.
	 Proof.
	   generalize dependent tvs. generalize dependent f.
	   induction xs; intros.
	   + simpl in *; reflexivity.
	   + simpl in *. rewrite <- app_assoc. simpl in *.
	     rewrite IHxs; destruct pt; simpl in *; forward; inv_all; subst; simpl; forward.
	 Qed.
    assert (gs ((fold_right tyArr t (t0::typs))) = Some _) by admit. simpl in H5.
    rewrite add_quants_typeof_expr with (pt := pt) in H6; [|eassumption].
    forward. inv_all; subst.
    revert Heq. uip_all'. intros.
    pose proof (@exprD'_add_quants_rev_Some (tyArr t0 (fold_right tyArr t typs)) _ pt H5 tus xs tvs _ _ H7).
    destruct H6 as [? [? ?]].
    forward; inv_all; subst. 
    rewrite typ_cast_typ_refl. 
    pose proof exprD'_lift RSym_sym tus nil (rev xs) tvs e t0.
    simpl in H11. rewrite rev_length in H11. rewrite app_nil_r in H8.
    forward.
    eexists. split; [reflexivity|].
    intros. simpl. inv_all; subst; rewrite Heq. 
    inv_all; subst. 
    unfold valid_env in Henv.
    specialize (Henv _ H7 us vs).
    apply valid_arg_none_inv in Henv.
    destruct Henv.
    specialize (H10 us vs).
    transitivity (((pt_quant pt (ILFun_Ops (typD ts nil t0)) (fun vs' : hlist (typD ts nil) (rev xs) => t5 us (hlist_app vs' vs)))) (t3 us vs)).
    Focus 2.
    destruct H10.
    split. apply H15. apply H10.
    destruct vars; simpl in *.
    admit.
    split.
    specialize (H13 us HList.Hnil).
    destruct pt; simpl in *.
    adm
    admit.
    destruct pt; simpl in *.
    apply lforallR. intro. apply lforallL with x0.
    specialize (H11 (fun v => t6 us (hlist_app v vs))).
    etransitivity; [|eapply H11].
    etransitivity.
    destruct vars. simpl in *.
    Check @existT.
    assert ( (fun x : hlist (typD ts nil) (rev xs) => t5 us (hlist_app x vs)) = f0) by admit.
    change (fun x : hlist (typD ts nil) (rev xs) => t5 us (hlist_app x vs)) with f0.
    setoid_rewrite H11 at 1.
    inversion H16.
    eapply f_equal in H16.
    specialize (H10 (t3 us vs)). .
    Print existT.
    inversion H16.
    Check existT.
    setoid_rewrite <- H6.
    einversion Henv. 
    setoid_rewrite <- H10.
    destruct Henv as [? [_ Henv]].
    specialize (Henv us vs). inversion Henv. subst.
    inv_all; subst.
    specialize (H13 us HList.Hnil).
    rewrite UIP_refl in Heq.
    forward.
    pose proof(@add_quants_typeof_expr tus tvs _ _ _ (fold_right tyArr t (x::l)) _ H5 ).
    assert (typeof_expr tus tvs (add_quants pt (tyArr x (fold_right tyArr t l)) xs f) = Some (tyArr x (fold_right tyArr t l))).
    
    rewrite add_quants_typeof_expr in H6. forward.
    Lemma exprD'_lift_arg
    	(H : exprD' tus (xs ++ ys ++ zs) (App f (lift (length xs) (length ys) e)) t = Some de
    	exrpD' tus (xs ++ ys ++ zs) (App f
    
    apply exprD'_add_quants_app_Some in H2. 
    apply (apps_rewrite (e2 := App (add_quants pt (tyArr x (fold_right tyArr t l)) xs f) e)) in H1.
    apply apps_rewrite in H1.
    apply IHrs.    
    admit.
    admit. apply H3.
    destruct vars. simpl.
    
    

         destruct H5; split; [apply H5 | apply H6].
         Local Transparent ILFun_Ops.
         apply H5.
         unfold lentails in H5. simpl in H5.
         Transparent ILFun_Ops.
         simpl in *.
         assert (t3 us vs |-- de2 us vs).
         apply f_equal.
         exists t3.
         specialize
       	 inv_all; subst.
       	       	    simpl.
       	    unfold PQR_aux, TD, Teval.
       	    forward; inv_all; subst.
       	    forward.
       	    
       	    
Lemma test : 
       	    unfold PQR_aux, TD, Teval.
       	    forward. inv_all; subst.
 			simpl in *.
       	    specialize (IHrs _ Hf).
       	+ simpl.
       	  inversion Hrs; simpl in *; revert Hf Heq. revert ft. subst; simpl; intros; destruct modes.
       	  * eapply PQR_atom; try assumption.
       	  * destruct o.
       	    - destruct p. eapply PQR_atom; assumption.
       	    - eapply PQR_atom; assumption.
       + destruct a; simpl in *; inversion Hrs; revert Heq Hf; revert ft; subst; simpl; intros; clear Hrs.
         destruct modes.
         * unfold PQR_aux, TD, Teval. simpl.
         
         
         eapply IHrs; try eassumption.   
           destruct H2; simpl in *. forward; inv_all; subst. forward.
           replace (length xs) with (length (rev xs)) by admit.
           replace (rev xs ++ tvs) with (nil ++ rev xs ++ tvs) by reflexivity.
           rewrite typeof_expr_lift. simpl. forward.
           intros.
           Print PQR_aux.
           apply Heq.
      	   pose proof (@exprD'_pull_empty tus tvs).     
		   intros.
		   red_exprD; forward; inv_all; subst.
		   specialize (Heq df).
		   apply Heq.           
       	  * inversion Hrs; simpl in *; revert ILOpsf Hft Heq. revert ft. subst; simpl; intros.
       	    eapply PQR_atom; try assumption. 
       	  * destruct o. destruct p. eapply PQR_atom; eassumption. eapply PQR_atom; eassumption.
       	+ simpl. 
       	  destruct modes.
       	  * destruct a. simpl. inversion Hrs; subst.
       	    eapply IHrs. apply H3. simpl in *. apply Htg.
       	    intros. red_exprD. forward. inv_all; subst.
       	    apply Heq.
			destruct H2.
			
       	    apply ve_nil. intros. reflexivity.
       	  * destruct o.
       	    - destruct p, a; simpl in *. forward.
       	      inversion Hrs; subst. clear Hrs. simpl in *. destruct H3.
       	      specialize (H1 v p).
       	      
     Lemma PQR_var t pt tus tvs e f g (ILOps : ILogicOps (typD ts nil t)) (_ : (gs t = Some ILOps))
        (Hf : exists df, exprD' tus tvs f t = Some df)
     	(Hef : forall de df, exprD' tus tvs e t = Some de -> exprD' tus tvs f t = Some df -> forall us vs, de us vs |-- df us vs) 
     	(HPQR : PQR_aux CoVariant pt t g e tus tvs) :
     	PQR_aux CoVariant pt t g f tus tvs.
     Proof.
       destruct Hf.
       unfold PQR_aux, TD, Teval in *. forward; inv_all; subst.
       rewrite HPQR, Hef; reflexivity. 
     Qed.
       
     destruct vars.
     eapply PQR_var.
     admit.
     SearchAbout typeof_expr exprD'.
     clear IHrs. clear H4 H1 Henv H H0.
     generalize dependent (map fst rs). generalize dependent tvs. generalize dependent f; generalize dependent e; induction xs; intros. 
     destruct pt. simpl.
     apply typeof_expr_exprD'_impl. assumption.
     apply typeof_expr_exprD'_impl. assumption.
     simpl in *.
     
     

     replace (S (length xs)) with (length xs + 1) in Ht by omega.
     rewrite <- app_assoc in Ht; simpl.       
     rewrite <- lift_lift' in Ht.
     rewrite <- lift_lift in Ht.
     rewrite lift_apps in Ht.
     
       
     rewrite lift_app in Ht. simpl in Ht.
     destruct (IHxs _ _ _ _ Ht); clear IHxs.
     destruct pt.
     exists (fun us vs => Forall x, x0 us (HList.Hcons x vs)).
	 rewrite <- lift_lift'.
	 replace (S (length xs)) with (length xs + 1) by omega.
	 rewrite <- lift_lift, lift_apps, lift_app.
	 simpl. red_exprD; forward; inv_all; subst.
     assert (gs t = Some ILOps) by admit.
     forward; inv_all; subst.
     red_exprD. forward. rewrite typ_cast_typ_refl.
     inv_all; subst. reflexivity.
     admit. 
     Focus 2.
     rewrite lift_lift. 
     replace (length l + length xs) with (length xs + length l) by omega.
     rewrite lift_lift_1. simpl.
     rewrite <- lift_app.
     apply IHrs.
     inv_all; subst.
     forward.
     Check exprD'_lift.
     remember ( exprD' tus (a :: tvs)
      (add_forall xs t
         (lift' 0 (S (length xs)) (apps (App f e) (map fst rs)))) t).
     destruct o.
	 admit.
     red_exprD.
     exists (fun us vs => Forall x, x0 us (HList.Hcons x vs)).
     red_exprD; forward; inv_all; subst.
     assert (gs t = Some (ILOps)) by admit.
     forward. inv_all; subst.
     red_exprD. forward. rewrite typ_cast_typ_refl.
     inv_all; subst. reflexivity.
     admit. intros.
     Focus 2. 
     
     
     specialize (IHrs (l ++ xs) _ H4).
     apply IHrs. 
     rewrite rev_app_distr. rewrite <- app_assoc.
     assert (App f (lift (length l) (length xs) e0) = lift (length l) (length xs) (App f e0)).
     destruct (length xs). simpl. reflexivity.
     simpl. 
     rewrite typeof_expr_lift.
     SearchAbout List.rev List.app.
     f_equal. 
     Require Import FunctionalExtensionality.
     apply functional_extensionality.
     intros.
     apply functional_extensionality; intros.
     reflexivity.
     simpl in *.
     Focus 3.
     eapply IHrs.
     eapply H4.
     Focus 2.
     inversion Henv; subst.
     eapply H7.
     eapply H7.
     rewrite <- app_assoc.
     SearchAbout lift typeof_expr.
     SearchAbout typeof_expr apps.
     SearchAbout typeof_expr apps.
     SearchAbout type_of_applys.
     SearchAbout apps lift.
     admit.
     Focus 2.
     intros.
     erewrite type_of_applys_typeof.
     simpl.
     Print type_of_applys.
     SearchAbout type_of_applys.
     Focus 2.
     rewrite typeof_expr_lift.
     rewrite typeof_expr_lift.
     SearchAbout lift typeof_expr.
     SearchAbout List.rev List.app.
     rewrite rev_app_distr. rewrite <- app_assoc.
     Focus 2.intros.
     induction xs. simpl.
     unfold add_quant. destruct pt. simpl. forward.
     SearchAbout exprD' apps.
     rewrite exprD'_apps.
     Focus 23 	      
     Lemma PQR_covar t pt tus tvs e f g de df (ILOps : ILogicOps (typD ts nil t)) (_ : (gs t = Some ILOps))
     	(He : exprD' tus tvs e t = Some de)
     	(Hf : exprD' tus tvs f t = Some df) 
     	(Hef : forall us vs, de us vs |-- df us vs) 
     	(HPQR : He : exprD' tus tvs e t = Some de -> exprD' tus tvs f t = Some df PQR_aux ContraVariant pt t g f tus tvs) :
     	PQR_aux ContraVariant pt t g e tus tvs.
     Proof.
       unfold PQR_aux, TD, Teval in *. forward; inv_all; subst.
       rewrite <- HPQR, Hef; reflexivity. 
     Qed.

     Lemma add_quant pt xs t (apps (App f e) args)
       	      
       	    - destruct a. apply IHrs. apply Ht.
       	      inversion Henv. subst. apply H0.
     Qed.
     Lemma PQR_atomic vars pt t xs f tus tvs : PQR_aux vars pt t (xs, f) (add_quant pt xs t f) tus tvs.
     Proof.
       unfold PQR_aux, TD, Teval.
       forward. destruct vars; intros; reflexivity.
     Qed.
     
     induction rs. simpl.
     apply PQR_app_nil. simpl.
     assert (exists ILOps, (gs t) = Some ILOps) by admit. destruct H2.
     assert (exists f, l = Inj f) by admit. destruct H3 as [f H3]. subst.
     destruct a. simpl.
     unfold pq_app.
     
     
     Lemma Happ_aux
     
     unfold PQR; intros. simpl.
     unfold TD. simpl.
     simpl.
     unfold pq_app. simpl. destruct a.
     unfold PQR; intros. simpl. unfold TD. simpl. unfold Teval. simpl.
     unfold PQR, TD, Teval.
     forward; inv_all; subst.
     assert (valid_env tus tvs (Inj f) (pq_env f pt vars)) by admit.
     
     Lemma Happ_aux tus tvs pt vars l f rs t e de modes xs (ILOps : ILogicOps (typD ts nil t)) (IL : ILogic (typD ts nil t))
        (H : exprD' tus tvs
    	     match pt with
       		 | PAll => add_forall l t e
        	 | PExists => add_exists l t e
       	     end t = Some de) 
       	(Htyp : typeof_expr tus tvs (apps f (map fst rs)) = Some t)
       	(Henv : valid_env tus tvs f modes)
       	(Happ : pq_app_aux tus tvs modes (xs, f) rs = (l, e)) : 
       	     match pt with
       	     | PAll => match exprD' tus tvs (add_forall xs t (apps f (map fst rs))) t with
				| Some q =>
				    match vars with
				    | CoVariant =>
				        forall (us : HList.hlist (typD ts nil) tus)
				          (vs : HList.hlist (typD ts nil) tvs), de us vs |-- q us vs
				    | ContraVariant =>
				        forall (us : HList.hlist (typD ts nil) tus)
				          (vs : HList.hlist (typD ts nil) tvs), q us vs |-- de us vs
				    end
				| None => False
				end
		    | PExists => match exprD' tus tvs (add_exists xs t (apps f (map fst rs))) t with
				| Some q =>
				    match vars with
				    | CoVariant =>
				        forall (us : HList.hlist (typD ts nil) tus)
				          (vs : HList.hlist (typD ts nil) tvs), de us vs |-- q us vs
				    | ContraVariant =>
				        forall (us : HList.hlist (typD ts nil) tus)
				          (vs : HList.hlist (typD ts nil) tvs), q us vs |-- de us vs
				    end
				| None => False
				end
		    end.
     Proof.
       generalize dependent f; generalize dependent l; generalize dependent modes; generalize dependent pt; generalize dependent vars. generalize dependent xs.
       induction rs; intros.
       + simpl in *.
         destruct modes.
         * simpl in *. inv_all. subst.
           destruct pt, vars; forward; inv_all; subst; reflexivity.
         * simpl in *. destruct o. destruct p; inv_all; subst;
           destruct pt, vars; forward; inv_all; subst; reflexivity.
           inv_all; subst. destruct pt, vars; forward; inv_all; subst; reflexivity.
       + simpl.
         destruct a. simpl in *.
         destruct modes; simpl in *.
         * inv_all; subst; simpl in *. 
           specialize (IHrs xs vars pt).
           eapply IHrs.
           apply H. apply Htyp.
           apply ve_nil; intros; reflexivity.
           apply Happ.
         * destruct o. 
           - destruct p.
             inversion Henv; subst.
             eapply IHrs.
             eapply H.
             apply Htyp.
             apply H4.
             
             apply Happ.
             inversion Henv. subst.
             simpl in *.
           - eapply IHrs.
             apply H. apply Htyp.
             Focus 2. apply Happ.
             inversion Henv. subst. apply H1.
   Qed.
             eapply ve_none; intros. reflexivity.
         destruct p. simpl in *.
           destruct pt, vars; forward; inv_all; subst.
           eapply IHrs.
         eapply IHrs.
         apply H.
         apply Htyp.
         admit.
         destruct modes.
         simpl in *.
         apply Happ.
         destruct modes.
         simpl.
           inversion Henv. forward.
    Qed.
    
    eapply Happ_aux.
    eassumption.
    eassumption.
    eassumption.
     *)
     (*
     induction rs.
     + simpl in *.
       destruct (pq_env f pt vars). simpl in *. inv_all; subst.
       destruct vars, pt; simpl in *; forward; inv_all; subst; reflexivity.
       simpl in *. destruct o. destruct p. inv_all; subst.
       destruct vars, pt; simpl in *; forward; inv_all; subst; reflexivity.
       inv_all; subst.
       destruct vars, pt; simpl in *; forward; inv_all; subst; reflexivity.
     + simpl.
       apply IHrs.
       destruct (pq_env f CoVariant 
     generalize dependent ts0. generalize dependent t. generalize dependent l.
     induction rs; simpl in *.
     + intros; apply PQR_app_nil.
     + simpl in *; intros.
       simpl.
       destruct l.
       admit.
       admit.
       admit.
       rewrite typeof_expr_apps in H; [congruence|]. 
       simpl. forward.
       admit.
       
       SearchAbout typeof_expr App.
        
        
        forward. simpl.
       SearchAbout typeof_expr
       unfold type_of_apply. destruct t0; try reflexivity.
       simpl in *.
       cases (typ_eqb t0_1 t1).
       case (typ_eqb t0_1 t1).
       destruct a. simpl. forward.
       inversion H1; subst. clear H1.
       destruct a; simpl in *.
       destruct H6.
       specialize (IHrs _ _ H _ H2).
	   unfold pq_app. simpl.
       SearchAbout typeof_expr apps.
       Check type_of_applys_typeof.
       
       Lemma type_of_applys_typeofE  : forall (ts : types) (sym : Type) (RSym_sym : RSym (typD ts) sym)
      									      (tus tvs : tenv typ) (es : list (expr sym)) (e : expr sym) (t : typ),
          typeof_expr tus tvs e = Some t ->
          typeof_expr tus tvs (apps e es) = type_of_applys RSym_sym tus tvs t es
       
       erewrite type_of_applys_typeof in H.
       Focus 2.
       SearchAbout typeof_expr apps.
       
       Lemma typeof_expr_apps_App tus tvs f e rs t (H : typeof_expr tus tvs (apps (App f e) rs) = Some t) :
       	 exists te, typeof_expr tus tvs f = Some (tyArr te t) /\ typeof_expr tus tvs (apps e rs) = Some te.
       Proof.
         generalize dependent e.
         induction rs.
         + simpl in *. forward. unfold type_of_apply in H1. forward. inv_all; subst.
           exists t1. intuition.
         + simpl in *. intros.
           apply IHrs. simpl in *.
           exists (tyArr t1 t3), t1.
       Lemma PQR_typeof_expr pt vars t l f tus tvs IL (H : PQR pt vars t l f tus tvs) 
                             (HIL : gs t = Some IL) :
                             typeof_expr tus tvs l = Some t.
       Proof.
         unfold PQR, TD, Teval in H. forward.
         destruct vars, pt. inv_all; subst.
       
       
       simpl. forward.  
       inv_all; subst. forward.     
       simpl in H1.
       destruct H0.
       simpl in H1.
       unfold PQR, TD, Teval.
       simpl.
       rewrite exprD'_apps.
       forward.
       inv_all; subst.
       destruct a. simpl.
       SearchAbout apps_sem.
       simpl in *.
       
       red_exprD.
       unfold PQR, TD, Teval in IHrs.
       forward.
       Print apps_sem'.
       Check apps_sem.
       Print ExprD3.EXPR_DENOTE_core.exprD'.
       Print apps_sem.
       Print apply_sem.
       Check exprD_apps.
Qed.

       Lemma exprD'_apps : forall (ts : types) (sym : Type) (RSym_sym : RSym (typD ts) sym)
         (us vs : env (typD ts)) (es : list (expr sym)) (e : expr sym)
         (t : typ),
       exprD' (typeof_env us) (typeof_env vs) (apps e es) t = apps_sem RSym_sym us vs e es t.
       
       destruct a. simpl in *.
       unfold PQR, TD, Teval.
       Check
       forward. inv_all; subst.
       simpl in *.
       destruct pt, vars. forward. simpl in *.
       Print apps.
       
Check exprD_apps.

Check apps_sem.
       
       rewrite exprD_apps.
       SearchAbout apps.
       SearchAbout typeof_expr apps.
       erewrite type_of_applys_typeof in H.
       Focus 2. simpl. forward. forward. inv_all; subst. forward.
       simpl in H.
       unfold PQR, TD, Teval in *; simpl in *.
       simpl.
       inversion H2; subst; intros.
       simpl in *; clear H2. destruct H6.
       unfold PQR, TD, Teval. simpl.
       forward. inv_all; subst.
       SearchAbout typeof_expr.
       destruct vars. forward.
       destruct l. 
       red_exprD. simpl in H. forward. red_exprD.
       SearchAbout ExprDI.nth_error_get_hlist_nth.
       replace ft with t.
       apply ft.
       destruct l. 
       admit.
       red_exprD; forward; simpl in *.
       uip_all'.
       forward.
       admit.
       forward.
       forward.
       destruct pt, vars.
       red_exprD. simpl.
       simpl in *.
       admit.
       admit.
       forward.
       destruct vars, pt.
       rewrite ft in .
       forward; inv_all; subst.
       rewrite pqapp_nil in H3.
       inv_all; subst.
       destruct vars. 
       destruct pt. forward.
       red_exprD.
       progress forward.
       progress forward.
       forward; inv_all; subst.
       destruct vars; simpl in *.
       destruct vars. simpl in *.
       destruct pt, vars; simpl in *.
       inversion H1.
       apply Forall2_refl in H1.
       apply Forall2_ind.
       SearchAbout Forall2.
       forward; inv_all; subst.
       destruct pt, vars. simpl.
       forward.
       unfold pq_app in H3. destruct l.
       simpl in *. inv_all; subst. forward.
       forward. destruct vars.
       destruct vars. simpl in *.
       destruct pt. forward.
     
   Qed.

  Lemma add_quants_app tus tvs xs ys t p q d (IL : ILogicOps (typD ts nil t))
  	(H : exprD' tus tvs (add_quants (xs ++ ys) t (App (lift 0 (length ys) p) (lift (length ys) (length xs) q))) t = Some d) :
    exists tq dp dq,
      typeof_expr (typeof_env tus) (rev ys ++ tvs) q = Some tq /\
      exprD' tus tvs (add_quants xs (tyArr tq t) p) (tyArr tq t) = Some dp /\ exprD' tus tvs (add_quants ys tq q) tq = Some dq /\
      forall vs, d vs |-- (dp vs) (dq vs).
  Proof.


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