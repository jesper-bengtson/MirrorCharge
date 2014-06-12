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
Require Export ExtLib.Data.HList.

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

  Local Instance RSym_sym : SymI.RSym (typD ts) ilfunc := RSym_ilfunc funcs gs es.

 
  Inductive variance := CoVariant | ContraVariant.
  Inductive pull_type := PAll | PExists.
  
  Definition get_quant (pt : pull_type) :=
  	match pt with
  	  | PAll => ilf_forall
  	  | Pexists => ilf_exists
  	end.  

  Definition add_quant (pt : pull_type) (t : typ) (x : typ) (e : expr ilfunc) :=
    App (Inj ((get_quant pt) x t)) (Abs x e).

  Definition add_quants (pt : pull_type) (t : typ) (xs : list typ) (e : expr ilfunc) :=
    fold_right (fun x a => add_quant pt t x a) e xs.
    
 Definition add_quants' us vs (pt : pull_type) (xs : list typ) (e : expr ilfunc) :=
 	match typeof_expr us (rev xs ++ vs) e with
 	  | Some t => add_quants pt t xs e
 	  | None => e
 	end.
 
 Definition pt_quant (pt : pull_type) := 
 	match pt with
 	  | PExists => @lexists
 	  | PForall => @lforall
    end.
    
  Require Import Morphisms.

 Require Import Program.Basics.
  
  Definition var_entail (var : variance) (A : Type) (ILOps: ILogicOps A) :=
  	match var with
  	  | CoVariant => (@lentails A ILOps)
  	  | ContraVariant => (flip lentails)
    end.


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

  Global Instance var_entails_lequiv_m (vars : variance) :
    Proper (lequiv ==> lequiv ==> iff) (var_entail vars _).
  Proof.
    destruct vars; simpl; apply _.
  Qed.

  Global Instance var_entails_m (vars : variance) :
    Proper ((var_entail vars _) --> (var_entail vars _) ++> impl) (var_entail vars _).
  Proof.
	destruct vars; simpl; apply _.
  Qed.

  Global Instance var_entail_eq (vars : variance) : PreOrder (var_entail vars _).
  Proof.
	destruct vars; simpl; apply _.
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
  
  Definition modes := list (option (variance * pull_type)).

  Inductive valid_arg (pt : pull_type) (var : variance) (t : typ) (ILt : ILogicOps (typD ts nil t)) :
    forall (typs : list typ), (typD ts nil (fold_right tyArr t typs))  -> modes -> Prop :=
    | ve_nil typs f : @valid_arg pt var t ILt typs f nil
    | ve_none typs t' f ms : (forall a, @valid_arg pt var t _ typs (f a) ms) -> @valid_arg pt var t _ (t'::typs) f (None::ms)
    | ve_some typs t' f p v ms : 
                              (forall a, @valid_arg pt var t _ typs (f a) ms) ->
                              (forall a b (ILt' : ILogicOps (typD ts nil t')), gs t' = Some ILt' -> (var_entail v ILt') a b -> (var_entail var _) (f a) (f b)) ->
                              (forall T (a : T -> (typD ts nil t')) (ILt' : ILogicOps (typD ts nil t')), gs t' = Some ILt' ->  (var_entail var _) ((pt_quant pt) _ _ (fun x => f (a x))) (f ((pt_quant p) _ _ a))) ->
                              @valid_arg pt var t _ (t'::typs) f (Some (v, p)::ms).
  
  Lemma valid_arg_some_inv (pt pt' : pull_type) (var var' : variance) (t te : typ) (ILOps : ILogicOps (typD ts nil t))
    (typs : list typ) (f : typD ts nil te -> typD ts nil (fold_right tyArr t typs)) (ms : modes)  (ILt' : ILogicOps (typD ts nil te))
    (H : @valid_arg pt var t ILOps (te::typs) f ((Some (var', pt'))::ms)) :
                              (forall a, @valid_arg pt var t _ typs (f a) ms) /\
                              (forall a b (ILte : ILogicOps (typD ts nil te)), gs te = Some ILte -> (var_entail var' ILte) a b -> (var_entail var _) (f a) (f b)) /\
                              (forall T (a : T -> (typD ts nil te)) (ILte : ILogicOps (typD ts nil te)), gs te = Some ILte -> (var_entail var _) ((pt_quant pt) _ _ (fun x => f (a x))) (f ((pt_quant pt') _ _ a))).
  Proof.
    change (typD ts nil te -> typD ts nil (fold_right tyArr t typs)) with (typD ts nil (fold_right tyArr t (te::typs))) in f.
    inversion H. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4. subst.
    intuition.
  Qed.

  Lemma f_eq : forall t typs, typD ts nil (fold_right tyArr t typs) = fold_right (fun T A : Type => T -> A) (typD ts nil t) (map (typD ts nil) typs).
  Proof.
    induction typs.
    simpl. reflexivity.
    simpl. rewrite IHtyps. reflexivity.
  Qed.
      
  Definition valid_env (tus tvs : tenv typ) (pt : pull_type) (var : variance) (f : expr ilfunc) (ms : modes) :=
    forall t typs df (ILt : ILogicOps (typD ts nil t)), gs t = Some ILt -> exprD' tus tvs f (fold_right tyArr t typs) = Some df -> forall us vs, @valid_arg pt var t ILt typs (df us vs) ms. 

  Section valid_arg_test.
    Context {t : typ} `{IL : ILogic (typD ts nil t)}.
    
    Lemma test (H : gs t = Some ILOps) : @valid_arg PExists CoVariant t ILOps (t::t::nil) land (Some(CoVariant, PExists)::Some(CoVariant, PExists)::nil).
    Proof.
      eapply (@ve_some); intros; simpl in *.
      eapply (@ve_some); intros; simpl in *.
      
      apply ve_nil.
      rewrite H0 in H. inv_all; subst.
      rewrite H1. reflexivity.
      
      apply lexistsL; intro x.
      apply landR; [apply landL1; reflexivity|apply landL2].
      rewrite H0 in H; inv_all; subst.
      apply lexistsR with x. reflexivity.
      
      intros.
      simpl in *.
      Transparent ILFun_Ops.
      rewrite H0 in H. inv_all; subst.
      intros c. simpl. rewrite H1.
      reflexivity.
      simpl; intros.

	  apply lexistsL; intro x.
	  rewrite H0 in H; inv_all; subst.
	  apply landR. apply lexistsR with x.
	  apply landL1. reflexivity. apply landL2. reflexivity.      
   Qed.

  End valid_arg_test.
 
  Definition TT := variance -> pull_type -> list typ * modes * expr ilfunc.

  Fixpoint arity (t : typ) :=
    match t with
      | tyArr t t' => S (arity t')
      | _          => 0
    end.

  Fixpoint empty_modes (n : nat) : modes :=
    match n with 
      | 0   => nil
      | S n => None::(empty_modes n)
    end.
    
  Let T:Type := tenv typ -> tenv typ -> TT.
  Definition atomic (e : expr ilfunc) : T := fun tus tvs _ _ => (nil, nil, e).

  Definition pq_var (v : var) : T := atomic (Var v).
  Definition pq_uvar (u : uvar) : T := atomic (UVar u).
  Definition pq_inj (s : ilfunc) : T := atomic (Inj s).
  Definition pq_abs (x : typ) (e : expr ilfunc) (_ : T) : T :=
    atomic (Abs x e).
  
  Fixpoint pq_app_aux (us vs : tenv typ) (pt : pull_type) (f : list typ * modes * expr ilfunc) (args : list (expr ilfunc * T)) : list typ * modes * expr ilfunc :=
  match f, args with
    | (xs, Some (var, pt')::ms, f'), (e, t)::args' => 
      match t us vs var pt', typeof_expr us vs e with
        | (ys, _, a), Some t =>
	          match gs t with
	            | Some _ => pq_app_aux us vs pt (xs ++ ys, ms, App (lift 0 (length ys) f') (lift (length ys) (length xs) a)) args'
	            | None   => (nil, ms, apps (add_quants' us vs pt xs f') (map fst args))
	          end
        | _, None => (nil, ms, apps (add_quants' us vs pt xs f') (map fst args))
    end
    | (xs, None::ms, f'), (e, _)::args => pq_app_aux us vs pt (xs, ms, App f' (lift 0 (length xs) e)) args
    | (xs, ms, f'), _ => (nil, ms, apps (add_quants' us vs pt xs f') (map fst args))
  end.

  Definition pq_app (_ : expr ilfunc) (f : T) (args : list (expr ilfunc * T)) : T :=
    fun us vs var pt => pq_app_aux us vs pt (f us vs var pt) args.
  
   Definition pq_exists (t t_logic : typ) (f : expr ilfunc) (a : T) : T :=
    fun us vs vm pt =>
      match pt with
      	| PExists => match a us (t :: vs) vm pt with
      	               | (ts, ms, a) => (t::ts, ms, a)
      	             end
      	| _       => (nil, nil, App (Inj (ilf_exists t t_logic)) (Abs t f)) 
      	
      end.

  Definition Teval (pt : pull_type) (e : list typ * modes * expr ilfunc) (t : typ) :=
    match e with 
      | (xs, _, a) => add_quants pt t xs a
    end.
    
  Definition TD (pt : pull_type) (t : typ) (e : list typ * modes * expr ilfunc) (us vs : tenv typ) :=
    exprD' us vs (Teval pt e t) t.

  Definition PQR_aux var pt (t : typ) 
                     (arg : list typ * modes * expr ilfunc)
                     (e : expr ilfunc) (us vs : tenv typ) 
                      :=  
    match (TD pt t arg) us vs, exprD' us vs e t, gs t with
      | None, _, _ => False
      | _, None, _ => False
      | _, _, None => True
      | Some p, Some q, Some ILOps => forall us vs, (var_entail var ILOps) (p us vs) (q us vs)
    end.
    
  Definition PQR (t : typ) (l : expr ilfunc) (arg : TT) (us vs : tenv typ) :=
  	   forall var pt, 
  	     @valid_env us vs pt var l (snd (fst (arg var pt))) /\
  	     PQR_aux var pt t (arg var pt) l us vs.

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

  Lemma HVar tus tvs t v (H : typeof_expr tus tvs (Var v) = Some t) :
    PQR t (Var v) (atomic (Var v) tus tvs) tus tvs.
  Proof.
    unfold atomic, PQR, PQR_aux, TD, Teval; simpl in *; intros; split.
    + unfold valid_env; intros. constructor.
    + pose proof (typeof_expr_exprD'_impl RSym_sym tus tvs (Var v) H).
      destruct H0. forward; inv_all; subst. 
      simpl. forward; inv_all; subst. reflexivity.
  Qed.
(*
  Lemma Habs (e : pq_env) 
  : forall tus tvs t t' f e_res,
      typeof_expr tus tvs (Abs t f) = Some (tyArr t t') ->
      @PQR e t' f (e_res tus (t :: tvs)) tus (t :: tvs) ->
      @PQR e (tyArr t t') (Abs t f) (pq_abs t f e_res tus tvs) tus tvs.
  Proof.
    intros.
    unfold atomic, PQR, PQR_aux, TD, Teval; simpl; intros; split.
    + intros. exists (map (fun _ => None) typs).
      intros. apply valid_env_eq.
    + pose proof (typeof_expr_exprD'_impl RSym_sym tus tvs (Abs t f) H); destruct H1.
	  forward; inv_all; subst.
	  assert (exists IL : ILogic (typD ts nil (tyArr t t')), True).
	  eexists; [|apply I]. apply _.
	  destruct H2. reflexivity.
  Qed.

  Lemma Hex 
  : forall (e : pq_env) (tus tvs : tenv typ) t t_logic f (e_res : T),
      typeof_expr tus tvs (App (Inj (ilf_exists t t_logic)) (Abs t f)) = Some t_logic ->
      PQR e t_logic f (e_res tus (t :: tvs)) tus (t :: tvs) ->
      PQR e t_logic
          (App (Inj (ilf_exists t t_logic)) (Abs t f))
          (@pq_exists t t_logic f e_res tus tvs) tus tvs.
  Proof.
    intros.
    unfold PQR in *; intros; split. 
    + intros. exists (map (fun _ => None) typs).
      intros. apply valid_env_eq.
    + specialize (H0 var pt); destruct H0 as [_ H0]. 
      destruct pt; simpl in *; unfold PQR_aux, TD, Teval in *; simpl in *.
      * red_exprD; forward; inv_all; subst.
        red_exprD; forward; inv_all; subst.
        rewrite typ_cast_typ_refl.
        intros. reflexivity.
      * red_exprD; forward; simpl in *; inv_all; simpl in *; subst. unfold add_quant; simpl.
        red_exprD; forward; simpl in *; inv_all; simpl in *; subst.  
        red_exprD; forward; simpl in *; inv_all; subst.
        red_exprD. intros. destruct H4; subst. 
        destruct var; intros; simpl. setoid_rewrite H3. reflexivity.
        unfold flip. setoid_rewrite <- H3. reflexivity.
  Qed.
*)
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

  Lemma PQR_app_nil t l l_res tus tvs 
    (H : typeof_expr tus tvs l = Some t) :
  	PQR t l (pq_app l l_res nil tus tvs) tus tvs.
  Proof.
    admit.
    (*
    apply typeof_expr_exprD' in H. destruct H. 
    unfold PQR, PQR_aux, TD, Teval, add_quant; intros.
    simpl. forward. inv_all; subst. forward.
    rewrite pqapp_nil in H0. inv_all; subst; simpl in *.
    destruct var, pt; forward; inv_all; subst; reflexivity.
    *)
  Qed.


  Lemma add_quants_typeof_expr tus tvs xs f pt t (ILOps : ILogicOps (typD ts nil t)) (HIL : gs t = Some ILOps) :
  	typeof_expr tus (rev xs ++ tvs) f = Some t <-> typeof_expr tus tvs (add_quants pt t xs f) = Some t.
  Proof.
    generalize dependent tvs. generalize dependent f.
    induction xs; intros.
    + simpl in *. reflexivity.
    + simpl in *. rewrite <- app_assoc. simpl in *.
      rewrite IHxs; destruct pt; simpl in *; forward; inv_all; subst; simpl; forward.
  Qed.

  Lemma PQR_atomic vars pt t xs ms f tus tvs (ILOps : ILogicOps (typD ts nil t)) (HIL : gs t = Some ILOps)
   (H : typeof_expr tus (rev xs ++ tvs) f = Some t) : 
   PQR_aux vars pt t (xs, ms, f) (add_quants pt t xs f) tus tvs.
  Proof.
    rewrite add_quants_typeof_expr with (pt := pt) in H; [|eassumption].
    apply typeof_expr_exprD' in H. destruct H.
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

  Lemma PQR_atom tus tvs vars pt xs ms t f g (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
    (Hf : typeof_expr tus (rev xs ++ tvs) f = Some t)
    (Hg : typeof_expr tus tvs g = Some t)
    (Heq : forall df dg, exprD' tus tvs (add_quants pt t xs f) t = Some df -> exprD' tus tvs g t = Some dg -> forall us vs, df us vs -|- dg us vs) :
    PQR_aux vars pt t (xs, ms, f) g tus tvs.
  Proof.
    unfold PQR_aux, TD, Teval.
    apply typeof_expr_exprD' in Hg. destruct Hg.
    eapply add_quants_typeof_expr with (pt := pt) in Hf; [|eassumption].
    apply typeof_expr_exprD' in Hf. destruct Hf.
	    forward; inv_all; subst.
	rewrite Heq; reflexivity. 
  Qed.

	Lemma PQR_typeof vars pt t xs ms f g tus tvs (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
	    (Hf : typeof_expr tus tvs (add_quants pt t xs f) = Some t)
	 	(H : PQR_aux vars pt t (xs, ms, f) g tus tvs) :
	 	typeof_expr tus tvs g = Some t.
	 Proof.
	   	unfold PQR_aux, TD, Teval in H. 
	   	apply typeof_expr_exprD'_impl in Hf.
	    destruct Hf. forward. inv_all; subst.
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
        intros; subst. (** eta *) reflexivity. }
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

 Lemma PQR_aux_rewrite tus tvs e1 e2 t vars pt e3 de2 de3 (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps) (IL : ILogic (typD ts nil t))
    (He1 : exprD' tus tvs e2 t = Some de2) (He3 : exprD' tus tvs e3 t = Some de3) (H : forall us vs, (var_entail vars _) (de2 us vs) (de3 us vs))
 	(HPQR : PQR_aux vars pt t e1 e2 tus tvs) :
 	PQR_aux vars pt t e1 e3 tus tvs.
 Proof.
   	unfold PQR_aux, TD, Teval in *.
   	forward; inv_all; subst.
   	rewrite <- H. apply HPQR.
 Qed.

 Lemma PQR_aux_rewrite2 tus tvs e1 e2 t vars pt e3 (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps) (IL : ILogic (typD ts nil t))
    (H : forall de2, exprD' tus tvs e2 t = Some de2 -> exists de3, exprD' tus tvs e3 t = Some de3 /\ forall us vs, (var_entail vars _) (de2 us vs) (de3 us vs))
 	(He2 : PQR_aux vars pt t e1 e2 tus tvs) :
 	PQR_aux vars pt t e1 e3 tus tvs.
 Proof.
   	unfold PQR_aux, TD, Teval in *.
   	forward; inv_all; subst.
   	specialize (H1 t1 eq_refl).
   	destruct H1. destruct H0.
   	forward; inv_all; subst.
   	rewrite He2, H1; reflexivity.
  Qed.  

     Lemma apps_rewrite tus tvs e1 e2 rs t typs de1 de2 (ILOps : ILogicOps (typD ts nil t)) vars
        (He1 : exprD' tus tvs e1 (fold_right tyArr t typs) = Some de1) 
        (He2 : exprD' tus tvs e2 (fold_right tyArr t typs) = Some de2)
        (Heq : forall us vs, (var_entail vars _) (de1 us vs) (de2 us vs))
        (H : Forall2 (fun t e => typeof_expr tus tvs e = Some t) typs rs) :
        exists dea1 dea2, exprD' tus tvs (apps e1 rs) t = Some dea1 /\ exprD' tus tvs (apps e2 rs) t = Some dea2 /\ forall us vs, (var_entail vars _) (dea1 us vs) (dea2 us vs).
     Proof.
       generalize dependent e1; generalize dependent e2; generalize dependent rs; induction typs; simpl in *; intros.
       + inversion H; subst. simpl. exists de1, de2; tauto.
       + inversion H; subst; simpl in *; clear H.
         destruct (typeof_expr_exprD'_impl _ tus tvs y H2) as [v Hv].
         assert (typeof_expr tus tvs e1 = Some (tyArr a (fold_right tyArr t typs))) by (eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof; eassumption).
         assert (typeof_expr tus tvs e2 = Some (tyArr a (fold_right tyArr t typs))) by (eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof; eassumption).
         specialize (IHtyps (fun us vs => (de1 us vs) (v us vs)) (fun us vs => (de2 us vs) (v us vs))).
         apply IHtyps; try assumption; intros.
         * specialize (Heq us vs). destruct vars; simpl in *; specialize (Heq (v us vs)); apply Heq.
         * red_exprD; forward; inv_all; subst. forward; inv_all; subst. rewrite typ_cast_typ_refl. reflexivity.
         * red_exprD; forward; inv_all; subst. forward; inv_all; subst. rewrite typ_cast_typ_refl. reflexivity.
     Qed.
 
     Lemma apps_rewrite2 tus tvs e1 e2 rs t dea1 (ILOps : ILogicOps (typD ts nil t)) vars
        (H : exprD' tus tvs (apps e1 rs) t = Some dea1) 
        (He: forall typs de1, exprD' tus tvs e1 (fold_right tyArr t typs) = Some de1 -> 
        	                exists de2, exprD' tus tvs e2 (fold_right tyArr t typs) = Some de2 /\ forall us vs, (var_entail vars _ ) (de1 us vs) (de2 us vs)) :
        exists dea2, exprD' tus tvs (apps e2 rs) t = Some dea2 /\ forall us vs, (var_entail vars _) (dea1 us vs) (dea2 us vs).
     Proof.
       generalize dependent e1; generalize dependent e2; induction rs; simpl in *; intros.
       + specialize (He nil). apply He. simpl. apply H.
       + eapply IHrs; [eassumption |].
         intros.
         red_exprD; forward; inv_all; subst. clear IHrs.
         specialize (He (t1::typs) _ H2).
         destruct He as [de2 [He1 He2]].
         simpl in *.
         SearchAbout exprD' typeof_expr.
         assert (typeof_expr tus tvs e2 = Some (tyArr t1 (fold_right tyArr t typs))) by admit.
         forward; inv_all; subst.
         forward; inv_all; subst.
         rewrite typ_cast_typ_refl.
         eexists. split; [reflexivity|]. intros.
         simpl. 
         assert ((var_entail vars _) (t3 us vs) (de2 us vs)). apply He2.
         Local Transparent ILFun_Ops.
         destruct vars; apply H5.
    Qed.
 
       Lemma PQR_valid v p t xs ms e f tus tvs (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
          (H : PQR_aux v p t (xs, ms, e) f tus tvs) (Hvalid : valid_env tus tvs p v f ms) : 
         valid_env tus (rev xs ++ tvs) p v e ms.
       Proof.
         admit.
         (*
         unfold valid_env in *; intros.
         unfold PQR_aux, TD, Teval in H.
         forward; inv_all; subst.
         replace xs with (xs ++ nil) in H by (apply app_nil_r).
         pose proof (exprD'_add_quants_app_Some H3 H).
         destruct H5 as [? [? ?]].   
         pose proof H1. pose proof H5.      
         eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof in H1.		        
         eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof in H5.
         simpl in *. rewrite H5 in H1. inv_all; subst.
         specialize (Hvalid _ _ _ _ H0 H2 us (snd (hlist_split _ _ vs))).
         rewrite app_nil_r in *.
         rewrite H8 in H7. inv_all; subst.
         specialize (H6 us (snd (hlist_split _ _ vs))).
         specialize (H4 us (snd (hlist_split _ _ vs))).
         rewrite H6 in H4.
         
         clear -H4 Hvalid.
         generalize dependent typs. induction ms; intros; [constructor|].
         destruct a; [destruct p0|]; simpl in *.
         + destruct typs; simpl in *. admit. (* Trivially false, but must construct inversion rule *)
           apply ve_some. intros. 
           apply valid_arg_some_inv in Hvalid.
           destruct Hvalid as [? [? ?]].
           specialize (IHms typs (fun tus tvs => t2 tus tvs a) (H a) (fun tus tvs => df tus tvs a) _).
           simpl in *.
           apply IHms.
           
         *)
       Qed.

     Lemma Happ_aux tus tvs pt vars f rs t ms xs typs (ILOps : ILogicOps (typD ts nil t)) (IL : ILogic (typD ts nil t)) (Hgs : gs t = Some ILOps)
        (Hf : typeof_expr tus (rev xs ++ tvs) f = Some (fold_right tyArr t typs))
        (Hrs : Forall2
		       (fun (t : typ) (x : expr ilfunc * (tenv typ -> tenv typ -> TT)) =>
		        typeof_expr tus tvs (fst x) = Some t /\
		        PQR t (fst x) (snd x tus tvs) tus tvs) typs rs)
        (Henv : @valid_env tus (rev xs ++ tvs) pt vars f ms) :
     	PQR_aux vars pt t (pq_app_aux tus tvs pt (xs, ms, f) rs)
     	                  (apps (add_quants pt (fold_right tyArr t typs) xs f) (map fst rs)) tus tvs.
     Proof.     
        generalize dependent typs. generalize dependent f. generalize dependent ms. generalize dependent xs.
       	induction rs; intros.
       	+ inversion Hrs; subst. destruct ms; simpl in *.  
       	  * unfold PQR_aux, TD, Teval. simpl. forward; inv_all; subst.
       	    rewrite add_quants_typeof_expr with (pt := pt) in Hf; [|eassumption].
       	    pose proof Hf.
       	    apply typeof_expr_exprD' in Hf. destruct Hf. 
       	    rewrite <- add_quants_typeof_expr in H0; [|eassumption].
       	    unfold add_quants'. forward; inv_all; subst.
       	    rewrite H1 in H3. inv_all; subst. reflexivity.
       	  * unfold valid_env in Henv. simpl in *.
       	    pose proof Hf.
       	    apply typeof_expr_exprD' in Hf. destruct Hf. 
       	    specialize (Henv t nil _ ILOps Hgs H0).
       	    unfold add_quants'. forward; inv_all; subst.
       	    rewrite add_quants_typeof_expr with (pt := pt) in H; [|eassumption].
       	    apply typeof_expr_exprD' in H; destruct H.
       	    
       	    destruct o.
       	    - destruct p. 
       	      unfold PQR_aux, TD, Teval. forward; inv_all; subst; simpl. 
       	      forward; inv_all; subst. reflexivity.
       	    - unfold PQR_aux, TD, Teval. forward. inv_all; subst; simpl. 
       	      forward; inv_all; subst; reflexivity.
       	+ destruct typs; [inversion Hrs|].
       	  destruct ms; simpl in *.
       	  * unfold add_quants'. rewrite Hf.
       	    admit. (* Reflexivity, but also proof of type is required *)
       	  * destruct o; simpl in *. {
       	      destruct p, a; simpl in *.
       	      unfold add_quants'. rewrite Hf.
       	      inversion Hrs; subst. clear Hrs. simpl in *. destruct H2 as [? ?].
       	      unfold PQR in H0. specialize (H0 v p). destruct H0 as [_ H0].
       	      forward; inv_all; subst; simpl in *.       	    
       	      unfold PQR_aux, TD, Teval in H2. forward.
       	      remember (gs t0). destruct o; [|admit (* Reflexivity again *)].
       	      symmetry in Heqo.
       	      apply (PQR_aux_rewrite2 (e2 := apps (add_quants pt (fold_right tyArr t typs) (xs ++ l) (App (lift 0 (length l) f) (lift (length l) (length xs) e0))) (map fst rs))); [assumption | assumption | |]. 
              intros.
              apply (apps_rewrite2 (e1 := add_quants pt (fold_right tyArr t typs) (xs ++ l) (App (lift 0 (length l) f) (lift (length l) (length xs) e0)))); [assumption|].
              intros.
              red_exprD; forward; inv_all; subst.
	  	      assert (gs (fold_right tyArr t typs) = Some _) by admit.
		      assert (typs0 = typs) by admit; subst. simpl in *.
              rewrite add_quants_typeof_expr with (pt := pt) in Hf.
              forward; inv_all; subst.
              pose proof (exprD'_add_quants_app_Some H7 H6).
              destruct H8 as [de3 [Hde3 Heq]].
              red_exprD; forward; inv_all; subst; intros.
              simpl in *. 
              replace l with (l ++ nil) in Hde3 by (apply app_nil_r).
		      pose proof (exprD'_add_quants_app_Some H7 Hde3).
		      destruct H8 as [? [? ?]]. rewrite app_nil_r in H8. simpl in H8.
		      red_exprD; forward; inv_all; subst.
		      pose proof (exprD'_lift RSym_sym tus nil (rev l) (rev xs ++ tvs) f (tyArr t0 (fold_right tyArr t typs))). 
		      simpl in H8. rewrite rev_length in H8.
  		      pose proof (exprD'_lift RSym_sym tus (rev l) (rev xs) tvs e0 t5).
  		      do 2 rewrite rev_length in H14.
  		      forward; inv_all; subst.		      
		      assert (t0 = t5); [|subst]. {
		        eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof in H0.		        
		        eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof in H15.		        
		        rewrite <- add_quants_typeof_expr in H0; [|eassumption].
		        rewrite H0 in H15. inv_all; subst. reflexivity.
		      }
		      forward; inv_all; subst.
	  	      assert (gs (tyArr t5 (fold_right tyArr t typs)) = Some _) by admit.
		      pose proof (@exprD'_add_quants_rev_Some _ _ pt H12 tus xs tvs _ _ H14).
		      destruct H18 as [? [? ?]].
		      forward; inv_all; subst.
		      replace l with (l ++ nil) in H0 by (apply app_nil_r).
		      pose proof (exprD'_add_quants_app_Some Heqo H0).
		      destruct H20 as [? [? ?]]. simpl in H20.
		      rewrite H20 in H15; inv_all; subst.
		      eexists; split; [reflexivity|].
		      intros.
		      rewrite Heq. setoid_rewrite H10.
		      Check exprD'_add_quants_app_Some.
		      pose proof (exprD'_add_quants_app_Some Heqo H0).
		      transitivity ((pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs)
     (fun v0 : hlist (typD ts nil) (rev xs) =>
      pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs)
        (fun v1 : hlist (typD ts nil) (rev l) =>
         t4 us ((hlist_app v0 vs))
           (t6 us (hlist_app v1 vs)))))).
              match goal with 
                | |- var_entail vars _ ?a ?b => replace a with b; [reflexivity|]
              end. 
              f_equal.
              Require Import FunctionalExtensionality.
              apply functional_extensionality; intros.
              f_equal. apply functional_extensionality. intros.
              specialize (H17 us Hnil x1 (hlist_app x0 vs)).
              etransitivity.
              Lemma blarb (A B : Type) (f g : A -> B) (a : A) (H : f = g) : f a = g a.
              Proof.
                rewrite H. reflexivity.
              Qed.

         Lemma pt_quant_elim vars {A B : Type} {ILOps : ILogicOps A} {IL : ILogic A} pt (e1 e2 : B -> A) (H : forall x, (var_entail vars _) (e1 x) (e2 x)) :
         	(var_entail vars _) (pt_quant pt _ e1) (pt_quant pt _ e2).
         Proof.
           destruct vars; (destruct pt; simpl in *; unfold flip in *; [
           apply lforallR; intro x; apply lforallL with x; apply H |
           apply lexistsL; intro x; apply lexistsR with x; apply H]).
         Qed.

              eapply blarb. symmetry. apply H17.
              f_equal. symmetry. apply H16.
              setoid_rewrite H21 in H3.
              transitivity ((pt_quant pt _ (fun x => t4 us (hlist_app x vs))) (t3 us vs)); [|destruct vars; apply H19].
              assert ((pt_quant pt _ (fun x => t4 us (hlist_app x vs))) (t3 us vs) = (pt_quant pt _ (fun x => t4 us (hlist_app x vs) (t3 us vs)))).
              destruct pt; simpl; reflexivity.
              rewrite H22.
              eapply pt_quant_elim. intros.
              
              specialize (Henv t (t5::typs) _ _ Hgs H14 us (hlist_app x0 vs)).
              apply valid_arg_some_inv in Henv.
              destruct Henv as [? [? ?]]. clear H22.
              transitivity (t4 us (hlist_app x0 vs) (pt_quant p i (fun v => t6 us (hlist_app v vs)))); [|eapply H24; [assumption | apply H3]].
              eapply H25; eassumption. apply _. admit.
              apply IHrs; [rewrite rev_app_distr, <- app_assoc | rewrite rev_app_distr, <- app_assoc | assumption].
              + admit.
              + simpl. 
                replace (rev l) with (nil ++ (rev l)) by reflexivity.
                replace 0 with (length (@nil typ)) by reflexivity.
                rewrite <- app_assoc. 
                replace (length l) with (length (rev l)) by (apply rev_length).
                rewrite typeof_expr_lift. simpl. forward.
                replace (length xs) with (length (rev xs)) by (apply rev_length).
                rewrite typeof_expr_lift. 
                replace l with (l ++ nil) in H0 by (apply app_nil_r).
                pose proof (exprD'_add_quants_app_Some Heqo H0).
                destruct H6 as [de3 [Hde3 Heq]]. simpl in Hde3. 
                eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof in Hde3.
                forward; inv_all; subst. simpl. SearchAbout typ_eqb.
                
                Lemma typ_eqb_refl (t : typ) : typ_eqb t t = true.
                Proof.
                  induction t; simpl; try reflexivity.
                  rewrite IHt1, IHt2. reflexivity.
                  rewrite rel_dec_eq_true. reflexivity. apply _. reflexivity.
                  admit. (* This command should work: rewrite EqNat.beq_nat_refl. *)
                Qed.

                rewrite typ_eqb_refl. reflexivity.
                }
                
                admit.
            Qed.

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
     intros.
     intros vars pt.
     split; intros. 
     + specialize (H0 vars pt). destruct H0 as [H0 _].       
       induction rs; simpl.
       * unfold pq_app. simpl. forward. 
       * simpl in *.
         unfold pq_app. admit. (* TODO *)
     + assert (exists ILOps, (gs t) = Some ILOps) by admit. destruct H2.
       specialize (H0 vars pt).
       assert (typeof_expr tus tvs l = Some ft). {
         clear H0. generalize dependent l; generalize dependent ts0.
     	 induction rs; simpl in *; intros; inversion H1; simpl.
     	 + apply H.
     	 + specialize (IHrs _ H6 _ H).
     	   destruct H5 as [H5 _].
     	   simpl in *; forward; inv_all; subst; simpl in *.
     	   f_equal. unfold type_of_apply in IHrs.
     	   destruct t0; try congruence.
     	   forward.
       }
       destruct H0 as [H0 H5].
       unfold pq_app.
       destruct (l_res tus tvs vars pt); destruct p.
       assert (exists ILOps, gs ft = Some ILOps) by admit.
       destruct H4.
       assert (valid_env tus (rev l0 ++ tvs) pt vars e m) as Hvalid. 
       eapply (@PQR_valid _ _ ft); eassumption. 

       unfold PQR_aux, TD, Teval in H5.
       forward; inv_all; subst.
       simpl in *.
       assert (x0 = ILogic_Ops_fold_fun (t := t) x ts0) by admit. subst.
       assert (Forall2 (fun t e => typeof_expr tus tvs e = Some t) ts0 (map fst rs)). {
         clear -H1. generalize dependent rs.
         induction ts0; simpl; intros.
         + inversion H1; subst; simpl. constructor.
         + inversion H1; subst; simpl in *. destruct H2 as [H2 _]. constructor. assumption.
           apply IHts0. assumption.
       }

       destruct (apps_rewrite H5 H6 H8 H7) as [dea1 [dea2 [Hdea1 [Hdea2 Heq]]]].
       eapply @PQR_aux_rewrite with (e2 := apps (add_quants pt ft l0 e) (map fst rs)).
       assumption. apply _.
       eassumption. eassumption. eassumption.
       apply Happ_aux.
       apply _.
       admit.
       admit.
       assumption.
	   assumption.
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