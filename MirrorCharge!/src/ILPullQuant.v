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
  
  Inductive valid_arg (pt : pull_type) (var : variance) (t : typ) (ILOps : ILogicOps (typD ts nil t)) (A : Type) : 
    forall typs : list typ,  (A -> typD ts nil (fold_right tyArr t typs)) -> list (option (variance * pull_type)) -> Prop :=
    | ve_nil f : @valid_arg pt var t ILOps A nil f nil
    | ve_none te typs (f : A -> typD ts nil te -> typD ts nil (fold_right tyArr t typs)) args : 
      (forall (e : typD ts nil te), (var_entail var _) (((pt_quant pt) _ _ f) e) ((pt_quant pt) _ _ (fun x => (f x) e))) ->
      (forall e, @valid_arg pt var t ILOps A typs (fun x => (f x) e) args) ->
      @valid_arg pt var t ILOps A (te::typs) f (None::args)
    | ve_some te typs (f : A -> typD ts nil te -> typD ts nil (fold_right tyArr t typs)) pt' var' args :
      (forall B x (e : B -> typD ts nil te) (ILOps' : ILogicOps (typD ts nil te)), 
             (var_entail var _) ((pt_quant pt) _ _ (fun y => (f x) (e y))) ((f x) ((pt_quant pt') _ _ e))) ->
      (forall (e : typD ts nil te), (var_entail var _) ((pt_quant pt) _ _ (fun x => (f x) e)) (((pt_quant pt) _ _ f) e)) ->
      (forall e e' (ILOps' : ILogicOps (typD ts nil te)) x, (var_entail var' _) e e' -> (var_entail var _) ((f x) e) ((f x) e')) ->
      @valid_arg pt var t ILOps A (te::typs) f ((Some (var', pt'))::args).

  Definition valid_env (tus tvs : tenv typ) (xs : list typ) (pt : pull_type) (var : variance) (t : typ) (ILOps : ILogicOps (typD ts nil t)) (typs : list typ)
                       (f : expr ilfunc) modes :=
                       forall df, exprD' tus (rev xs ++ tvs) f (fold_right tyArr t typs) = Some df ->
                       forall us vs, @valid_arg pt var t ILOps (HList.hlist _ (rev xs)) typs (fun x => df us (HList.hlist_app x vs)) modes.
  

  Lemma valid_arg_some_inv (pt pt' : pull_type) (var var' : variance) (t te : typ) (ILOps : ILogicOps (typD ts nil t)) (A : Type) 
    (typs : list typ) (f : A -> typD ts nil te -> typD ts nil (fold_right tyArr t typs)) (modes : list (option (variance * pull_type))) 
    (H : @valid_arg pt var t ILOps A (te::typs) f ((Some (var', pt'))::modes)) : 
      (forall B x (e : B -> typD ts nil te) (ILOps' : ILogicOps (typD ts nil te)), 
             (var_entail var _)  ((pt_quant pt) _ _ (fun y => (f x) (e y))) ((f x) ((pt_quant pt') _ _ e))) /\
      (forall (e : typD ts nil te), (var_entail var _) ((pt_quant pt) _ _ (fun x => (f x) e)) (((pt_quant pt) _ _ f) e)) /\
      (forall e e' (ILOps' : ILogicOps (typD ts nil te)) x, (var_entail var' _) e e' -> (var_entail var _) ((f x) e) ((f x) e')).
  Proof.
    change (typD ts nil te -> typD ts nil (fold_right tyArr t typs)) with (typD ts nil (fold_right tyArr t (te::typs))) in f.
    inversion H. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4. subst.
    intuition.
  Qed.

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

  Lemma valid_arg_empty (pt : pull_type) (var : variance) (t : typ) (ILOps : ILogicOps (typD ts nil t)) (A : Type) o
    (f : A -> typD ts nil t) (modes : list (option (variance * pull_type))) 
    (H : @valid_arg pt var t ILOps A nil f (o::modes)) : False.
  Proof.
    change (typD ts nil t) with (typD ts nil (fold_right tyArr t nil)) in f.
    inversion H.
  Qed.

  Definition TT := variance -> pull_type -> list typ * expr ilfunc.

  Let T:Type := tenv typ -> tenv typ -> TT.
  Definition atomic (e : expr ilfunc) : T := fun _ _ _ _ => (nil, e).

  Record pq_env := {
    pq_env_fun :> ilfunc -> variance -> pull_type -> list (option (variance * pull_type));
    pq_env_sound : forall f pt var t tus tvs xs (ILOps : ILogicOps (typD ts nil t)) typs, 
    	typeof_expr tus tvs (Inj f) = Some (fold_right tyArr t typs) ->
    	valid_env tus tvs xs pt var ILOps typs (Inj f) (pq_env_fun f var pt)
  }.
(*
  Fixpoint typ_empty_mode (t : typ) : list (option (variance * pull_type)) :=
  	match t with
  		| tyArr t t' => None::(typ_empty_mode t')
  		| _          => nil
    end.

  Program Definition pq_env_empty := {| pq_env_fun := fun f _ _ => match typeof_expr nil nil (Inj f) with 
                                                                     | Some t => typ_empty_mode t
                                                                     | None   => nil
                                                                   end;
                                        pq_env_sound := _ |}.
  Next Obligation.
	unfold valid_env; intros.
	simpl.
	remember (typeof_func funcs gs es f). destruct o; [|congruence]. 
	inv_all; subst.
	induction typs. simpl.
	simpl in Heqo.
	SearchAbout typeof_func.
	Print typeof_func.
	destruct f. simpl in *.
	forward. inv_all; subst. simpl.
	
	reflexivity.
	forward.
	induction typs. simpl.
	simpl.
  
  Definition env_sound (e : pq_env) tus tvs p := 
        forall pt var xs t (ILOps : ILogicOps (typD ts nil t)) typs,
    	typeof_expr tus (rev xs ++ tvs)  = Some (fold_right tyArr t typs) ->
    	valid_env tus tvs xs pt var ILOps typs (Inj f) (e f var pt).  	
  *)  
  Definition pq_var (v : var) : T := atomic (Var v).
  Definition pq_uvar (u : uvar) : T := atomic (UVar u).
  Definition pq_inj (s : ilfunc) : T := atomic (Inj s).
  Definition pq_abs (x : typ) (e : expr ilfunc) (_ : T) : T :=
    atomic (Abs x e).
    
  Fixpoint pq_app_aux (us vs : tenv typ) (ats : list (option (variance * pull_type))) (f : list typ * expr ilfunc) (args : list (expr ilfunc * T)) : list typ * expr ilfunc :=
  match ats, args with
  	| Some (var, pt)::ats, (_, t)::args =>
  	  match f, t us vs var pt with
  	  	| (xs, f'), (ys, a) => pq_app_aux us vs ats (xs ++ ys, App (lift 0 (length ys) f') (lift (length ys) (length xs) a)) args
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
  			| _     => (nil, apps f (map fst args))
  		end.
 
  Definition pq_exists (t t_logic : typ) (f : expr ilfunc) (a : T) : T :=
    fun us vs vm pt =>
      match pt with
      	| PExists => let (ts, a) := a us (t :: vs) vm pt in (t::ts, a)
      	| _       => (nil, App (Inj (ilf_exists t t_logic)) (Abs t f)) 
      	
      end.

  Definition pqArgs (e : pq_env) : AppFullFoldArgs ilfunc TT :=
    @Build_AppFullFoldArgs ilfunc TT pq_var pq_uvar pq_inj pq_abs (pq_app e).

  Definition Teval (pt : pull_type) (e : list typ * expr ilfunc) (t : typ) :=
    let (xs, a) := e in add_quants pt t xs a.
        
  Definition TD (pt : pull_type) (t : typ) (e : list typ * expr ilfunc) (us vs : tenv typ) :=
    exprD' us vs (Teval pt e t) t.

  Definition PQR_aux var pt (t : typ) 
                     (arg : list typ * expr ilfunc)
                     (e : expr ilfunc) (us vs : tenv typ) 
                      :=  
    match (TD pt t arg) us vs, exprD' us vs e t, gs t with
      | None, _, _ => False
      | _, _, None => True 
      | Some p, Some q, Some _ => forall us vs, (var_entail var _) (p us vs) (q us vs)
      | _, _, _ => False
    end.
    
  Definition PQR (e : pq_env) (t : typ) (l : expr ilfunc) (arg : TT) (us vs : tenv typ) :=
  	   forall var pt, 
  	     (forall t' typs, t = fold_right tyArr t' typs ->
  	       exists modes, forall (ILOps : ILogicOps (typD ts nil t')) xs,
  	       valid_env us vs xs pt var ILOps typs l modes) /\
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

  Lemma valid_env_eq tus tvs xs pt var t (ILOps : ILogicOps (typD ts nil t)) typs l :
  	valid_env tus tvs xs pt var ILOps typs l (map (fun _ => None) typs).
  Proof.
    unfold valid_env; intros. clear H.
    induction typs; simpl; constructor; intros.
    + assert (exists IL : ILogic (typD ts nil t), True) by admit.
      destruct H. destruct var, pt; reflexivity.
    + specialize (IHtyps (fun us vs => df us vs e)).
      simpl in *. apply IHtyps.
  Qed.

  Lemma HVar (e : pq_env) tus tvs t v (H : typeof_expr tus tvs (Var v) = Some t) :
    PQR e t (Var v) (atomic (Var v) tus tvs) tus tvs.
  Proof.
    unfold atomic, PQR, PQR_aux, TD, Teval; simpl; intros; split.
    + intros. exists (map (fun _ => None) typs).
      intros. apply valid_env_eq.
    + pose proof (typeof_expr_exprD'_impl RSym_sym tus tvs (Var v) H).
      destruct H0. forward; inv_all; subst. reflexivity.
  Qed.

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
(*
  Lemma pqapp_cons_cases pq_env a ats l l_res tus tvs pt vars xs e 
  	(H : pq_app pq_env l l_res (a :: ats) tus tvs pt vars = (xs, e)) :
  	(xs = nil /\ e = l) \/
  	(exists f, l = Inj f /\ pq_app_aux tus tvs (pq_env f pt vars) (nil, Inj f) (a :: ats) = (xs, e)).
  Proof.
    destruct l; simpl in *; inv_all; subst; try (left; split; reflexivity).
    right. exists v. firstorder.
  Qed.
*)
  Lemma PQR_app_nil t pq_env l l_res tus tvs 
    (H : typeof_expr tus tvs l = Some t) :
  	PQR pq_env t l (pq_app pq_env l l_res nil tus tvs) tus tvs.
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
    + simpl in *; reflexivity.
    + simpl in *. rewrite <- app_assoc. simpl in *.
      rewrite IHxs; destruct pt; simpl in *; forward; inv_all; subst; simpl; forward.
  Qed.

  Lemma PQR_atomic vars pt t xs f tus tvs (ILOps : ILogicOps (typD ts nil t)) (HIL : gs t = Some ILOps)
   (H : typeof_expr tus (rev xs ++ tvs) f = Some t) : 
   PQR_aux vars pt t (xs, f) (add_quants pt t xs f) tus tvs.
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

  Lemma PQR_atom tus tvs vars pt xs t f g (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
    (Hf : typeof_expr tus (rev xs ++ tvs) f = Some t)
    (Hg : typeof_expr tus tvs g = Some t)
    (Heq : forall df dg, exprD' tus tvs (add_quants pt t xs f) t = Some df -> exprD' tus tvs g t = Some dg -> forall us vs, df us vs -|- dg us vs) :
    PQR_aux vars pt t (xs, f) g tus tvs.
  Proof.
    unfold PQR_aux, TD, Teval.
    apply typeof_expr_exprD' in Hg. destruct Hg.
    eapply add_quants_typeof_expr with (pt := pt) in Hf; [|eassumption].
    apply typeof_expr_exprD' in Hf. destruct Hf.
	    forward; inv_all; subst.
	rewrite Heq; reflexivity. 
  Qed.

	Lemma PQR_typeof vars pt t xs f g tus tvs (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
	    (Hf : typeof_expr tus tvs (add_quants pt t xs f) = Some t)
	 	(H : PQR_aux vars pt t (xs, f) g tus tvs) :
	 	typeof_expr tus tvs g = Some t.
	 Proof.
	   	unfold PQR_aux, TD, Teval in H. 
	   	apply typeof_expr_exprD'_impl in Hf.
	    destruct Hf. forward. inv_all; subst.
	    eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof; eassumption.
	Qed.

    Lemma PQR_typeof2 vars pt t xs f g tus tvs (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps)
        (Hg : typeof_expr tus tvs g = Some t)
     	(H : PQR_aux vars pt t (xs, f) g tus tvs) :
        typeof_expr tus tvs (add_quants pt t xs f) = Some t.
     Proof.
       	unfold PQR_aux, TD, Teval in H. 
       	apply typeof_expr_exprD'_impl in Hg.
        destruct Hg. forward. inv_all; subst.
        eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof. eassumption.
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

 Lemma PQR_aux_rewrite tus tvs e1 e2 t vars pt e3 (ILOps : ILogicOps (typD ts nil t)) (Hgs : gs t = Some ILOps) (IL : ILogic (typD ts nil t))
    (H : forall de2, exprD' tus tvs e2 t = Some de2 -> exists de3, exprD' tus tvs e3 t = Some de3 /\ forall us vs, (var_entail vars _) (de2 us vs) (de3 us vs))
 	(He2 : PQR_aux vars pt t e1 e2 tus tvs) :
 	PQR_aux vars pt t e1 e3 tus tvs.
 Proof.
   	unfold PQR_aux, TD, Teval in *.
   	forward; inv_all; subst.
   	specialize (H2 t1 eq_refl).
   	destruct H2. destruct H0.
   	forward; inv_all; subst.
   	rewrite He2, H2; reflexivity.
 Qed.

     Lemma apps_rewrite tus tvs e1 e2 rs t dea1 (ILOps : ILogicOps (typD ts nil t)) vars
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

 
  Lemma Happ pq_env
  : forall tus tvs l (l_res : T) rs t ts,
      typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
      let ft := fold_right tyArr t ts in
      PQR pq_env ft l (l_res tus tvs) tus tvs ->
      Forall2 (fun t x =>
                    typeof_expr tus tvs (fst x) = Some t
                 /\ PQR pq_env t (fst x) (snd x tus tvs) tus tvs)
              ts rs ->
      PQR pq_env t (apps l (map fst rs)) (pq_app pq_env l l_res rs tus tvs) tus tvs.
   Proof.
     intros.
     intros vars pt. simpl.
     assert (exists ILOps, (gs t) = Some ILOps) by admit. destruct H2.
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

     intros.  
     specialize (H0 t ts0 eq_refl).
     destruct H0 as [H0 H5].
     exists nil. intros.
     split; [admit|].
     destruct l. simpl.
     admit.
     replace (apps (Inj i) (map fst rs)) with (apps (add_quants pt (fold_right tyArr t ts0) nil (Inj i)) (map fst rs)).


     Lemma Happ_aux pq_env tus tvs pt vars f rs t modes xs typs (ILOps : ILogicOps (typD ts nil t)) (IL : ILogic (typD ts nil t)) (Hgs : gs t = Some ILOps)
        (Hf : typeof_expr tus (rev xs ++ tvs) f = Some (fold_right tyArr t typs))
        (Hrs : Forall2
		       (fun (t : typ) (x : expr ilfunc * (tenv typ -> tenv typ -> TT)) =>
		        typeof_expr tus tvs (fst x) = Some t /\
		        PQR pq_env t (fst x) (snd x tus tvs) tus tvs) typs rs)
        (Henv : @valid_env tus tvs xs pt vars t ILOps typs f modes) :
     	PQR_aux vars pt t (pq_app_aux tus tvs modes (xs, f) rs)
     	                  (apps (add_quants pt (fold_right tyArr t typs) xs f) (map fst rs)) tus tvs.
     Proof.
        generalize dependent typs. generalize dependent f. generalize dependent modes. generalize dependent xs.
       	induction rs; intros.
       	+ inversion Hrs; subst. destruct modes; simpl in *. 
       	  * unfold PQR_aux, TD, Teval. simpl. forward; inv_all; subst.
       	    rewrite add_quants_typeof_expr with (pt := pt) in Hf; [|eassumption].
       	    apply typeof_expr_exprD' in Hf. destruct Hf. forward.
       	    destruct vars; reflexivity.
       	  * unfold valid_env in Henv. simpl in *.
       	    pose proof Hf.
       	    rewrite add_quants_typeof_expr with (pt := pt) in Hf; [|eassumption].
       	    apply typeof_expr_exprD' in Hf. destruct Hf. forward.
       	    apply typeof_expr_exprD'_impl in H. destruct H.
       	    specialize (Henv _ H).
       	    destruct o. destruct p. unfold PQR_aux, TD, Teval. forward. inv_all; subst.
       	    destruct vars; intros; reflexivity.
       	    unfold PQR_aux, TD, Teval; forward. destruct vars; reflexivity.
       	+ destruct typs; [inversion Hrs|].
       	  destruct modes; [admit|].
       	  inversion Hrs; clear Hrs; subst. destruct H2.
       	  destruct o; simpl in *. 
       	  * destruct p, a; simpl in *.
       	    unfold PQR in H0. specialize (H0 v p).
       	    forward. 
       	    apply (PQR_aux_rewrite (e2 := apps (add_quants pt (fold_right tyArr t typs) (xs ++ l) (App (lift 0 (length l) f) (lift (length l) (length xs) e0))) (map fst rs))); [assumption | assumption | |]. 
            intros.
            apply (apps_rewrite (e1 := add_quants pt (fold_right tyArr t typs) (xs ++ l) (App (lift 0 (length l) f) (lift (length l) (length xs) e0)))); [assumption|].
            intros.
		    assert (gs (fold_right tyArr t typs) = Some _) by admit.
		    assert (typs = typs0) by admit; subst. simpl in *.
            pose proof (exprD'_add_quants_app_Some H5 H3).
            destruct H5 as [de3 [Hde3 Heq]].
            red_exprD; forward; inv_all; subst; intros.
		    destruct H6 as [? [? ?]].
		    replace l with (l ++ nil) in H5 by (apply app_nil_r).
            assert (gs ((fold_right tyArr t typs0)) = Some _) by admit. simpl in H6.
		    pose proof (exprD'_add_quants_app_Some H7 H5).
		    destruct H8 as [? [? ?]]. rewrite app_nil_r in H8. simpl in H8.
		    red_exprD; forward; inv_all; subst.
		    pose proof (typeof_expr_lift RSym_sym tus nil (rev l) (rev xs ++ tvs) f); simpl in H8. 
		    rewrite rev_length in H8. rewrite H8 in H10. rewrite H10 in Hf. inv_all; revert H9; subst; intros. 
		    rewrite add_quants_typeof_expr with (pt := pt) in H10.
		    forward; inv_all; subst.
		    pose proof (exprD'_lift RSym_sym tus nil (rev l) (rev xs ++ tvs) f (tyArr t0 (fold_right tyArr t typs0))).
		    simpl in H10. rewrite rev_length in H10. forward.
            assert (gs ((fold_right tyArr t (t0::typs0))) = Some _) by admit. simpl in H17.
		    pose proof (@exprD'_add_quants_rev_Some (tyArr t0 (fold_right tyArr t typs0)) _ pt H17 tus xs tvs _ _ H15).
		    destruct H18 as [? [? ?]].
		    forward. inv_all; subst.
		    pose proof (exprD'_lift RSym_sym tus (rev l) (rev xs) tvs e0 t0).
		    do 2 rewrite rev_length in H11. forward; inv_all; subst.
		    unfold PQR_aux, TD, Teval in H1.
		    forward; inv_all; subst.
		    forward; inv_all; subst.
		    assert (exists ILOps', gs t0 = Some ILOps') by admit. destruct H12.
		    forward; inv_all; subst.
		    rewrite typ_cast_typ_refl.
		    specialize (H12 t0 nil eq_refl). destruct H12. specialize (H12 x1 nil). destruct H12.
		    forward; inv_all; subst.
		    exists (fun us vs => (x0 us vs) (t7 us vs)). split. reflexivity.
		    intros.
		    unfold valid_env in Henv.
		    specialize (Henv _ H15 us vs).
		    apply valid_arg_some_inv in Henv. destruct Henv as [? [? ?]].
		    rewrite H6. setoid_rewrite H9. 
		    specialize (H16 us HList.Hnil). simpl in H16.
		    assert (var_entail vars (ILogic_Ops_fold_fun (t:=t) ILOps typs0) 
  (pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs0)
     (fun v0 : hlist (typD ts nil) (rev xs) =>
      pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs0)
        (fun v1 : hlist (typD ts nil) (rev l) =>
         t5 us (hlist_app v1 (hlist_app v0 vs))
           (t6 us (hlist_app v1 (hlist_app v0 vs)))))) (x0 us vs (t7 us vs)) =
var_entail vars (ILogic_Ops_fold_fun (t:=t) ILOps typs0)
  (pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs0)
     (fun v0 : hlist (typD ts nil) (rev xs) =>
      pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs0)
        (fun v1 : hlist (typD ts nil) (rev l) =>
         t3 us (hlist_app v0 vs) (t4 us (hlist_app v1 vs)))))
  (x0 us vs (t7 us vs))).
           f_equal. f_equal.
           Require Import FunctionalExtensionality.
            apply functional_extensionality; intros.
            apply f_equal.
            apply functional_extensionality.
            intros.
            rewrite H16, H21; reflexivity. 
            Lemma blarf (P Q : Prop) (HPQ : P = Q) (H : Q) : P. rewrite HPQ. assumption. Qed.

            eapply blarf.
            eassumption.
            clear H28.
             
            Lemma pt_quant_sym {A B C : Type} {ILOps : ILogicOps C} {IL : ILogic C} vars pt (e : A -> B -> C) :
               (var_entail vars _) (pt_quant pt _ (fun x => pt_quant pt _ (fun y => e x y))) (pt_quant pt _ (fun x => pt_quant pt _ (fun y => e y x))). 
            Proof.
              destruct vars; (destruct pt; simpl; [
                do 2 (apply lforallR; intros); do 2 (eapply lforallL); reflexivity |
                do 2 (apply lexistsL; intros); do 2 (eapply lexistsR); reflexivity
              ]).
            Qed.
            transitivity ((pt_quant pt (ILogic_Ops_fold_fun (t:=t) ILOps typs0)
     						(fun v0 : hlist (typD ts nil) (rev xs) =>
    					     t3 us (hlist_app v0 vs) (t7 us vs)))).

         Lemma pt_quant_elim vars {A B : Type} {ILOps : ILogicOps A} {IL : ILogic A} pt (e1 e2 : B -> A) (H : forall x, (var_entail vars _) (e1 x) (e2 x)) :
         	(var_entail vars _) (pt_quant pt _ e1) (pt_quant pt _ e2).
         Proof.
           destruct vars; (destruct pt; simpl in *; unfold flip in *; [
           apply lforallR; intro x; apply lforallL with x; apply H |
           apply lexistsL; intro x; apply lexistsR with x; apply H]).
         Qed.

         apply pt_quant_elim. intros.
         transitivity (t3 us (hlist_app x3 vs) (t2 us vs)).
         replace l with (l ++ nil) in H22 by (apply app_nil_r).
         pose proof (exprD'_add_quants_app_Some H1 H22).
         destruct H28 as [? [? ?]].
         pose proof (@exprD'_add_quants_rev_Some t0 _ p H1 tus l tvs _ _ H28).
         destruct H30 as [? [? ?]]. simpl in *.
         assert (Some t4 = Some x4) by intuition congruence.
         inv_all; subst.
         specialize (H29 us vs).
         etransitivity; [eapply H25|].
         eapply H27.
         rewrite H29.
         apply pt_quant_elim; intros.
         reflexivity.
         eapply H27.
         destruct v; simpl in *; apply H24.
         clear -H19.
         specialize (H19 us vs); destruct vars; [destruct H19 as [_ H19] | destruct H19 as [H19 _]]; simpl in *; specialize (H19 (t7 us vs)).
 

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