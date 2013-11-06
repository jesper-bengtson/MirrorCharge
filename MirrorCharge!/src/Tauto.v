Require Import ILogicFunc ILogic.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import Bool.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.

Ltac reduce_exprD := 
	repeat match goal with
		| H : context [ exprD _ _ _ _] |- _ => 
		  progress (autorewrite with exprD_rw in H; simpl in H)
	end.


Section Tauto.
  Context (ts : types) (funcs : fun_map ts) (gs : logic_ops ts).
  Context (H : forall g, match gs g with
                             | Some T => @ILogic _ T
                             | None => unit
                           end).
                           
  Local Instance RSym_ilfunc : SymI.RSym (typD ts) ilfunc := RSym_ilfunc ts funcs gs.

Require Import ExtLib.Core.RelDec.

  Fixpoint assumption (env : list (expr ilfunc)) (p : expr ilfunc) :=
  	match env with
  		| nil => false
  		| q :: env' => if p ?[eq] q then
  					       true
  					   else
  					   	   assumption env' p
  	end.
  
  Fixpoint tauto (env : list (expr ilfunc)) (p : expr ilfunc) : bool :=
  match p with
  	| Inj (ilf_true _) => true
  	| App (App (Inj (ilf_and _)) p) q => andb (tauto env p) (tauto env q)
  	| App (App (Inj (ilf_or _)) p) q => orb (tauto env p) (tauto env q)
  	| App (App (Inj (ilf_impl _)) p) q => tauto (p::env) q
  	| _ => assumption env p
  end.
    
  Fixpoint eval_env (env : list (expr ilfunc)) us vs (t : typ) (ILO : ILogicOps (typD ts nil t)) 
  	: option (typD ts nil t) :=
  	match env with
  		| nil => Some (@ltrue _ ILO)
  		| p :: env => match exprD us vs p t, eval_env env us vs t ILO with
  				 		| Some p, Some q => Some (@land _ ILO q p)
  				 		| _, _ => None
  				 	  end
  	end.

	Hint Extern 0 (Injective (typ_cast_typ ?A ?B ?C ?D ?E = Some ?F)) =>
	  eapply (Injective_typ_cast_typ_hetero_Some A B C D E F) : typeclass_instances.

Lemma assumption_sound : forall (env : list (expr ilfunc)) (p : expr ilfunc) (t : typ) us vs x v 
    (ILO : ILogicOps (typD ts nil t))
	(_ : exprD us vs p t = Some v) 
	(_ : eval_env env us vs t ILO = Some x)
    (_ : gs t = Some ILO),
  	assumption env p = true -> @lentails (typD ts nil t) ILO x v.
Proof.
	intros. generalize dependent x; generalize dependent env.
	specialize (H t); rewrite H2 in H.
	induction env; simpl; try congruence.
	+ intros; simpl in *.
	Require Import ExtLib.Tactics.Consider.
	  forward; inv_all; subst.	  
	  consider (p ?[ eq ] a).
	  * intros Hpa; subst. apply (@landL1 _ ILO H).
	    rewrite H1 in H0. inv_all; subst. 
	    Require Import Setoid Morphisms RelationClasses.
	    admit.
	  * intros Hpa Henv.
	    apply (@landL1 _ ILO H).
	    apply IHenv; auto.
Qed.
  
  Lemma tauto_sound : forall (p : expr ilfunc) (t : typ) env us vs x v
    (_ : exprD us vs p t = Some v) 
    (ILO : ILogicOps (typD ts nil t))
    (_ : gs t = Some ILO)
 	(_ : eval_env env us vs t ILO = Some x),
  	tauto env p = true -> @lentails (typD ts nil t) ILO x v.
  Proof.
    intro p.
    apply expr_strong_ind with (e := p); clear p; intros.
    destruct e; simpl in *; try (eauto using assumption_sound).
    
    destruct i; eauto using assumption_sound.
	reduce_exprD. unfold SymI.funcAs in H1. simpl in H1.
	forward. inv_all. destruct H5; subst.
	specialize (H t); rewrite H1 in *. inv_all; subst. 
	apply (@ltrueR _ ILO H).

    destruct e1; eauto using assumption_sound.
    destruct e1_1; eauto using assumption_sound.
    destruct i; eauto using assumption_sound.
	+ repeat progress (reduce_exprD; forward; inv_all; try subst).
	  revert H14; subst.
	  unfold SymI.funcAs in H9; simpl in H9. forward. inv_all; subst. 

	  repeat (match goal with
	  		   | H : exists x, _ |- _ => destruct H; intuition; subst
	  		  end). inv_all; subst.
	  		  inversion x1; subst. subst.
	  		  	  		  Require Import ExtLib.Tactics.EqDep.
	  		  
	  		  uip_all.
	rewrite Bool.andb_true_iff in H4. destruct H4 as [H4 H5].
	rewrite H1 in H2. inversion H2; subst.
	specialize (H t). rewrite H1 in H.
	apply (@landR _ _ H); eapply H0; try eassumption; red; solve_expr_acc_trans.

	+ repeat progress (reduce_exprD; forward; inv_all; try subst).
	  revert H14; repeat subst. intros.
	  unfold SymI.funcAs in H9; simpl in H9; forward; inv_all; subst.
	  repeat (match goal with
	  		   | H : exists x, _ |- _ => destruct H; intuition; subst
	  		  end). inv_all; subst.
	  		  inversion x1; subst. subst.
	  		  	  		  Require Import ExtLib.Tactics.EqDep.
	  		  
	  		  uip_all.
	rewrite H2 in *; inv_all; subst.
	specialize (H t). rewrite H2 in H.
	rewrite Bool.orb_true_iff in H4. destruct H4 as [H4 | H4].
	apply (@lorR1 _ i H); eapply H0; try eassumption; red; solve_expr_acc_trans.
	apply (@lorR2 _ i H); eapply H0; try eassumption; red; solve_expr_acc_trans.
	+ repeat progress (reduce_exprD; forward; inv_all; try subst).
	  revert H14; subst; intros.
	  unfold SymI.funcAs in H9; simpl in H9; forward; inv_all; subst.
	  repeat (match goal with
	  		   | H : exists x, _ |- _ => destruct H; intuition; subst
	  		  end). inv_all; subst.
	  		  inversion x1; subst. subst.
	  		  uip_all.
	  		  simpl in *.
	rewrite H1 in H2. inversion H2; subst.
	specialize (H t). rewrite H1 in H.
	  
	apply (@limplAdj _ _ H).
	eapply H0; try eassumption.
	* red; solve_expr_acc_trans.
	* simpl. rewrite H12, H3. reflexivity.
Qed.	

End Tauto.