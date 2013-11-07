Require Import ILogic ILogicFunc.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MapPositive.
Require Import MirrorCore.SymI.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Data.Positive.
Require Import Ext.ExprLift.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.

Set Implicit Arguments. 
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Definition inhabited (ts : types) := forall (t : typ),
  option (Inhabited (typD ts nil t)).

Section PullExistsLeft.
  Context (ts : types) (funcs : fun_map ts) (gs : logic_ops ts).
  Context (H : forall g, match gs g with
                             | Some T => @ILogic _ T
                             | None => unit
                           end).
                           
  Local Instance RSym_ilfunc : SymI.RSym (typD ts) ilfunc := RSym_ilfunc ts funcs gs.

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
	rewrite (@exprD_app ts ilfunc RSym_ilfunc us vs
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

