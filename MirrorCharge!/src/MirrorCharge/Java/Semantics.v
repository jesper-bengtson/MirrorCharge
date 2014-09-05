Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import Charge.Open.OpenILogic.
Require Import Charge.Open.Subst.

Require Import Java.Language.Lang.

Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Semantics.AxiomaticSemantics.

Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.

Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Applicative.

Require Import MirrorCharge.Java.Reify.
Require Import MirrorCharge.Java.Syntax.

Set Implicit Arguments.
Set Strict Implicit.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Lemma rule_seq c1 c2 (P Q R : sasn) G
      (Hc1 : G |-- {[P]} c1 {[Q]})
      (Hc2 : G |-- {[Q]} c2 {[R]}) :
  G |-- {[P]} cseq c1 c2 {[R]}.
Proof.
  apply rule_seq with Q; assumption.
Qed.

Lemma rule_skip P Q G : P |-- Q -> G |-- {[P]} cskip {[Q]}.
Proof.
  intros.
  eapply roc_post; [eapply rule_skip | apply H].
Qed.

Lemma rule_if (e : dexpr) c1 c2 (P Q : sasn) G
      (Hc1 : G |-- {[(@embed (@vlogic String.string _) sasn _ 
      				  (ap (T := Fun stack)
      				      (ap (pure (@eq sval)) (eval2 e)) 
      				  (pure (vbool true)))) //\\ P]} c1 {[Q]})
      (Hc2 : G |-- {[(@embed (@vlogic String.string _) sasn _ 
      				  (ap (T := Fun stack)
      				      (ap (pure (@eq sval)) (eval2 (E_not e))) 
      				  (pure (vbool true)))) //\\ P]} c2 {[Q]}) :
  G |-- {[P]} cif e c1 c2 {[Q]}.
Proof.
  eapply rule_if; unfold vlogic_eval, Open.liftn, Open.lift; simpl in *;
  	[apply Hc1|apply Hc2].
Qed.


  Lemma rule_read_fwd (x y : String.string) (f : String.string) (e : dexpr) (P : sasn) (G : spec)
    (HPT : P |-- ap (T := Fun stack) (ap (ap (pure pointsto) (stack_get y)) (pure f)) (eval2 e)) : 
  (*  G |-- {[ P ]} 
              cread x y f 
              {[ Exists v : sval, (@embed (@vlogic String.string _) sasn _)
    								      (ap (T := Fun stack) 
    								          (ap (pure (@eq sval)) (stack_get x)) 
    								          ((eval2 e)[{(pure v)//x}])) //\\ 
    							   P[{(pure v)//x}]]}.*) True.
  Proof.
(*
	reify_imp (stack_get y).
	reify_imp (ap (T := Fun stack) (ap (ap (pure pointsto) (stack_get y)) (pure f)) (eval2 e)).
	admit.
	
    simpl in *.
    pose proof @rule_read_fwd x y f (eval2 e) P. unfold Open.liftn, Open.lift, open_eq, stack_get, Open.var_expr in *; simpl in *.
	rewrite <- H; [apply ltrueR | apply HPT].
	*)
  Qed.
