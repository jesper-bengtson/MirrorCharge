Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.Later.
Require Import Charge.Logics.ILEmbed.
Require Import Charge.Open.OpenILogic.
Require Import Charge.Open.Subst.

Require Import Java.Language.Lang.
Require Import Java.Language.Program.

Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Semantics.AxiomaticSemantics.

Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.

Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Structures.Applicative.

Require Import MirrorCharge.Java.Reify.

Set Implicit Arguments.
Set Strict Implicit.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Lemma pull_exists {A} {P : A -> sasn} c Q G
	(H : forall x, G |-- {[P x]} c {[Q]}) :
	G |-- {[Exists x, P x]} c {[Q]}.
Proof.
  rewrite <- exists_into_precond2.
  apply lforallR. apply H.
Qed.

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
	
Lemma rule_skip2 P G :(* P |-- Q -> *)G |-- {[P]} cskip {[P]}.
Proof.
  apply rule_skip. reflexivity.
Qed.

Notation "'ap_eq' '[' x ',' y ']'" :=
	 (ap (T := Fun stack) (ap (T := Fun stack) (pure (T := Fun stack) (@eq sval)) x) y).
Notation "'ap_pointsto' '[' x ',' f ',' e ']'" := 
	(ap (T := Fun stack) (ap (T := Fun stack) (ap (T := Fun stack) 
		(pure (T := Fun stack) pointsto) (stack_get x)) 
			(pure (T := Fun stack) f)) e).
Notation "'ap_typeof' '[' e ',' C ']'" :=
	(ap (T := Fun stack) 
	    (ap (T := Fun stack) 
	        (pure (T := Fun stack) typeof) 
	        (pure (T := Fun stack) C))
	    e).

Lemma rule_if (e : dexpr) c1 c2 (P Q : sasn) G
      (Hc1 : G |-- {[(@embed (@vlogic var _) sasn _ 
                      (ap_eq [eval e, pure (vbool true)])) //\\ P]} c1 {[Q]})
      (Hc2 : G |-- {[(@embed (@vlogic var _) sasn _ 
                      (ap_eq [eval (E_not e), pure (vbool true)])) //\\ P]} c2 {[Q]}) : 
  G |-- {[P]} cif e c1 c2 {[Q]}. 
Proof.
  eapply rule_if; unfold vlogic_eval, Open.liftn, Open.lift; simpl in *;
  	[apply Hc1|apply Hc2].
Qed.
Check @apply_subst.
  Lemma rule_read_fwd (x y : var) (f : field) (e : stack -> sval) (P Q : sasn) (G : spec)
    (HP : P |-- ap_pointsto [y, f, e])
    (HQ : Exists v : sval, embed (ap_eq [stack_get x, apply_subst e (subst1 (pure (T := Fun stack) v) x)]) //\\ 
    					      (apply_subst P (subst1 (pure (T := Fun stack) v) x)) |-- Q) :
    G |-- {[ P ]} cread x y f {[ Q ]}.
  Proof.
    reify_imp (ap_pointsto [y, f, e]).
    pose proof @rule_read_fwd x y f e P. 
    unfold Open.liftn, Open.lift, open_eq, stack_get, Open.var_expr in *; simpl in *.
    rewrite <- HQ , <- H; [apply ltrueR | apply HP].
  Qed.

Require Import Charge.Logics.BILogic.

  Lemma rule_write_fwd (x : var) (f : field) (e : dexpr) G (P Q F : sasn) (e' : stack -> sval)
        (HP : P |-- ap_pointsto [x, f, e'] ** F) 
        (HQ : ap_pointsto [x, f, eval e] ** F |-- Q) :
    G |-- ({[ P ]} cwrite x f e {[ Q ]}).
  Proof.
     pose proof @rule_write_frame G P F x f e' e. unfold Open.liftn, Open.lift, open_eq, stack_get, Open.var_expr in *; simpl in *.
	 rewrite <- HQ, H.
	 unfold stack. unfold pointsto. unfold eval.
	 
	 setoid_rewrite <- sepSPC1 at 2.
	 reflexivity. 
	 rewrite HP. 
	 setoid_rewrite <- sepSPC1 at 2.
	 reflexivity.
  Qed.

  Lemma rule_assign_fwd (x : var) (e : dexpr) G P :
    G |-- {[ P ]} cassign x e {[ Exists v : sval,
                                 embed (ap_eq [stack_get x, 
                                               apply_subst (eval e) (subst1 (pure (T := Fun stack) v) x)]) //\\ 
    							   (apply_subst P (subst1 (pure (T := Fun stack) v) x)) ]}.
  Proof.
    pose proof @rule_assign_fwd G P.
    apply H. reflexivity.
  Qed.

Definition set_fold_fun (x f : String.string) (P : sasn) :=
	ap_pointsto [x, f, pure null] ** P.

  Lemma rule_alloc_fwd (x C : String.string) (G : spec) (P : sasn) (fields : SS.t) (Pr : Prog_wf) 
	(Heq : G |-- prog_eq Pr)
	(Hf : field_lookup Pr C fields) :
	G |-- {[ P ]} calloc x C {[ Exists p : ptr, embed (ap_typeof [stack_get x, C] //\\
	                                            ap_eq [stack_get x, pure (vptr p)]) //\\
	                                            SS.fold (set_fold_fun x) fields 
	                                                    (apply_subst P (subst1 (pure (T := Fun stack) p) x)) ]}.
  Proof.
  	admit.
  Qed.

Require Import List.
(*
  Lemma rule_static_complete C (m : String.string) (ps : list String.string) (es : list dexpr) (x r : var) G
    (P Q F Pm Qm : sasn)
    (HSpec : G |-- |> method_spec C m ps r Pm Qm)
    (HPre: P |-- apply_subst2 asn Pm (substl_trunc (zip ps (@map _ (stack -> sval) eval2 es))) ** F)
    (HLen: length ps = length es) :
          G |-- {[ P ]} cscall x C m es {[ Exists v:sval, apply_subst asn Qm (substl_trunc (zip (@cons String.string r ps) 
                                     (@cons (stack -> sval) (stack_get x)
                                      (@map (stack -> sval) _ (fun e => apply_subst2 sval e (subst2 (pure (T := Fun stack) v) x)) 
                                          (@map dexpr (stack -> sval) eval2 es))))) ** 
                           apply_subst2 asn F (subst2 (pure (T := Fun stack) v) x)]}.
Proof.
	admit.
Qed.

Lemma rule_dynamic_complete C (m : String.string) (ps : list String.string) (es : list dexpr) (x y r : var) G
    (P F Pm Qm : sasn)
    (HSpec : G |-- |> method_spec2 C m ps r Pm Qm)
    (HPre: P |-- (embed (ap_typeof [stack_get y, C]) //\\ 
                  apply_subst2 asn Pm (substl_trunc (zip ps (@map _ (stack -> sval) eval2 (E_var y :: es))))) ** 
                 F)
    (HLen: length ps = length (E_var y :: es)) :
           G |-- {[ P ]} cdcall x y m es 
                 {[ Exists v:sval, embed (ap_typeof [apply_subst2 sval (stack_get y) (subst2 (pure (T := Fun stack) v) x), C]) //\\
                    apply_subst2 asn Qm (substl_trunc (zip (@cons String.string r ps) 
                    (@cons (stack -> sval) (stack_get x) (@cons (stack -> sval) (apply_subst2 sval (stack_get y) (subst2 (pure (T := Fun stack) v) x))
			        (@map (stack -> sval) _ (fun e => apply_subst2 sval e (subst2 (pure (T := Fun stack) v) x)) 
			        (@map dexpr (stack -> sval) eval2 es)))))) ** 
                    apply_subst2 asn F (subst2 (pure (T := Fun stack) v) x) ]}.
Proof.
    eapply rule_dcall_forward.
    eassumption.
    rewrite HPre. 
    reflexivity.
    assumption.
    reflexivity.
Qed.
*)