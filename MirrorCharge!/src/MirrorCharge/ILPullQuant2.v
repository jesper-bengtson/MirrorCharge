Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.syms.SymSum.

Require Import MirrorCharge.AutoSetoidRewrite.

Require Import MirrorCharge.ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.

Section ILPullQuant.

  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RelDec_typ_eq : RelDec (@eq typ).
  Variable RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq.

  Variable func : Type.
  Variable RelDec_func_eq : RelDec (@eq func).
  Variable RelDecCorrect_func_eq : RelDec_Correct RelDec_func_eq.
  
  Variable func_to_ilfunc : func -> option (ilfunc typ).
  Variable ilfunc_to_func : ilfunc typ -> func.
  
  Variable Eq : typ -> func.

Let Rbase := expr typ func.

(*
Let Rbase := expr typ (ilfunc typ).
*)
Definition m (T : Type) : Type :=
  rsubst Rbase -> option (T * rsubst Rbase).

Definition rg_bind {T U} (a : m T) (b : T -> m U) : m U :=
  fun s => match a s with
             | None => None
             | Some (val,s') => b val s'
           end.
Definition rg_fail {T} : m T := fun _ => None.
Definition rg_ret {T} (v : T) : m T := fun s => Some (v, s).
Definition rg_plus {T} (l r : m T) : m T :=
  fun s =>
    let v := l s in
    match v with
      | None => r s
      | Some _ => v
    end.
Print rel_dec.

Definition match_plus_l (e : expr typ func) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App (Inj a) (App (Inj b) P)) Q =>
      match func_to_ilfunc a, func_to_ilfunc b with 
      	| Some (ilf_and _), Some (ilf_exists l t) =>
	      rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
	               (RGflip (RGinj (Inj (ilfunc_to_func (ilf_entails l))))))
	        (fun _ =>
	           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t)))
	                  (Abs t (App (App (Inj ((ilfunc_to_func (ilf_and l)))) 
	                  (App P (Var 0))) (lift 0 1 Q))))))
	      (rg_bind
	        (unifyRG (@rel_dec (expr typ func) _ _) rg 
	                 (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))
	        (fun _ =>
	           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t))) 
	                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_and l))) 
	                  (App P (Var 0))) (lift 0 1 Q))))))
	    | _, _ => rg_fail
	  end
	  | _ => rg_fail
  end.
  
Definition match_plus_r (e : expr typ func) (rg : RG Rbase) : m (expr typ func) :=
  match e with
   | App (App (Inj a) Q) (App (Inj b) P) =>
     match func_to_ilfunc a, func_to_ilfunc b with
       | Some (ilf_and _), Some (ilf_exists l t) =>
	      rg_plus
	      (rg_bind
	        (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))
	        (fun _ =>
	           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t))) 
	                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_and l)))
	                  (lift 0 1 Q)) (App P (Var 0)))))))
	      (rg_bind
	        (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (Inj (ilfunc_to_func (ilf_entails l))))))
	        (fun _ =>
	           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t)))
	                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_and l))) 
	                  (lift 0 1 Q)) (App P (Var 0)))))))
	   | _, _ => rg_fail
	 end
   | _ => rg_fail
 end.

Definition rewrite_exs (e : (expr typ func)) (_ : list (RG (expr typ func))) (rg : RG (expr typ func)) : m (expr typ func) :=
  rg_plus (match_plus_l e rg) (match_plus_r e rg).

Definition rewrite_respects (e : Rbase) (_ : list (RG Rbase))
	 (rg : RG Rbase) : m (expr typ func) :=
	match e with
		| Inj op =>
		  match func_to_ilfunc op with
			| Some (ilf_and l) => 
				rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
				        (RGrespects (RGinj (Inj (ilfunc_to_func (ilf_entails l)))) 
				        (RGrespects (RGinj (Inj (ilfunc_to_func (ilf_entails l)))) 
				        (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))))
					(fun _ => rg_ret (Inj (ilfunc_to_func (ilf_and l))))
			| Some (ilf_or l) => 
				rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
				        (RGrespects (RGinj (Inj (ilfunc_to_func (ilf_entails l)))) 
				        (RGrespects (RGinj (Inj (ilfunc_to_func (ilf_entails l))))
				        (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))))
					(fun _ => rg_ret (Inj (ilfunc_to_func (ilf_or l))))
			| Some (ilf_impl l) => 
				rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
				                 (RGrespects (RGflip (RGinj (Inj (ilfunc_to_func (ilf_entails l))))) 
				                 (RGrespects (RGinj (Inj (ilfunc_to_func (ilf_entails l)))) 
				                 (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))))
					(fun _ => rg_ret (Inj (ilfunc_to_func (ilf_impl l))))
			| Some (ilf_exists l t) => 
				rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
				                 (RGrespects (RGrespects (RGinj (Inj (Eq t)))
							                 (RGinj (Inj (ilfunc_to_func (ilf_entails l))))) 
							                 (RGinj (Inj (ilfunc_to_func (ilf_entails l))))))
					(fun _ => rg_ret (Inj (ilfunc_to_func (ilf_exists l t))))
			| Some (ilf_true l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))
					(fun _ => rg_ret (Inj (ilfunc_to_func (ilf_true l))))
			| _ => rg_fail
		  end
		| _ => rg_fail
	end.
		
Definition rw_type := expr typ func -> list (RG (expr typ func))
                      -> RG (expr typ func) -> m (expr typ func).

Section interleave.
  Variables (rw rw' : rw_type -> rw_type).

  Fixpoint interleave (n : nat)
           (e : expr typ func) (rvars : list (RG (expr typ func)))
           (rg : RG (expr typ func)) : m (expr typ func) :=
    match n with
      | 0 => rg_fail
      | S n => rw (fun rs => rw' (fun e rvars rg rs => interleave n e rvars rg rs) rs) e rvars rg
    end.
End interleave.



Fixpoint rw_fix (n : nat)
  (rw : rw_type -> rw_type)
  (e : expr typ func) (rvars : list (RG Rbase)) (rg : RG Rbase)
  (rs : rsubst Rbase)
: option (expr typ func * rsubst Rbase) :=
  match n with
    | 0 => Some (e,rs)
    | S n => rw (fun e rvars rg rs => rw_fix n rw e rvars rg rs) e rvars rg rs
  end.

Definition quant_pull l (e : expr typ func) : expr typ func :=
  match
    rw_fix 10 (@setoid_rewrite typ func (expr typ func)
                     rel_dec
                     rewrite_exs rewrite_respects)
      e nil (RGinj (Inj (ilfunc_to_func (ilf_entails l))))
      (rsubst_empty _)
  with
    | None => e
    | Some (e,_) => e
  end.
  
End ILPullQuant.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyNat | tyBool
| tyProp.

Fixpoint typD (ts : list Type) (t : typ) : Type :=
  match t with
    | tyNat => nat
    | tyBool => bool
    | tyProp => Prop
    | tyArr a b => typD ts a -> typD ts b
  end.

Definition typ_eq_dec : forall a b : typ, {a = b} + {a <> b}.
  decide equality.
Defined.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b =>
               match typ_eq_dec a b with
                 | left _ => true
                 | right _ => false
               end }.

Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ.
Proof.
  constructor.
  intros.
  unfold rel_dec; simpl.
  destruct (typ_eq_dec x y); intuition.
Qed.

Inductive tyAcc' : typ -> typ -> Prop :=
| tyArrL : forall a b, tyAcc' a (tyArr a b)
| tyArrR : forall a b, tyAcc' b (tyArr a b).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc'
; type_cast := fun _ a b => match typ_eq_dec a b with
                              | left pf => Some pf
                              | _ => None
                            end
}.

Instance RTypeOk_typ : @RTypeOk typ _.
Proof.
  eapply makeRTypeOk.
  { red.
    induction a; constructor; inversion 1.
    subst; auto.
    subst; auto. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x x).
    f_equal. compute.
    uip_all. reflexivity. congruence. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x y); try congruence. }
Qed.

Instance Typ2_tyArr : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ _ => eq_refl
; typ2_match :=
    fun T ts t tr =>
      match t as t return T (TypesI.typD ts t) -> T (TypesI.typD ts t) with
        | tyArr a b => fun _ => tr a b
        | _ => fun fa => fa
      end
}.

Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
Proof.
  constructor.
  { reflexivity. }
  { apply tyArrL. }
  { intros; apply tyArrR. }
  { inversion 1; subst; unfold Rty; auto. }
  { destruct x; simpl; eauto.
    left; do 2 eexists; exists eq_refl. reflexivity. }
  { destruct pf. reflexivity. }
Qed.

Instance Typ0_tyProp : Typ0 _ Prop :=
{| typ0 := tyProp
 ; typ0_cast := fun _ => eq_refl
 ; typ0_match := fun T ts t =>
                   match t as t
                         return T Prop -> T (TypesI.typD ts t) -> T (TypesI.typD ts t)
                   with
                     | tyProp => fun tr _ => tr
                     | _ => fun _ fa => fa
                   end
 |}.
 
Inductive func :=
| N : nat -> func | Eq : typ -> func.


Definition typeof_func (f : func) : option typ :=
  Some match f with
         | N _ => tyNat
         | Eq t => tyArr t (tyArr t tyProp)
       end.

Definition funcD (ts : list Type) (f : func)
: match typeof_func f with
    | None => unit
    | Some t => typD ts t
  end :=
  match f as f return match typeof_func f with
                        | None => unit
                        | Some t => typD ts t
                      end
  with
    | N n => n
    | Eq t => @eq _
  end.

Instance RelDec_func_eq : RelDec (@eq func) :=
{ rel_dec := fun (a b : func) =>
               match a , b with
                 | N a , N b => a ?[ eq ] b
                 | Eq a , Eq b => a ?[ eq ] b
                 | _ , _ => false
               end
}.

Instance RSym_func : RSym func :=
{ typeof_sym := typeof_func
; symD := funcD
; sym_eqb := fun a b => Some (a ?[ eq ] b)
}.
 
Definition my_func := (func + ilfunc typ)%type.

Definition func_to_ilfunc (f : my_func) : option (ilfunc typ) :=
	match f with
		| inl _ => None
		| inr ilf => Some ilf
	end.
 
Definition ilfunc_to_func (ilf : ilfunc typ) : my_func := inr ilf.
Definition my_eq t : my_func := inl (Eq t).
 
Instance RelDec_my_func_eq : RelDec (@eq my_func) :=
{ rel_dec := fun (a b : my_func) =>
               match a , b with
                 | inl a , inl b => a ?[ eq ] b
                 | inr a , inr b => a ?[ eq ] b
                 | _ , _ => false
               end
}.

Definition fAnd l a b : expr typ my_func := App (App (Inj (inr (ilf_and l))) a) b.
Definition fOr l a b : expr typ my_func := App (App (Inj (inr (ilf_or l))) a) b.
Definition fAll l t P : expr typ my_func := App (Inj (inr (ilf_forall l t))) (Abs t P).
Definition fEx l t P : expr typ my_func := App (Inj (inr (ilf_exists l t))) (Abs t P).
Definition fTrue l : expr typ my_func := Inj (inr (ilf_true l)).
Definition mkNat n : expr typ my_func := Inj (inl (N n)).
Definition mkEq t a b : expr typ my_func := App (App (Inj (my_eq t)) a) b.
Print quant_pull.

Definition my_quant_pull := @quant_pull typ _ my_func _ func_to_ilfunc ilfunc_to_func my_eq.
Definition my_rewrite_exs := @rewrite_exs typ _ my_func _ func_to_ilfunc ilfunc_to_func.
 Definition goal :=
 	fAnd tyProp (fTrue tyProp) (fEx tyProp tyNat (mkEq tyNat (Var 0) (mkNat 3))).
 
Check rewrite_exs.
Time Eval vm_compute in my_rewrite_exs goal nil (RGinj (Inj (inr (ilf_entails tyProp) : my_func))).
Print goal.

Fixpoint crazy_goal n :=
	match n with
		| 0 => goal
		| S n => fAnd tyProp (crazy_goal n) (crazy_goal n)
	end.

Time Eval vm_compute in my_quant_pull tyProp (crazy_goal 6).

Example test :
	exists x, x = my_quant_pull tyProp goal.
Proof.
  vm_compute.
  unfold my_quant_pull.
  unfold quant_pull. simpl.
  Transparent rewrite_respects.
  unfold rewrite_respects.
  Opaque rewrite_respects.
  unfold func_to_ilfunc.
  
  pose (rg_bind
          (unifyRG rel_dec
             (RGrespects (RGvar (expr typ my_func) 2)
                (RGrespects (RGvar (expr typ my_func) 1)
                   (RGinj (Inj (ilfunc_to_func (ilf_entails tyProp))))))
             (RGrespects (RGinj (Inj (ilfunc_to_func (ilf_entails tyProp))))
                (RGrespects
                   (RGinj (Inj (ilfunc_to_func (ilf_entails tyProp))))
                   (RGinj (Inj (ilfunc_to_func (ilf_entails tyProp)))))))
          (fun _ : RG (expr typ my_func) =>
           rg_ret ((Inj (ilfunc_to_func (ilf_and tyProp)) : expr typ my_func)))
           {|
          mp := FMapPositive.PositiveMap.empty (RG (expr typ my_func));
          max := 3 |}).
       Eval compute in o.   
       Ltac redfirstmatch :=
       	let rec go x := 
       	match x with 
       		| match ?y with _ => _ end => go y
       		| _ => let x' := eval hnf in x in change x with x'
       	end in
       	match goal with
       		| |- exists y, _ = ?x => go x 
       	end.
       	redfirstmatch.
       	cbv iota beta.
       	redfirstmatch.
  simpl in o.
  cbv in o.
  simpl in o.
  red in o.
  red in m0.
  simpl in m0.
  cbv in m0.
  red.
cbv.
vm_compute.
simpl.
unfold quant_pull.
simpl.
vm_compute.

Definition goal : expr typ func :=
  fAnd (fEx tyNat (fEq_nat (Var 0) (fN 3)))
       (fEx tyNat (fEq_nat (Var 0) (fN 7))).

Time Eval vm_compute in quant_pull goal.


Definition quant_pull' (e : expr typ (ilfunc typ)) : expr typ (ilfunc typ) :=
  match
    interleave (@setoid_rewrite typ (ilfunc typ) (expr typ (ilfunc typ))
                                rel_dec
                                rewrite_exs)
               (fun rw e rvars rg rs =>
                  rw (beta_all (@apps _ _) nil nil e) rvars rg rs)
               10 e nil (RGinj (Inj (Eq tyProp)))
               (rsubst_empty _)
  with
    | None => e
    | Some (e,_) => e
  end.

