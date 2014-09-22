(*
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.Red.
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
  
  Variable inhabited : typ -> bool.
  
Require Import Charge.Logics.ILogic.
  
  Variable inhabited_sound : forall t, inhabited t = true -> Inhabited (typD t).

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
	                  (beta (App P (Var 0)))) (lift 0 1 Q))))))
	      (rg_bind
	        (unifyRG (@rel_dec (expr typ func) _ _) rg 
	                 (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))
	        (fun _ =>
	           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t))) 
	                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_and l))) 
	                  (beta (App P (Var 0)))) (lift 0 1 Q))))))
      	| Some (ilf_or _), Some (ilf_exists l t) =>
      	  let rewrite_rl :=
	      rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
		               (RGflip (RGinj (Inj (ilfunc_to_func (ilf_entails l))))))
		        (fun _ =>
		           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t)))
		                  (Abs t (App (App (Inj ((ilfunc_to_func (ilf_or l)))) 
		                  (beta (App P (Var 0)))) (lift 0 1 Q))))) in
		      match inhabited t with 
		      	| true => rg_plus rewrite_rl 
		      			      (rg_bind
		        (unifyRG (@rel_dec (expr typ func) _ _) rg 
		                 (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))
		        (fun _ =>
		           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t))) 
		                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_or l))) 
		                  (beta (App P (Var 0)))) (lift 0 1 Q))))))
		      	| false => rewrite_rl
		      end
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
	                  (lift 0 1 Q)) (beta (App P (Var 0))))))))
	      (rg_bind
	        (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (Inj (ilfunc_to_func (ilf_entails l))))))
	        (fun _ =>
	           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t)))
	                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_and l))) 
	                  (lift 0 1 Q)) (beta (App P (Var 0))))))))
       | Some (ilf_or _), Some (ilf_exists l t) =>
          let rewrite_rl := 
		      rg_bind
		        (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (Inj (ilfunc_to_func (ilf_entails l))))))
		        (fun _ =>
		           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t)))
		                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_or l))) 
		                  (lift 0 1 Q)) (beta (App P (Var 0))))))) in
		      match inhabited t with
		      	| true => rg_plus rewrite_rl 
					      (rg_bind
					        (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (Inj (ilfunc_to_func (ilf_entails l)))))
					        (fun _ =>
					           rg_ret (App (Inj (ilfunc_to_func (ilf_exists l t))) 
					                  (Abs t (App (App (Inj (ilfunc_to_func (ilf_or l)))
					                  (lift 0 1 Q)) (beta (App P (Var 0)))))))) 
		      	| false => rewrite_rl
		      end
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
    rw_fix 500 (@setoid_rewrite typ func (expr typ func)
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
| tyNat | tyBool | tyEmpty
| tyProp.

Fixpoint typD (t : typ) : Type :=
  match t with
    | tyNat => nat
    | tyBool => bool
    | tyProp => Prop
    | tyEmpty => Empty_set
    | tyArr a b => typD a -> typD b
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
; type_cast := fun a b => match typ_eq_dec a b with
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
; typ2_cast := fun _ _ => eq_refl
; typ2_match := 
    fun T t tr =>
      match t as t return T (TypesI.typD t) -> T (TypesI.typD t) with
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
 ; typ0_cast := eq_refl
 ; typ0_match := fun T t =>
                   match t as t
                         return T Prop -> T (TypesI.typD t) -> T (TypesI.typD t)
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

Definition funcD (f : func)
: match typeof_func f with
    | None => unit
    | Some t => typD t
  end :=
  match f as f return match typeof_func f with
                        | None => unit
                        | Some t => typD t
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
Print typ.

Fixpoint my_inhabited t :=
	match t with
	  | tyArr t1 t2 => my_inhabited t2
	  | tyEmpty => false
	  | _ => true
	end.
	
Definition my_inhabited_sound : forall t, my_inhabited t = true -> Inhabited (typD t).
Proof.
  intros.
  induction t.
  simpl in H. specialize (IHt2 H).
  destruct IHt2.
  inversion cinhabited.
  repeat split. intro. simpl. apply X.
  simpl in *; apply _.
  simpl in *; apply _.
  simpl in *; inversion H.
  simpl in *. repeat split; apply True.
Qed.

Definition my_quant_pull := @quant_pull typ _ my_func _ func_to_ilfunc ilfunc_to_func my_eq my_inhabited.

Definition my_rewrite_exs := @rewrite_exs typ _ my_func _ func_to_ilfunc ilfunc_to_func my_inhabited.
 Definition goal :=
 	fAnd tyProp (fTrue tyProp) (fEx tyProp tyNat (mkEq tyNat (Var 0) (mkNat 3))).
 
 Definition inhabited_pull := fOr tyProp (fEx tyProp tyNat (mkEq tyNat (Var 0) (Var 0)))
 										  (fEx tyProp tyEmpty (mkEq tyEmpty (Var 0) (Var 0))).
 
Time Eval vm_compute in my_quant_pull tyProp inhabited_pull.
 
Check rewrite_exs.
Time Eval vm_compute in my_rewrite_exs goal nil (RGinj (Inj (inr (ilf_entails tyProp) : my_func))).
Print goal.

Fixpoint crazy_goal n :=
	match n with
		| 0 => goal
		| S n => fAnd tyProp (crazy_goal n) (crazy_goal n)
	end.

Time Eval vm_compute in my_quant_pull tyProp (crazy_goal 6).
*)
