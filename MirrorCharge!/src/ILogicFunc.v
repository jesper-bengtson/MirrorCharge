Require Import ILogic ZArith.
Require Import MirrorCore.Ext.ExprCore.
Require Import MapPositive.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.SymI.
Require Import ExtLib.Core.RelDec.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Data.Positive.

Inductive ilfunc :=
| ilf_true : typ -> ilfunc
| ilf_false : typ -> ilfunc
| ilf_and : typ -> ilfunc
| ilf_or: typ -> ilfunc
| ilf_impl : typ -> ilfunc
| ilf_exists : typ -> typ -> ilfunc
| ilf_forall : typ -> typ -> ilfunc
| fref (fi : positive).

Global Instance RelDec_ilfunc : RelDec (@eq ilfunc) := {
	rel_dec := fun a b => 
		match a, b with
			| ilf_true t, ilf_true t'
			| ilf_false t, ilf_false t' 
			| ilf_and t, ilf_and t'
			| ilf_or t, ilf_or t' 
			| ilf_impl t, ilf_impl t' => t ?[eq] t'
			| ilf_forall a t, ilf_forall a' t'
			| ilf_exists a t, ilf_exists a' t' => a ?[eq] a' && t ?[eq] t'
			| fref r, fref r' => r ?[eq] r'
			| _, _ => false
		end
}.

Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc. admit. Qed.

Section RFunc.
  Variable ts : types.
  
  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD ts nil t)).
  
  Record function := F
  { ftype : typ
  ; fdenote : typD ts nil ftype
  }.

  Definition fun_map := PositiveMap.t function.

  Variable fs : fun_map.
  Variable gs : logic_ops.
 
  Definition typeof_func (f : ilfunc) : option typ :=
    match f with
      | ilf_true t
      | ilf_false t =>
        match gs t with
   	      | Some _ => Some t
  	      | None => None
  	    end
      | ilf_and t
      | ilf_or t
      | ilf_impl t =>
        match gs t with
  	      | Some _ => Some (tyArr t (tyArr t t))
  	      | None => None
  	    end
  	  | ilf_forall a t
  	  | ilf_exists a t =>
  	  	match gs t with 
  	  		| Some _ => Some (tyArr (tyArr a t) t)
  	  		| None => None
  	  	end
      | fref i =>
        match PositiveMap.find i fs with
  	      | Some f => Some (ftype f)
  	      | None => None
  	    end
    end.

  Definition funcD (f : ilfunc) :
    match typeof_func f with
      | Some t => typD ts nil t
      | None => unit
    end.
    refine (match f as f return match typeof_func f with
							    | Some t => typD ts nil t
							    | None => unit
			                    end 
			with 
			| ilf_true t => match gs t as x return (match match x with
						                            | Some _ => Some t
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @ltrue _ t 
							| None => tt end
			| ilf_false t => match gs t as x return (match match x with
						                            | Some _ => Some t
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @lfalse _ t 
							| None => tt end
			| ilf_and t => match gs t as x return (match match x with
						                            | Some _ => Some (tyArr t (tyArr t t))
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @land _ t 
							| None => tt end
			| ilf_impl t => match gs t as x return (match match x with
						                            | Some _ => Some (tyArr t (tyArr t t))
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @limpl _ t 
							| None => tt end
			| ilf_or t => match gs t as x return (match match x with
						                            | Some _ => Some (tyArr t (tyArr t t))
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @lor _ t 
							| None => tt end
		| fref fi => 
        match PositiveMap.find fi fs as x
              return match 
                match x with
                  | None => None
                  | Some f0 => Some f0.(ftype)
                end
              with
                | None => unit
                | Some t => typD ts nil t
              end
        with
          | None => tt
          | Some f => f.(fdenote)
        end		
        | ilf_exists a t => match gs t as x return (match match x with
						                            | Some _ => Some (tyArr (tyArr a t) t)
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t0 => @lexists _ t0 (typD ts nil a)
							| None => tt end	
         | ilf_forall a t => match gs t as x return (match match x with
						                            | Some _ => Some (tyArr (tyArr a t) t)
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t0 => @lforall _ t0 (typD ts nil a)
							| None => tt end end).	
Defined.
Print RSym.
  Global Instance RSym_ilfunc : RSym (@typD ts) ilfunc :=
  { typeof_sym := typeof_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.
End RFunc.


Section demo.
  Context {T : Type} {ILO : ILogicOps T}.

  Definition ts : types := (default_type T)::(default_type nat)::nil.

  Definition logics : logic_ops ts :=
    fun t => match t with
             | tyType 0 => Some ILO
             | _ => None
             end.

  Axiom eq_nat : nat -> nat -> T.
  
  Definition eq_nat_emb := F ts (tyArr (tyType 1) (tyArr (tyType 1) (tyType 0))) (eq_nat).

  Definition funcs : fun_map ts := PositiveMap.add (1%positive) (eq_nat_emb) (PositiveMap.empty _).

  Definition inj_and (p q : expr ilfunc) : expr ilfunc := App (App (Inj (ilf_and (tyType 0))) p) q.
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

End demo.