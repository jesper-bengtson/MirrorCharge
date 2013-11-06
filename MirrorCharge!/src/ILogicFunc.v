Require Import ILogic ZArith.
Require Import MirrorCore.Ext.ExprCore.
Require Import MapPositive.
Require Import MirrorCore.Ext.Types.

Inductive ilfunc :=
| ilf_true : typ -> ilfunc
| ilf_false : typ -> ilfunc
| ilf_and : typ -> ilfunc
| ilf_or: typ -> ilfunc
| ilf_impl : typ -> ilfunc
| ilf_exists : typ -> typ -> ilfunc
| ilf_forall : typ -> typ -> ilfunc
| fref (fi : positive).

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
  	      | Some _ => Some (tvArr t (tvArr t t))
  	      | None => None
  	    end
  	  | ilf_forall a t
  	  | ilf_exists a t =>
  	  	match gs t with 
  	  		| Some _ => Some (tvArr (tvArr a t) t)
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
						                            | Some _ => Some (tvArr t (tvArr t t))
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @land _ t 
							| None => tt end
			| ilf_impl t => match gs t as x return (match match x with
						                            | Some _ => Some (tvArr t (tvArr t t))
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t => @limpl _ t 
							| None => tt end
			| ilf_or t => match gs t as x return (match match x with
						                            | Some _ => Some (tvArr t (tvArr t t))
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
						                            | Some _ => Some (tvArr (tvArr a t) t)
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t0 => @lexists _ t0 (typD ts nil a)
							| None => tt end	
         | ilf_forall a t => match gs t as x return (match match x with
						                            | Some _ => Some (tvArr (tvArr a t) t)
						                            | None => None
						                            end with
							| Some t0 => typD ts nil t0
							| None => unit
							end) with 
							| Some t0 => @lforall _ t0 (typD ts nil a)
							| None => tt end end).	
Defined.

  Global Instance RFunc_ilfunc : RFunc (@typD ts) ilfunc :=
  { typeof_func := typeof_func
  ; funcD := funcD
  }.
End RFunc.


Section demo.
  Context {T : Type} {ILO : ILogicOps T}.

  Definition ts : types := (default_type T)::nil.

  Definition logics : logic_ops ts :=
    fun t => match t with
             | tvType 0 => Some ILO
             | _ => None
             end.

  Definition funcs : fun_map ts := PositiveMap.empty _.

  Definition inj_and (p q : expr ilfunc) : expr ilfunc := App (App (Inj (ilf_and (tvType 0))) p) q.
  Definition inj_true : expr ilfunc := Inj (ilf_true (tvType 0)).
  Definition inj_false: expr ilfunc := Inj (ilf_false (tvType 0)).

  Definition tm : expr ilfunc := inj_and inj_true inj_true.

  Require Import MirrorCore.Ext.ExprD.

  (** TODO: Here we run into a problem because the [expr] type is
   ** fixed to the [typ] defined in [MirrorCore.Ext.Types].
   ** - To solve this problem, we need to abstract [expr] with respect to
   **   types.
   **)
   Check @RFunc_ilfunc.
  Eval cbv beta iota zeta delta - [ltrue land] in @exprD ts _ (RFunc_ilfunc ts funcs logics) nil nil tm (tvType 0).

End demo.