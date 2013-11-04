Require Import ILogic ZArith.
Require Import MirrorCore.Ext.ExprCore.
Require Import MapPositive.

Definition logic_index := positive.
Definition ref_index := positive.

Inductive typ :=
| tyPred : logic_index -> typ
| tyRef    : ref_index -> typ
| tyArr  : typ -> typ -> typ.

Section TypeDenotation.

  Definition var_logic_map := PositiveMap.t {x : Type & ILogicOps x}.
  Definition ref_type_map := PositiveMap.t Type.

  Fixpoint typD (vlm : var_logic_map) (rtm : ref_type_map) (l : list Type) (t : typ) :=
    match t with
      | tyPred p =>
        match PositiveMap.find p vlm with
	  | Some T => projT1 T
	  | None => Empty_set
	end
      | tyRef p =>
        match PositiveMap.find p rtm with
	  | Some T => T
	  | None => Empty_set
	end
      | tyArr t1 t2 => typD vlm rtm l t1 -> typD vlm rtm l t2
    end.

End TypeDenotation.

Inductive ilfunc :=
| ilf_true : logic_index -> ilfunc
| ilf_false : logic_index -> ilfunc
| ilf_and : logic_index -> ilfunc
| ilf_or: logic_index -> ilfunc
| ilf_impl : logic_index -> ilfunc
| fref (fi : positive).

Section RFunc.
  Variable ts : var_logic_map.
  Variable rs : ref_type_map.

  Record function := F
  { ftype : typ
  ; fdenote : typD ts rs nil ftype
  }.

  Definition fun_map := PositiveMap.t function.

  Variable fs : fun_map.

  Definition typeof_func (f : ilfunc) : option typ :=
    match f with
      | ilf_true i
      | ilf_false i =>
        match PositiveMap.find i ts with
  	  | Some _ => Some (tyPred i)
  	  | None => None
  	end
      | ilf_and i
      | ilf_or i
      | ilf_impl i =>
        match PositiveMap.find i ts with
  	  | Some _ => Some (tyArr (tyPred i) (tyArr (tyPred i) (tyPred i)))
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
      | Some t => typD ts rs nil t
      | None => unit
    end :=
    match f as f return match typeof_func f with
			  | Some t => typD ts rs nil t
			  | None => unit
			end with
      | ilf_true i =>
	match PositiveMap.find i ts as x
	      return x = PositiveMap.find i ts ->
		     (match match x with
			      | Some _ => Some (tyPred i)
			      | None => None
			    end
		      with
			| Some t => typD ts rs nil t
			| None => unit
		      end)
	with
  	  | Some t => fun pf => match pf in _ = t return
  				      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end with
  				  | eq_refl => @ltrue _ (projT2 t)
  				end
  	  | None => fun _ => tt
  	end eq_refl
      | ilf_false i =>
	match PositiveMap.find i ts as x
	      return x = PositiveMap.find i ts ->
		     (match match x with
			      | Some _ => Some (tyPred i)
			      | None => None
			    end
		      with
			| Some t => typD ts rs nil t
			| None => unit
		      end)
	with
  	  | Some t => fun pf => match pf in _ = t return
  				      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end with
  				  | eq_refl => @lfalse _ (projT2 t)
  				end
  	  | None => fun _ => tt
  	end eq_refl
      | ilf_and i =>
	match PositiveMap.find i ts as x
	      return x = PositiveMap.find i ts ->
		     (match match x with
			      | Some _ => Some (tyArr (tyPred i) (tyArr (tyPred i) (tyPred i)))
			      | None => None
			    end
		      with
			| Some t => typD ts rs nil t
			| None => unit
		      end)
	with
  	  | Some t => fun pf => match pf in _ = t return
  				      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end ->
                                      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end ->
                                      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end
                                with
  				  | eq_refl => @land _ (projT2 t)
  				end
  	  | None => fun _ => tt
  	end eq_refl
      | ilf_or i =>
	match PositiveMap.find i ts as x
	      return x = PositiveMap.find i ts ->
		     (match match x with
			      | Some _ => Some (tyArr (tyPred i) (tyArr (tyPred i) (tyPred i)))
			      | None => None
			    end
		      with
			| Some t => typD ts rs nil t
			| None => unit
		      end)
	with
  	  | Some t => fun pf => match pf in _ = t return
  				      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end ->
                                      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end ->
                                      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end
                                with
  				  | eq_refl => @lor _ (projT2 t)
  				end
  	  | None => fun _ => tt
  	end eq_refl
      | ilf_impl i =>
	match PositiveMap.find i ts as x
	      return x = PositiveMap.find i ts ->
		     (match match x with
			      | Some _ => Some (tyArr (tyPred i) (tyArr (tyPred i) (tyPred i)))
			      | None => None
			    end
		      with
			| Some t => typD ts rs nil t
			| None => unit
		      end)
	with
  	  | Some t => fun pf => match pf in _ = t return
  				      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end ->
                                      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end ->
                                      match t with
                                        | Some T => projT1 T
                                        | None => Empty_set
                                      end
                                with
  				  | eq_refl => @limpl _ (projT2 t)
  				end
  	  | None => fun _ => tt
  	end eq_refl
      | fref fi => 
        match PositiveMap.find fi fs as x
              return match 
                match x with
                  | None => None
                  | Some f0 => Some f0.(ftype)
                end
              with
                | None => unit
                | Some t => typD ts rs nil t
              end
        with
          | None => tt
          | Some f => f.(fdenote)
        end
    end.

  Global Instance RFunc_ilfunc : RFunc (@typD ts rs) ilfunc :=
  { typeof_func := typeof_func
  ; funcD := funcD
  }.
End RFunc.


Section demo.
  Context {T : Type} {ILO : ILogicOps T}.

  Definition logics : var_logic_map :=
    PositiveMap.add 1%positive (@existT _ ILogicOps _ ILO) (PositiveMap.empty _).
  Definition types : ref_type_map :=
    PositiveMap.empty _.

  Definition funcs : fun_map logics types := PositiveMap.empty _.

  Definition tm : expr typ ilfunc :=
    Inj (ilf_true 1%positive).

  Require Import MirrorCore.Ext.ExprD.

  (** TODO: Here we run into a problem because the [expr] type is
   ** fixed to the [typ] defined in [MirrorCore.Ext.Types].
   ** - To solve this problem, we need to abstract [expr] with respect to
   **   types.
   **)
  Eval simpl in @exprD _ _ (RFunc_ilfunc _ _ _) nil nil tm (tyPred 1%positive).

End demo.