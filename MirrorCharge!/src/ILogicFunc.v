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

	Definition var_logic_map := PositiveMap.t ({x : Type & ILogicOps x}).
	Definition ref_type_map := PositiveMap.t Type.
	
	Fixpoint typD (vlm : var_logic_map) (rtm : ref_type_map) (l : list Type) (t : typ) :=
		match t with
			| tyPred p => match PositiveMap.find p vlm with
						      | Some T => projT1 T
						      | None => Empty_set
						  end
			| tyRef p => match PositiveMap.find p rtm with
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
  
  Definition fun_logic_map := PositiveMap.t function.  
  
  Variable fs : fun_logic_map.
  
  Definition typeof_func (f : ilfunc) : option typ :=
  	match f with
  		| ilf_true i
  		| ilf_false i => match PositiveMap.find i ts with
  							| Some _ => Some (tyPred i)
  							| None => None
  						 end
  		| ilf_and i 
  		| ilf_or i 
  		| ilf_impl i => match PositiveMap.find i ts with
  							| Some _ => Some (tyArr (tyPred i) (tyArr (tyPred i) (tyPred i)))
  							| None => None
  						end
  		| fref i => match PositiveMap.find i fs with
  				    | Some f => Some (ftype f)
  				    | None => None
  				    end
  	end.
  Print RFunc.
  	
  	Definition funcD : forall f : ilfunc,
            match typeof_func f with
            | Some t => typD ts rs nil t
            | None => unit
            end.
    intros f.
    refine (match f as f return (match typeof_func f with
									| Some t => typD ts rs nil t
									| None => unit
									end) with 
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
			| _ => _ 
			end).
			simpl.
  
  
  Definition val : function := F (tvArr tvProp tvProp) not. 
  
Section oneuthoe.
Context {A : Type} `{HIL : ILogic A}.