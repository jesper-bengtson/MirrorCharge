Require Import Coq.Bool.Bool ZArith.
Require Import ILogic ILEmbed.
Require Import MapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Inductive ilfunc :=
| ilf_entails : typ -> ilfunc
| ilf_true : typ -> ilfunc
| ilf_false : typ -> ilfunc
| ilf_and : typ -> ilfunc
| ilf_or: typ -> ilfunc
| ilf_impl : typ -> ilfunc
| ilf_exists : typ -> typ -> ilfunc
| ilf_forall : typ -> typ -> ilfunc
(** It may be a little nicer to remove embed **)
| ilf_embed (from to : typ)
| fref (fi : positive).

Global Instance RelDec_ilfunc : RelDec (@eq ilfunc) :=
{ rel_dec := fun a b =>
	       match a, b with
		 | ilf_entails t, ilf_entails t'
		 | ilf_true t, ilf_true t'
		 | ilf_false t, ilf_false t'
		 | ilf_and t, ilf_and t'
		 | ilf_or t, ilf_or t'
		 | ilf_impl t, ilf_impl t' => t ?[eq] t'
		 | ilf_forall a t, ilf_forall a' t'
		 | ilf_exists a t, ilf_exists a' t'
		 | ilf_embed a t, ilf_embed a' t' => a ?[eq] a' && t ?[eq] t'
		 | fref r, fref r' => r ?[eq] r'
		 | _, _ => false
	       end
}.

Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
Proof.
  constructor.
  destruct x; destruct y; simpl; intuition; try congruence;
  repeat match goal with
           | _ : context [ ?X ?[ eq ] ?Y ] |- _ =>
             consider (X ?[ eq ] Y); intros; subst
           | |- context [ ?X ?[ eq ] ?Y ] =>
             consider (X ?[ eq ] Y); intros; subst
           | H : _ |- _ =>
             first [ solve [ inversion H ]
                   | inversion H; [ clear H; subst ] ]
         end; intuition.
Qed.

(** TODO: Build an ordered map over types **)
(** the canonical implementation doesn't work!
Inductive tree : (typ -> Type) -> Type :=
| Node : forall F, option (F tyProp) ->
         tree (fun t => tree (fun u => F (tyArr t u))) ->
         tree F
| Empty : forall F, tree F.
**)

Section RFunc.
  Variable ts : types.

  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD ts nil t)).
  Definition embed_ops := forall (t u : typ),
    option (EmbedOp (typD ts nil t) (typD ts nil u)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | Some T => @ILogic _ T
                | None => True
              end.
  Definition embed_opsOk (ls : logic_ops) (es : embed_ops) : Prop :=
    forall t t',
      match ls t , ls t' , es t t' return Prop with
        | Some a , Some b , Some T => @Embed _ _ _ _ T
        | _ , _ , _ => True
      end.

  Record function := F
  { ftype : typ
  ; fdenote : typD ts nil ftype
  }.

  Definition fun_map := PositiveMap.t function.

  Variable fs : fun_map.
  Variable gs : logic_ops.
  Variable es : embed_ops.

  Definition typeof_func (f : ilfunc) : option typ :=
    match f with
      | ilf_true t
      | ilf_false t =>
        match gs t with
   	  | Some _ => Some t
  	  | None => None
  	end
      | ilf_entails t =>
        match gs t with
  	  | Some _ => Some (tyArr t (tyArr t tyProp))
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
      | ilf_embed a b =>
        match es a b with
          | None => None
          | Some _ => Some (tyArr a b)
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
    refine (match f as f
                  return match typeof_func f with
			   | Some t => typD ts nil t
			   | None => unit
			 end
	    with
	      | ilf_true t => match gs t as x
                                    return (match match x with
						    | Some _ => Some t
						    | None => None
						  end with
					      | Some t0 => typD ts nil t0
					      | None => unit
					    end) with
				| Some t => @ltrue _ t
				| None => tt
                              end
	      | ilf_false t => match gs t as x
                                     return (match match x with
						     | Some _ => Some t
						     | None => None
						   end with
					       | Some t0 => typD ts nil t0
					       | None => unit
					     end) with
				 | Some t => @lfalse _ t
				 | None => tt
                               end
	      | ilf_entails t => match gs t as x
                                       return (match match x with
						       | Some _ => Some (tyArr t (tyArr t tyProp))
						       | None => None
						     end with
					         | Some t0 => typD ts nil t0
					         | None => unit
					       end) with
			           | Some t => @lentails _ t
			           | None => tt
                             end
	      | ilf_and t => match gs t as x
                                   return (match match x with
						   | Some _ => Some (tyArr t (tyArr t t))
						   | None => None
						 end with
					     | Some t0 => typD ts nil t0
					     | None => unit
					   end) with
			       | Some t => @land _ t
			       | None => tt
                             end

	      | ilf_impl t => match gs t as x
                                    return (match match x with
						    | Some _ => Some (tyArr t (tyArr t t))
						    | None => None
						  end with
					      | Some t0 => typD ts nil t0
					      | None => unit
					    end) with
				| Some t => @limpl _ t
				| None => tt
                              end
	      | ilf_or t => match gs t as x
                                  return (match match x with
						  | Some _ => Some (tyArr t (tyArr t t))
						  | None => None
						end with
					    | Some t0 => typD ts nil t0
					    | None => unit
					  end) with
			      | Some t => @lor _ t
			      | None => tt
                            end
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
				    | None => tt
                                  end
              | ilf_forall a t => match gs t as x return (match match x with
						                  | Some _ => Some (tyArr (tyArr a t) t)
						                  | None => None
						                end with
							    | Some t0 => typD ts nil t0
							    | None => unit
							  end) with
				    | Some t0 => @lforall _ t0 (typD ts nil a)
				    | None => tt
                                  end
              | ilf_embed t u =>
                match es t u as x
                      return match match x with
				     | Some _ => Some (tyArr t u)
				     | None => None
				   end with
			       | Some t0 => typD ts nil t0
			       | None => unit
			     end
                with
		  | Some t0 => @embed _ _ t0
		  | None => tt
                end
            end).
  Defined.

  Global Instance RSym_ilfunc : RSym (@typD ts) ilfunc :=
  { typeof_sym := typeof_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_ilfunc : RSymOk RSym_ilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End RFunc.

Section RFunc_ctor.
  Variable ts : types.

  Record tc_logic_opt : Type :=
  { logic_typ : typ
  ; logicD : ILogicOps (typD ts nil logic_typ) }.
  Definition tc_map := list tc_logic_opt.

  Fixpoint tc_map_to_logic_ops (ls : list tc_logic_opt) (t : typ) : option (ILogicOps (typD ts nil t)) :=
    match ls with
      | nil => None
      | {| logic_typ := lt ; logicD := logic |} :: ls =>
        match typ_eq_odec lt t with
          | Some pf => Some match pf in _ = t return ILogicOps (typD ts nil t) with
                              | eq_refl => logic
                            end
          | None => tc_map_to_logic_ops ls t
        end
    end.
  Definition tc_mapOk (t : tc_map) : Prop :=
    @List.Forall tc_logic_opt (fun x => @ILogic _ (logicD x)) t.

  Theorem tc_mapOk_to_logic_opsOk
  : forall t, tc_mapOk t -> logic_opsOk (tc_map_to_logic_ops t).
  Proof.
    induction 1; simpl.
    { red. auto. }
    { red. intros.
      destruct x.
      destruct (typ_eq_odec logic_typ0 g).
      { subst. apply H. }
      { eapply IHForall. } }
  Qed.


  Record embed_opt : Type :=
  { embed_from : typ
  ; embed_to : typ
  ; embedD : EmbedOp (typD ts nil embed_from) (typD ts nil embed_to) }.
  Definition embed_map := list embed_opt.

  Fixpoint embed_map_to_embed_ops (ls : embed_map) (t u: typ) : option (EmbedOp (typD ts nil t) (typD ts nil u)) :=
    match ls with
      | nil => None
      | {| embed_from := ef ; embed_to := et ; embedD := embed |} :: ls =>
        match typ_eq_odec ef t , typ_eq_odec et u with
          | Some pf , Some pf' =>
            Some match pf in _ = t , pf' in _ = u
                       return EmbedOp (typD ts nil t) (typD ts nil u) with
                   | eq_refl , eq_refl => embed
                 end
          | _ , _ => None
        end
    end.
  Definition embed_mapOk (t : tc_map) (e : embed_map) : Prop :=
    let gettc := tc_map_to_logic_ops t in
    @List.Forall _ (fun x =>
                      match gettc x.(embed_from) , gettc x.(embed_to) with
                        | Some a , Some b => @Embed _ a _ b x.(embedD)
                        | _ , _ => False
                      end) e.
  Theorem embed_mapOk_to_embed_opsOk
  : forall t e, embed_mapOk t e ->
                embed_opsOk (tc_map_to_logic_ops t) (embed_map_to_embed_ops e).
  Proof.
    induction 1.
    { red. simpl. intros. Require Import ExtLib.Tactics. forward. }
    { red. simpl. forward.
      inv_all. subst. simpl in *.
      rewrite H1 in *. rewrite H2 in *. inv_all. subst. assumption. }
  Qed.

  Definition RSym_ilfunc_ctor (fm : PositiveMap.t (function ts)) (tm : list tc_logic_opt) (em : list embed_opt)
  : RSym (@typD ts) ilfunc :=
    let to := tc_map_to_logic_ops tm in
    let eo := embed_map_to_embed_ops em in
  {| typeof_sym := @typeof_func ts fm to eo
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := @funcD ts fm to eo
  |}.
End RFunc_ctor.

(*
Section enhanced_resolution.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.

  Fixpoint gs' (t : typ) : option (ILogicOps (typD ts nil t)):=
    match t with
      | tyArr t t' =>
        match gs' t' with
          | Some T => Some _
          | None => None
        end
      | t => gs t
    end.
*)