Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import MapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RelDec_typ_eq : RelDec (@eq typ).
  Variable RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq.

  Inductive ilfunc :=
  | ilf_entails (logic : typ)
  | ilf_true (logic : typ)
  | ilf_false (logic : typ)
  | ilf_and (logic : typ)
  | ilf_or (logic : typ)
  | ilf_impl (logic : typ)
  | ilf_exists (arg logic : typ)
  | ilf_forall (arg logic : typ)
  (** It may be a little nicer to remove embed **)
  | ilf_embed (from to : typ).
(* | fref (fi : positive) *)

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
(*		   | fref r, fref r' => r ?[eq] r' *)
		   | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
  Qed.

  (** TODO: Build an ordered map over types **)
  (** the canonical implementation doesn't work!
  Inductive tree : (typ -> Type) -> Type :=
  | Node : forall F, option (F tyProp) ->
           tree (fun t => tree (fun u => F (tyArr t u))) ->
           tree F
  | Empty : forall F, tree F.
  **)

  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD t)).
  Definition embed_ops := forall (t u : typ),
    option (EmbedOp (typD t) (typD u)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | Some T => @ILogic _ T
                | None => True
              end.
  Definition embed_opsOk (ls : logic_ops) (es : embed_ops) : Prop :=
    forall t t',
      match ls t , ls t' , es t t' return Prop with
        | Some a , Some b , Some T => @Embed _ a _ _ T
        | _ , _ , _ => True
      end.

  Variable gs : logic_ops.
  Variable es : embed_ops.

  Variable Typ2_tyArr : Typ2 _ Fun.
  Variable Typ0_tyProp : Typ0 _ Prop.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

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
    end.

  Definition typ2_cast_bin (a b c : typ)
  : (typD a -> typD b -> typD c) -> typD (tyArr a (tyArr b c)) :=
    fun f =>
      match eq_sym (typ2_cast a (tyArr b c)) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast b c) in _ = t
                           return _ -> t with
                       | eq_refl => f
                     end
        end.

  Definition typ2_cast_quant (a b c : typ)
  : ((typD a -> typD b) -> typD c) -> typD (tyArr (tyArr a b) c) :=
    fun f =>
      match eq_sym (typ2_cast (tyArr a b) c) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast a b) in _ = t
                           return t -> _ with
                       | eq_refl => f
                     end
      end.

  Definition funcD (f : ilfunc) :
    match typeof_func f with
      | Some t => typD t
      | None => unit
    end.
  refine (
    match f as f
          return match typeof_func f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | ilf_true t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some t
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => @ltrue _ t
	  | None => tt
        end
      | ilf_false t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some t
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => @lfalse _ t
	  | None => tt
        end
      | ilf_entails t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t tyProp))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some C =>
            match eq_sym (typ2_cast t (tyArr t tyProp)) in _ = t
                  return t with
              | eq_refl =>
                match eq_sym (typ2_cast t tyProp) in _ = t
                      return _ -> t with
                  | eq_refl =>
                    match eq_sym (typ0_cast (F := Prop)) in _ = t
                          return _ -> _ -> t
                    with
                      | eq_refl => @lentails _ _
                    end
                end
            end
	  | None => tt
        end
      | ilf_and t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@land _ _)
	  | None => tt
        end
      | ilf_impl t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@limpl _ _)
	  | None => tt
        end
      | ilf_or t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@lor _ _)
	  | None => tt
        end
      | ilf_exists a t =>
        match gs t as x return (match match x with
					| Some _ => Some (tyArr (tyArr a t) t)
					| None => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | Some t0 => typ2_cast_quant _ _ _ (@lexists _ _ _)
	  | None => tt
        end
      | ilf_forall a t =>
        match gs t as x return (match match x with
					| Some _ => Some (tyArr (tyArr a t) t)
					| None => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | Some t0 => typ2_cast_quant _ _ _ (@lforall _ _ _)
	  | None => tt
        end
      | ilf_embed t u =>
        match es t u as x
              return match match x with
			     | Some _ => Some (tyArr t u)
			     | None => None
			   end with
		       | Some t0 => typD t0
		       | None => unit
		     end
        with
	  | Some t0 =>
            match eq_sym (typ2_cast t u) in _ = t return t
            with
              | eq_refl => @embed _ _ _
            end
	  | None => tt
        end
    end).
  Defined.

  Global Instance RSym_ilfunc : RSym ilfunc :=
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

End typed.

(*
Section RFunc_ctor.
  Variable ts : types.

  Record tc_logic_opt : Type :=
  { logic_typ : typ
  ; logicD : ILogicOps (typD ts nil logic_typ) }.
  Definition tc_map := list tc_logic_opt.

  Fixpoint tc_map_to_logic_ops (ls : list tc_logic_opt) : logic_ops ts :=
    match ls with
      | nil => fun _ => None
      | {| logic_typ := lt ; logicD := logic |} :: ls =>
        let otherwise := tc_map_to_logic_ops ls in
        fun t =>
          match typ_eq_odec lt t with
            | Some pf => Some match pf in _ = t return ILogicOps (typD ts nil t) with
                                | eq_refl => logic
                              end
            | None => otherwise t
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

  Fixpoint embed_map_to_embed_ops (ls : embed_map) : embed_ops ts :=
    match ls with
      | nil => fun _ _ => None
      | {| embed_from := ef ; embed_to := et ; embedD := embed |} :: ls =>
        let otherwise := embed_map_to_embed_ops ls in
        fun t u =>
          match typ_eq_odec ef t , typ_eq_odec et u with
            | Some pf , Some pf' =>
              Some match pf in _ = t , pf' in _ = u
                         return EmbedOp (typD ts nil t) (typD ts nil u) with
                     | eq_refl , eq_refl => embed
                   end
            | _ , _ => otherwise t u
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
    { red. simpl. intros. forward. }
    { red. simpl. forward. simpl in *.
      specialize (IHForall t0 t').
      rewrite H3 in *. rewrite H4 in *.
      destruct (typ_eq_odec embed_from0 t0); try rewrite H6 in *; auto.
      destruct (typ_eq_odec embed_to0 t'); try rewrite H6 in *; auto.
      inv_all; subst.
      rewrite H3 in *. rewrite H4 in *. inv_all; subst.
      assumption. }
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
*)

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