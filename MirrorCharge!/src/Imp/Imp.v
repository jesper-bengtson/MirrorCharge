Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import ILogic BILogic ILEmbed.
Require Import ILInsts BILInsts.

Set Implicit Arguments.
Set Strict Implicit.

Definition var := string.
Definition value := nat.

Parameter iexpr : Type.
Parameter iConst : value -> iexpr.
Parameter iVar : var -> iexpr.

Parameter icmd : Type.

Parameter locals : Type.
Parameter locals_upd : var -> value -> locals -> locals.
Parameter locals_get : var -> locals -> value.
Parameter HProp : Type.
Instance ILogicOps_HProp : ILogicOps HProp. Admitted.
Instance ILogic_HProp : ILogic HProp. Admitted.
Instance BILogicOps_HProp : BILOperators HProp. Admitted.

Definition lprop := locals -> HProp.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Local Instance ILogicOps_lprop : ILogicOps lprop :=
  @ILFun_Ops locals HProp _.
Local Instance BILOps : BILOperators lprop :=
  @BILFun_Ops _ _ _.
Local Instance EmbedOp_Prop_HProp : EmbedOp Prop HProp. Admitted.
Local Instance EmbedOp_HProp_lprop : EmbedOp HProp lprop :=
  @EmbedILFunDropOp HProp _ (@EmbedOpId _) _.

Parameter eval_iexpr : iexpr -> locals -> value.

Parameter triple : lprop -> icmd -> lprop -> Prop.

(** Sequence **)
Parameter Seq : icmd -> icmd -> icmd.

Axiom Seq_rule
: forall P Q R c1 c2,
    triple P c1 Q ->
    triple Q c2 R ->
    triple P (Seq c1 c2) R.

Axiom SeqA_rule
: forall P Q c1 c2 c3,
    triple P (Seq c1 (Seq c2 c3)) Q ->
    triple P (Seq (Seq c1 c2) c3) Q.

(** Assignment **)
Parameter Assign : var -> iexpr -> icmd.

Axiom Assign_rule
: forall P x e,
    triple P
           (Assign x e)
           (fun l => Exists v' : value,
                    embed (locals_get x l = eval_iexpr e l)
              //\\  P  (locals_upd x v' l)).

(** Read **)
Parameter Read : var -> iexpr -> icmd.

Parameter PtsTo : value -> value -> HProp.

Axiom Read_rule
: forall (P : lprop) x e (v : locals -> value),
    (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue) ->
    triple P
           (Read x e)
           (fun l =>
              Exists v' : value,
                    embed (locals_get x l = v (locals_upd x v' l))
              //\\  P (locals_upd x v' l)).

(** Write **)
Parameter Write : iexpr -> iexpr -> icmd.

(** TODO(gmalecha): This rule might be wrong **)
Axiom Write_rule
: forall (P : lprop) Q p v,
    (P |-- Exists v', ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (pure v') ** Q) ->
    triple P
           (Write p v)
           (ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (eval_iexpr v) ** Q).
