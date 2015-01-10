Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.BILogic.
Require Import Charge.Logics.ILEmbed.
Require Import Charge.Logics.ILInsts.
Require Import Charge.Logics.BILInsts.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Goal.

Local Open Scope string_scope.

Local Existing Instance ILogicOps_HProp.
Local Existing Instance ILogic_HProp.
Local Existing Instance BILogicOps_HProp.
Local Existing Instance ILogicOps_SProp.
Local Existing Instance ILogic_SProp.
Local Existing Instance BILogicOps_SProp.
Local Existing Instance ILogicOps_lprop.
Local Existing Instance ILogic_lprop.
Local Existing Instance BILOps.
Local Existing Instance BILogic.
Local Existing Instance EmbedOp_Prop_HProp.
Local Existing Instance Embed_Prop_HProp.
Local Existing Instance EmbedOp_HProp_lprop.
Local Existing Instance Embed_HProp_lprop.
Local Existing Instance EmbedOp_Prop_SProp.
Local Existing Instance Embed_Prop_SProp.

Ltac verify :=
  repeat first [ apply triple_exL ; apply lforallR ; intro
               | apply Skip_seq_rule
               | apply Assign_seq_rule
               | apply Skip_tail_rule
               | apply Assign_tail_rule
               | apply Skip_tail_rule ].

Goal ltrue |-- triple ltrue (skips 5) ltrue.
Proof.
unfold skips.
Time verify.
eapply embed_ltrue.
eapply ltrueR.
Time Qed.

Goal ltrue |-- triple ltrue (skips 10) ltrue.
Proof.
unfold skips.
Time verify.
eapply embed_ltrue.
eapply ltrueR.
Time Qed.

Goal ltrue |-- triple ltrue (skips 15) ltrue.
Proof.
unfold skips.
Time verify.
eapply embed_ltrue.
eapply ltrueR.
Time Qed.

Goal ltrue |-- triple ltrue (skips 20) ltrue.
Proof.
unfold skips.
Time verify.
eapply embed_ltrue.
eapply ltrueR.
Time Qed.
