Require Import incr_all.

Goal let lst := (tonums (seq NNN)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time repeat first [ apply Imp.triple_exL ; apply ILogic.lforallR ; intro
             | apply Imp.Assign_seq_rule
             | apply Imp.Skip_seq_rule
             | apply Imp.Assign_tail_rule
             | apply Imp.Skip_tail_rule ];
eapply Imp.embed_ltrue;
eapply Imp.go_lower_raw;
intros;
autorewrite with reduce_stuff;
repeat (eapply Imp.pull_embed_hyp; intros);
eapply Imp.pull_embed_last_hyp; intros;
subst;
repeat eapply and_split; eapply prove_Prop; assumption.
Time Qed.