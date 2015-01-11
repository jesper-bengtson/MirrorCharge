Require Import incr_all.

Goal let lst := (tonums (seq NNN)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time run_tactic (incr_all.sym_eval_no_mem 100).
Time (intros; subst;
repeat eapply and_split; eapply prove_Prop; assumption).
Time Qed.