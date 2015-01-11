Require Import incr_all.

(* full refl *)
Goal let lst := (tonums (seq NNN)) in
         @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time run_tactic (the_final_tactic).
Time Qed.