------------------------------- MODULE flags -------------------------------
EXTENDS TLC, Integers

(*
--algorithm flags

variables f1 \in BOOLEAN, f2 \in BOOLEAN, f3 \in BOOLEAN


begin
  while TRUE do
    with f \in {1, 2, 3} do
      if f = 1 then
        either
          f1 := TRUE;
        or
          f1 := FALSE;
        end either;
      elsif f = 2 then
        either
          f2 := TRUE;
        or
          f2 := FALSE;
        end either;
      else
        either
          f3 := TRUE;
        or
          f3 := FALSE;
        end either;
      end if;
    end with;
  end while;
end

algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES f1, f2, f3

vars == << f1, f2, f3 >>

Init == (* Global variables *)
        /\ f1 \in BOOLEAN
        /\ f2 \in BOOLEAN
        /\ f3 \in BOOLEAN

Next == \E f \in {1, 2, 3}:
          IF f = 1
             THEN /\ \/ /\ f1' = TRUE
                     \/ /\ f1' = FALSE
                  /\ UNCHANGED << f2, f3 >>
             ELSE /\ IF f = 2
                        THEN /\ \/ /\ f2' = TRUE
                                \/ /\ f2' = FALSE
                             /\ f3' = f3
                        ELSE /\ \/ /\ f3' = TRUE
                                \/ /\ f3' = FALSE
                             /\ f2' = f2
                  /\ f1' = f1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 02 09:31:28 CET 2021 by User
\* Created Tue Mar 02 09:23:13 CET 2021 by User
