----------------------------- MODULE increment -----------------------------

(*
--algorithm increment

variables x = 5

begin
    Add:
        x := x + 1;
end

algorithm;
*)
=================
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 5
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ x' = x + 1
       /\ pc' = "Done"

Next == Add
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Mon Mar 01 14:51:38 CET 2021 by User
\* Created Mon Mar 01 14:47:25 CET 2021 by User
