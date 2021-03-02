----------------------------- MODULE transfer2 -----------------------------
EXTENDS Naturals, TLC

(*
--algorithm transfer

variables alice_account = 10, bob_account = 10, money = 5;

begin

A: alice_account := alice_account - money;
B: bob_account := bob_account + money;

end algorithm*)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == << alice_account, bob_account, money, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money = 5
        /\ pc = "A"

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, money >>

Next == A \/ B
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Mar 01 11:53:32 CET 2021 by User
\* Created Mon Mar 01 11:29:24 CET 2021 by User
