----------------------------- MODULE transfer2 -----------------------------
EXTENDS Naturals, TLC

(*
--algorithm transfer

variables alice_account = 10, bob_account = 10, money \in 1..20;

begin
Transfer:
    if alice_account >= money then
        A: alice_account := alice_account - money;
        B: bob_account := bob_account + money;
    end if;
C: assert alice_account >= 0;

end algorithm*)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == << alice_account, bob_account, money, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in 1..20
        /\ pc = "Transfer"

Transfer == /\ pc = "Transfer"
            /\ IF alice_account >= money
                  THEN /\ pc' = "A"
                  ELSE /\ pc' = "C"
            /\ UNCHANGED << alice_account, bob_account, money >>

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << alice_account, money >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 15, column 4.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money >>

Next == Transfer \/ A \/ B \/ C
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Mar 01 12:05:36 CET 2021 by User
\* Created Mon Mar 01 11:29:24 CET 2021 by User
