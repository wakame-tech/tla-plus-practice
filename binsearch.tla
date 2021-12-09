------------------------------ MODULE binsearch ------------------------------

EXTENDS TLC, Integers, Sequences

MaxInt == 4
Range(f) == { f[x]: x \in DOMAIN f }

PT == INSTANCE PT

\* sort
OrderedSeqOf(set, n) ==
    { seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq): seq[x] >= seq[x-1]    
    }

Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0 THEN 1
        ELSE f[x-1] * 2
    IN f[n]

(*--algorithm min
    variables
        low = 1,
        high = Len(seq),
        seq \in OrderedSeqOf(1..MaxInt, MaxInt),
        target \in 1..MaxInt,
        found_index = 0;
        counter = 0;

    begin
        Search:
            while low <= high do
                counter := counter + 1;
                with
                    m = (low + high) \div 2
                do
                    if seq[m] = target then
                        found_index := m;
                        goto Result;
                    elsif seq[m] < target then
                        low := m + 1;
                    else
                        high := m - 1;
                    end if;
                end with;
            end while;

        Result:
            if Len(seq) > 0 then
                assert Pow2(counter - 1) <= Len(seq);
            end if;
            if target \in PT!Range(seq) then
                assert seq[found_index] = target;
            else
                assert found_index = 0;
            end if;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1f29bdc8" /\ chksum(tla) = "7ca26b10")
VARIABLES low, high, seq, target, found_index, counter, pc

vars == << low, high, seq, target, found_index, counter, pc >>

Init == (* Global variables *)
        /\ low = 1
        /\ high = Len(seq)
        /\ seq \in OrderedSeqOf(1..MaxInt, MaxInt)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ counter' = counter + 1
                     /\ LET m == (low + high) \div 2 IN
                          IF seq[m] = target
                             THEN /\ found_index' = m
                                  /\ pc' = "Result"
                                  /\ UNCHANGED << low, high >>
                             ELSE /\ IF seq[m] < target
                                        THEN /\ low' = m + 1
                                             /\ high' = high
                                        ELSE /\ high' = m - 1
                                             /\ low' = low
                                  /\ pc' = "Search"
                                  /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << low, high, found_index, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter - 1) <= Len(seq), 
                               "Failure of assertion at line 51, column 17.")
                ELSE /\ TRUE
          /\ IF target \in PT!Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 54, column 17.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 56, column 17.")
          /\ pc' = "Done"
          /\ UNCHANGED << low, high, seq, target, found_index, counter >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Search \/ Result
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
