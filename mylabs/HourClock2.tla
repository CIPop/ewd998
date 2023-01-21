---- MODULE HourClock2 ----
EXTENDS Integers

VARIABLE Hour, Minute

Init == 
    /\ Hour \in 1..12
    /\ Minute \in 0..59

Next ==
    /\ IF Minute = 59
       THEN 
       /\ Minute' = 0
       /\ IF Hour = 12
            THEN Hour' = 1
            ELSE Hour' = Hour + 1
       ELSE 
        /\ Minute' = Minute + 1
        /\ UNCHANGED Hour

HourIsValid == Hour \in 1..12
MinuteIsValid == Minute \in 0..59


====