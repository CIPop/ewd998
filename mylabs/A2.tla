---- MODULE A2 ----

EXTENDS Integers, TLC
CONSTANT NumberOfNodes

VARIABLE NodeWorking, TerminationDetected, TokenOwner

Nodes == 1..NumberOfNodes

Terminated == \A node \in Nodes : NodeWorking[node] = FALSE

Init == 
    /\  NodeWorking = [node \in Nodes |-> TRUE]
    /\  TokenOwner = 1
    /\  TerminationDetected = FALSE

\* Following is not going to work in TLC
\*NodeFinishesWork(node) == 
\*    /\ \A n \in Nodes : 
\*        IF n # node THEN 
\*            UNCHANGED NodeWorking[n]
\*        ELSE
\*            NodeWorking'[node] = FALSE
\*    /\ UNCHANGED DOMAIN(NodeWorking) - 

\* Parallel Termination
\* ---------------------
\* Usually not interesting since the events are not observable at the same time in most systems:
\*NodesFinishWork ==
\*       \E nodes \in SUBSET Nodes:
\*            \A node \in nodes:
\*                NodeWorking'[node] = FALSE
\* Also ensure that the domain doesn't change, all other nodes don't change, etc.

NodeFinishedWork(node) ==
\*    /\ NodeWorking' = node :> FALSE @@ NodeWorking \* same but node can be outside of domain!
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED TokenOwner

NodePassesToken(node) == 
    /\ TokenOwner = node
    /\ NodeWorking[node] = FALSE
    /\ UNCHANGED NodeWorking
    /\ IF TokenOwner = NumberOfNodes
       THEN 
        /\ TerminationDetected' = TRUE
        /\ TokenOwner' = 0
       ELSE 
        /\ TokenOwner' = TokenOwner + 1
        /\ UNCHANGED TerminationDetected

DetectTermination == 
    /\ TerminationDetected
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TerminationDetected

Next == 
    \E node \in Nodes : \* Q: but how to do multiple parallel ops?
    \/ NodeFinishedWork(node)
    \/ NodePassesToken(node)
    \/ DetectTermination

====
