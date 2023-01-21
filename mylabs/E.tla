---- MODULE E ----

EXTENDS Integers, TLC
CONSTANT NumberOfNodes

VARIABLE 
    TerminationDetected,
    Network,
    NodeWorking,
    TokenOwner

vars == <<
    TerminationDetected,
    Network,
    NodeWorking,
    TokenOwner
    >>

Nodes == 1..NumberOfNodes

ATD == INSTANCE A2_NETWORK

TypeOk ==
    /\ NodeWorking \in [Nodes -> {TRUE, FALSE}]
    /\ Network \in [Nodes -> Nat]
    /\ TerminationDetected \in {TRUE, FALSE}
    /\ TokenOwner \in Nodes

Terminated == 
    /\ \A node \in Nodes : NodeWorking[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

Init == 
    /\  NodeWorking = [node \in Nodes |-> TRUE]
    /\  TerminationDetected = FALSE
    /\  Network = [node \in Nodes |-> 0]
    /\  TokenOwner = 1

NodeFinishedWork(node) ==
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED Network
\*    /\ UNCHANGED NodeWorking : Very important - if this is in, a warning is issued and this predicate is ALWAYS FALSE
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED TokenOwner

NodePassesToken(node) == 
    /\ TokenOwner = node
    /\ NodeWorking[node] = FALSE
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED Network
    /\ IF TokenOwner = NumberOfNodes
       THEN 
        /\ TerminationDetected' = TRUE
        /\ UNCHANGED TokenOwner
       ELSE 
        /\ TokenOwner' = TokenOwner + 1
        /\ UNCHANGED TerminationDetected

DetectTermination == 
    /\ TerminationDetected
    /\ UNCHANGED TokenOwner
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TerminationDetected

SendMessage(sourceNode) ==
    \E destinationNode \in Nodes:
    /\ NodeWorking[sourceNode] = TRUE
    /\ Network' = [Network EXCEPT ![destinationNode] = Network[destinationNode] + 1]
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED NodeWorking
    /\ UNCHANGED TokenOwner

NodeReceives(recvNode) ==
    /\ Network[recvNode] > 0
    /\ NodeWorking[recvNode] = FALSE
    /\ Network' = [Network EXCEPT ![recvNode] = Network[recvNode] - 1]
    /\ NodeWorking' = [NodeWorking EXCEPT ![recvNode] = TRUE]
    /\ UNCHANGED TerminationDetected
    /\ UNCHANGED TokenOwner

Next == 
    \E node \in Nodes :
    \/ NodeFinishedWork(node)
    \/ SendMessage(node)
    \/ NodeReceives(node)
    \/ NodePassesToken(node)

NetworkIsFinite ==
    \A node \in Nodes : Network[node] <= 3

NetworkIsValid ==
    \A node \in Nodes : Network[node] >= 0

TerminationDetectionIsStable ==
    [][TerminationDetected => TerminationDetected']_TerminationDetected

\* Because of this invariant, TerminationDetectionIsStable will guarantee stability of Network and Nodes state.
TerminationDetectionIsCorrect == 
    TerminationDetected => Terminated

TerminationIsEventuallyDetected ==
    \* If we are eventually (<>) Terminated then we will eventually (~>) set TerminationDetected to true.
    <>Terminated ~> TerminationDetected


Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

THEOREM Spec => ATD!Spec

Correct ==
    /\ Spec => ATD!Spec
    /\ [](ATD!TypeOk)
    /\ [](TypeOk)

====