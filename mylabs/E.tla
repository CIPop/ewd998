---- MODULE E ----

\* See EWD997.tla as well as https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF for details.

EXTENDS Integers, TLC
CONSTANT NumberOfNodes

VARIABLE 
    TerminationDetectedFromEModule,
    Network,
    NodeWorking,
    TokenOwner,
    TokenCounter,
    TokenColor,
    NodeColors,
    DeltaSendReceive

vars == <<
    TerminationDetectedFromEModule,
    Network,
    NodeWorking,
    TokenOwner,
    TokenCounter,
    TokenColor,
    NodeColors,
    DeltaSendReceive
    >>

Nodes == 1..NumberOfNodes
Colors == {"White", "Black"}

ATD == INSTANCE A2_NETWORK WITH TerminationDetected <- TerminationDetectedFromEModule

TypeOk ==
    /\ NodeWorking \in [Nodes -> {TRUE, FALSE}]
    /\ Network \in [Nodes -> Nat]
    /\ TerminationDetectedFromEModule \in {TRUE, FALSE}
    /\ TokenOwner \in Nodes
    /\ TokenCounter \in Int
    /\ TokenColor \in Colors
    /\ NodeColors \in [Nodes -> Colors]
    /\ DeltaSendReceive \in [Nodes -> Int]

Terminated == 
    /\ \A node \in Nodes : NodeWorking[node] = FALSE
    /\ \A node \in Nodes : Network[node] = 0

Init == 
    /\  TerminationDetectedFromEModule = FALSE
    /\  Network = [node \in Nodes |-> 0]
    /\  NodeWorking = [node \in Nodes |-> TRUE]
    /\  TokenOwner = 1
    /\  TokenCounter = 0
    /\  TokenColor = "Black"
    /\  NodeColors = [node \in Nodes |-> "White"]
    /\  DeltaSendReceive = [node \in Nodes |-> 0 ]

NewRound == 
\* 5) The initiator starts a new round iff the current round is inconclusive:
\*    The round is conclusive IIF TokenColor is White OR TokenCounter is 0
    /\ TokenOwner = 1
    /\ NodeWorking[1] = FALSE
    /\ \/ TokenCounter # 0
       \/ TokenColor = "Black"
\* 6) The initiator whitens itself and the token when initiating a new round
\* 1) The initiator sends the token with a counter  q  initialized to  0  and color white
    /\ NodeColors' = [NodeColors EXCEPT ![1] = "White"]
    /\ TokenCounter' = DeltaSendReceive[1] \* + 0 which is the init of the TokenCounter
    /\ TokenOwner' = 2
    /\ IF NodeColors[TokenOwner'] = "Black" THEN 
        /\ TokenColor' = "Black"
       ELSE 
        /\ TokenColor' = "White"
    /\ UNCHANGED <<TerminationDetectedFromEModule, Network, NodeWorking, DeltaSendReceive>>

DetectTermination == 
    /\ TokenOwner = 1
    /\ TokenCounter = 0
    /\ TokenColor = "White"
    /\ TerminationDetectedFromEModule' = TRUE
    /\  UNCHANGED <<DeltaSendReceive, Network, NodeColors, NodeWorking, TokenColor, TokenCounter, TokenOwner>>

NodeFinishedWork(node) ==
    /\ NodeWorking[node] = TRUE
    /\ NodeWorking' = [NodeWorking EXCEPT ![node] = FALSE]
    /\ UNCHANGED <<Network, TerminationDetectedFromEModule, TokenOwner, DeltaSendReceive, NodeColors, TokenColor, TokenCounter>>

NodePassesToken(node) == 
    /\ node # 1
    /\ TokenOwner = node
    /\ NodeWorking[node] = FALSE
    /\ Network[node] = 0
\* 7) Passing the token whitens the sender node
    /\ NodeColors' = [NodeColors EXCEPT ![node] = "White"]
    /\ UNCHANGED << NodeWorking, Network, DeltaSendReceive, TerminationDetectedFromEModule >>
    /\ TokenCounter' = TokenCounter + DeltaSendReceive[node]
    /\ IF TokenOwner = NumberOfNodes THEN
\* 5) The initiator starts a new round iff the current round is inconclusive
            /\ TokenOwner' = 1
       ELSE 
\* 2) An active node j -owning the token- keeps the token.  When j becomes inactive,
\*    it passes the token to its neighbor with  q = q + counter[j] 
            /\ TokenOwner' = TokenOwner + 1
\* 4) A black node taints the token
    /\ IF NodeColors[TokenOwner] = "Black" THEN     \* I was wrong here initially in checking the next token.
        /\ TokenColor' = "Black"
       ELSE 
        /\ UNCHANGED TokenColor

SendMessage(sourceNode) ==
    \E destinationNode \in Nodes:
        /\ NodeWorking[sourceNode] = TRUE
        /\ Network' = [Network EXCEPT ![destinationNode] = Network[destinationNode] + 1]
    \* 0) Sending a message by node  i  increments a counter at  i [...]
        /\ DeltaSendReceive' = [DeltaSendReceive EXCEPT ![sourceNode] = DeltaSendReceive[sourceNode] + 1]
        /\ UNCHANGED << TerminationDetectedFromEModule, NodeWorking, TokenOwner, NodeColors, TokenColor, TokenCounter>>

NodeReceives(recvNode) ==
    /\ Network[recvNode] > 0
    /\ NodeWorking[recvNode] = FALSE
    /\ Network' = [Network EXCEPT ![recvNode] = Network[recvNode] - 1]
\* 3) Receiving a *message* (not token) blackens the (receiver) node
    /\ NodeColors' = [NodeColors EXCEPT ![recvNode] = "Black"]
    /\ NodeWorking' = [NodeWorking EXCEPT ![recvNode] = TRUE]
\* 0) the receipt of a message decrements i's counter
    /\ DeltaSendReceive' = [DeltaSendReceive EXCEPT ![recvNode] = DeltaSendReceive[recvNode] - 1]
    /\ UNCHANGED << TerminationDetectedFromEModule, TokenOwner, TokenColor, TokenCounter>>

Next == 
    \E node \in Nodes :
        \/ NewRound
        \/ NodeFinishedWork(node)
        \/ SendMessage(node)
        \/ NodeReceives(node)
        \/ NodePassesToken(node)
        \/ DetectTermination

NetworkIsFinite ==
    \A node \in Nodes : Network[node] <= 3

NetworkIsValid ==
    \A node \in Nodes : Network[node] >= 0

DeltaSendReceiveFinite ==
    \A node \in Nodes : DeltaSendReceive[node] <= 2 /\ DeltaSendReceive[node] >= -2

\* Once the termination occured, it can never change.
TerminationDetectionIsStable ==
    [][TerminationDetectedFromEModule => TerminationDetectedFromEModule']_TerminationDetectedFromEModule

\* Because of this invariant, TerminationDetectionIsStable will guarantee stability of Network and Nodes state.
TerminationDetectionIsCorrect == 
    TerminationDetectedFromEModule => Terminated

TerminationIsEventuallyDetected ==
    \* If we are eventually (<>) Terminated then we will eventually (~>) set TerminationDetectedFromEModule to true.
    <>Terminated ~> TerminationDetectedFromEModule


Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ WF_vars(\E node \in Nodes : NodeReceives(node))

ATDSpec == ATD!Spec

\* The ATDSpec is describing a generic termination system. 
\* There is an implicit mapping between the two spec's variables.
THEOREM Spec => ATD!Spec

Correct ==
    /\ [](ATD!TypeOk)
    /\ [](TypeOk)
    /\ ATD!TerminationIsEventuallyDetected
    /\ ATD!TerminationDetectionIsStable
    /\ [](ATD!TerminationDetectionIsCorrect)

\* TESTING:
\* Verification if token owner can be before or after nodes that receive messages.
VerifyThatTokenCanBePastANodeThatReceivesAMessage ==
    [][~(
    /\  DeltaSendReceive[2] = 2
    /\  DeltaSendReceive'[2] = 1
    /\  TokenOwner = 3
    )]_vars

VerifyThatTokenCanBeBeforeANodeThatReceivesAMessage ==
    [][~(
    /\  DeltaSendReceive[2] = 2
    /\  DeltaSendReceive'[2] = 1
    /\  TokenOwner = 1
    )]_vars

MyAlias == [
    Network_Counters |-> << Network, DeltaSendReceive>>,
    NodeWorking_Color |-> <<NodeWorking, NodeColors>>,
    TerminationDetected |-> TerminationDetectedFromEModule,
    Terminated |-> Terminated,
    Token |-> <<TokenOwner,TokenCounter,TokenColor>>,
    NextEnabled |-> ENABLED(Next),
    Token_Next |-> <<TokenOwner,TokenCounter,TokenColor>>',
    Node |-> CHOOSE node \in Nodes : 
                    \/ NewRound
                    \/ NodeFinishedWork(node)
                    \/ SendMessage(node)
                    \/ NodeReceives(node)
                    \/ NodePassesToken(node)
                    \/ DetectTermination

]

====