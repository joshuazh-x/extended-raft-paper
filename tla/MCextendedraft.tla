--------------------------------- MODULE MCextendedraft ---------------------------------
EXTENDS extendedraft, TLC, Functions, Bags

\* Constraints
MaxLogLength == 6
MaxRestarts == 1
MaxTimeouts == 2
MaxClientRequests == 6
MaxTerms == MaxTimeouts + 1
MaxReplicationSetChange == 3
MaxInFlightMessages == LET card == Cardinality(Server) IN 2 * card * card
UnreliableNetwork == FALSE

R == INSTANCE extendedraft

\* history variable used to constraining the search space
\* restarted: how many times each server restarted
VARIABLE
    history

MCDuplicateMessage(m) ==
    /\ UnreliableNetwork
    /\ R!DuplicateMessage(m)
    /\ UNCHANGED <<history>>

MCDropMessage(m) ==
    /\ UnreliableNetwork
    /\ R!DropMessage(m)
    /\ UNCHANGED <<history>>

MCRestart(i) ==
    /\ history["server"][i]["restarted"] < MaxRestarts
    /\ R!Restart(i)
    /\ history' = [history EXCEPT !["server"][i]["restarted"] = @ + 1]

MCUpdateTerm(i, j, m) ==
    /\ R!UpdateTerm(i, j, m)
    /\ UNCHANGED <<history>>

MCDropStaleResponse(i, j, m) ==
    /\ R!DropStaleResponse(i, j, m)
    /\ UNCHANGED <<history>>

MCHandleAppendEntriesResponse(i, j, m) ==
    /\ R!HandleAppendEntriesResponse(i, j, m)
    /\ UNCHANGED <<history>>

MCHandleAppendEntriesToWitnessRequest(i, m) ==
    /\ R!HandleAppendEntriesToWitnessRequest(i, m)
    /\ UNCHANGED <<history>>

MCHandleAppendEntriesRequest(i, j, m) ==
    /\ R!HandleAppendEntriesRequest(i, j, m)
    /\ UNCHANGED <<history>>

MCHandleRequestVoteResponse(i, j, m) ==
    /\ R!HandleRequestVoteResponse(i, j, m)
    /\ UNCHANGED <<history>>

MCHandleRequestWitnessVoteRequest(i, m) ==
    /\ R!HandleRequestWitnessVoteRequest(i, m)
    /\ UNCHANGED <<history>>

MCHandleRequestVoteRequest(i, j, m) ==
    /\ R!HandleRequestVoteRequest(i, j, m)
    /\ UNCHANGED <<history>>

MCAdjustReplicationSet(i, s) ==
    /\ history["server"][i]["replicationSetChanged"] < MaxReplicationSetChange
    /\ R!AdjustReplicationSet(i, s)
    /\ history' = [history EXCEPT !["server"][i]["replicationSetChanged"] = @ + 1]
    
MCAdvanceCommitIndex(i) ==
    /\ R!AdvanceCommitIndex(i)
    /\ UNCHANGED <<history>>

MCClientRequest(i, v) ==
    /\ history["hadNumClientRequests"] <= MaxClientRequests
    /\ R!ClientRequest(i, v)
    /\ history' = [history EXCEPT !["hadNumClientRequests"] = @ + 1]

MCBecomeLeader(i) ==
    /\ R!BecomeLeader(i)
    /\ history' = [history EXCEPT !["hadNumLeaders"] = @ + 1]

MCAppendEntries(i, j) ==
    /\ R!AppendEntries(i, j)
    /\ UNCHANGED <<history>>

MCAppendEntriesToWitness(i) ==
    /\ R!AppendEntriesToWitness(i)
    /\ UNCHANGED <<history>>

MCRequestVote(i, j) ==
    /\ R!RequestVote(i, j)
    /\ UNCHANGED <<history>>

MCRequestWitnessVote(i) ==
    /\ R!RequestWitnessVote(i)    
    /\ UNCHANGED <<history>>

MCTimeout(i) ==
    /\ history["server"][i]["timeout"] < MaxTimeouts
    /\ R!Timeout(i)
    /\ history' = [history EXCEPT !["server"][i]["timeout"] = @ + 1]

InitHistory == 
    history = [ server |-> [i \in Server |-> [restarted |-> 0, timeout |-> 0, replicationSetChanged |-> 0]],
                global |-> << >>,
                hadNumLeaders |-> 0,
                hadNumClientRequests |-> 0,
                hadReplicationSetChanges |-> 0 ]

MCInit ==
    /\ R!Init
    /\ InitHistory

MCvars ==
    << vars, history >>

MCSpec == 
    /\ MCInit 
    /\ [][Next]_MCvars
    \* fairness
    /\ \E i \in NonWitnessServer : WF_MCvars(Restart(i))
    /\ \E i \in NonWitnessServer : WF_MCvars(Timeout(i))
    /\ \E i,j \in NonWitnessServer : WF_MCvars(RequestVote(i, j))
    /\ \E i \in NonWitnessServer : WF_MCvars(BecomeLeader(i))
    /\ \E i \in NonWitnessServer, v \in Value : WF_MCvars(ClientRequest(i, v))
    /\ \E i \in NonWitnessServer : WF_MCvars(AdvanceCommitIndex(i))
    /\ \E i,j \in NonWitnessServer : WF_MCvars(AppendEntries(i, j))
    /\ \E i \in NonWitnessServer: \E s \in ReplicationSets[i] : WF_MCvars(AdjustReplicationSet(i, s))
    /\ \E i \in NonWitnessServer : WF_MCvars(RequestWitnessVote(i))
    /\ \E i \in NonWitnessServer : WF_MCvars(AppendEntriesToWitness(i))
    /\ WF_MCvars(NextRequestVoteRequest)
    /\ WF_MCvars(NextRequestVoteResponse)
    /\ WF_MCvars(NextRequestWitnessVoteRequest)
    /\ WF_MCvars(NextAppendEntriesRequest)
    /\ WF_MCvars(NextAppendEntriesResponse)
    /\ WF_MCvars(NextAppendEntriesToWitnessRequest)
    /\ WF_MCvars(NextDuplicateMessage)
    /\ WF_MCvars(NextDropMessage)

\* Constraints to make model checking more feasible

BoundedInFlightMessages == messages = EmptyBag \/ BagCardinality(messages) <= MaxInFlightMessages

BoundedLogSize == \A i \in Server: Len(log[i]) <= MaxLogLength

BoundedTerms == \A i \in Server: currentTerm[i] <= MaxTerms

ElectionsUncontested == Cardinality({c \in DOMAIN state : state[c] = Candidate}) <= 1

CleanStartUntilFirstRequest ==
    ((history["hadNumLeaders"] < 1 /\ history["hadNumClientRequests"] < 1)) =>
    /\ \A i \in Server: history["server"][i]["restarted"] = 0
    /\ FoldFunction(+, 0, [i \in Server |-> history["server"][i]["timeout"]]) <= 1        
    /\ ElectionsUncontested

CleanStartUntilTwoLeaders ==
    (history["hadNumLeaders"] < 2) =>
    /\ FoldFunction(+, 0, [i \in Server |-> history["server"][i]["restarted"]]) <= 1      
    /\ FoldFunction(+, 0, [i \in Server |-> history["server"][i]["timeout"]]) <= 2        


-------------------------------------------------------------------------------

===============================================================================
