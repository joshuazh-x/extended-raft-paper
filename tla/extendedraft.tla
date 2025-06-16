--------------------------------- MODULE extendedraft ---------------------------------
\* This is the formal specification for the extended Raft consensus algorithm.
\* <TODO: Copyright Info>
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC, Bags, SequencesExt

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* ID of the witness
CONSTANTS WitnessServer

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          RequestWitnessVoteRequest, AppendEntriesToWitnessRequest

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. 
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* The set of log entries that are acknowledged by witness, e.g. not shortcut replication. 
\* This is used to assist invariant and does not exist in real implementation.
VARIABLE witnessAcks

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
\* Leader's replication set
VARIABLE replicationSet
\* Leader's subterm number
VARIABLE currentSubterm
\* The latest subterm that this leader has written to the witness
VARIABLE witnessSubterm
leaderVars == <<nextIndex, matchIndex, elections, 
                replicationSet, currentSubterm, witnessSubterm, witnessAcks>>

\* The following variables are persisted only on witness:
\* The latest replication set sent from leader
VARIABLE witnessReplicationSet
\* The latest term of replicated log entry
VARIABLE witnessLastLogTerm
\* The latest subterm of replicated log entry
VARIABLE witnessLastLogSubterm
witnessVars == <<witnessReplicationSet, 
                 witnessLastLogTerm, witnessLastLogSubterm>>


\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, witnessVars>>

----
\* Helpers

NonWitnessServer == Server \ {WitnessServer}

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The set of all replication sets for each server. 
ReplicationSets == 
    [ i \in NonWitnessServer |-> 
        { s \in SUBSET(Server) : 
            /\ i \in s
            /\ Cardinality(s) = Cardinality(NonWitnessServer) } ]
                                         

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* The subterm of the last entry in a log, or 0 if the log is empty.
LastSubterm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].subterm

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Add a message to the bag of messages.
SendDirect(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardDirect(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
ReplyDirect(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

Send(m) == SendDirect(m)
Reply(response, request) == ReplyDirect(response, request)
Discard(m) == DiscardDirect(m)

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y
MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

----
\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
                   /\ witnessAcks = {}
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ replicationSet = [i \in Server |-> NonWitnessServer]
                  /\ currentSubterm = [i \in Server |-> 0]
                  /\ witnessSubterm = [i \in Server |-> 0]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitWitnessVars == /\ witnessReplicationSet = NonWitnessServer
                   /\ witnessLastLogTerm = 0
                   /\ witnessLastLogSubterm = 0
Init == /\ messages = EmptyBag
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitWitnessVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ i              /= WitnessServer
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ currentSubterm' = [currentSubterm EXCEPT ![i] = 0]
    /\ replicationSet' = [replicationSet EXCEPT ![i] = NonWitnessServer]
    /\ witnessSubterm' = [witnessSubterm EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, commitIndex, witnessAcks, votedFor, log, elections, witnessVars>>

\* Server i times out and starts a new election.
Timeout(i) == /\ i /= WitnessServer
              /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, witnessVars>>

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j /= WitnessServer
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, witnessVars>>

\* Candidate i sends witness a RequestWitnessVote request.
RequestWitnessVote(i) ==
    /\ state[i] = Candidate
    /\ WitnessServer \notin votesResponded[i]
    /\ (votesGranted[i] \cup {WitnessServer}) \in Quorum
    /\ Send([mtype              |-> RequestWitnessVoteRequest,
             mterm              |-> currentTerm[i],
             mlastLogTerm       |-> LastTerm(log[i]),
             mlastLogSubterm    |-> LastSubterm(log[i]),
             mvotesGranted      |-> votesGranted[i],
             msource            |-> i,
             mdest              |-> WitnessServer])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   witnessVars>>


\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   witnessVars>>

\* Leader i sends witness an AppendEntriesToWitness request with log entry 
\* in current subterm acknowledged by a subquorum in current replication set.
AppendEntriesToWitness(i) ==
    /\ state[i] = Leader
    /\ WitnessServer \in replicationSet[i]
    /\ LET Agree(index) == 
               {i} \cup {k \in replicationSet[i]: matchIndex[i][k] >= index}
           IsAgreed(k)  ==
               /\ log[i][k].term    = currentTerm[i]
               /\ log[i][k].subterm = currentSubterm[i]
               /\ ({WitnessServer} \cup Agree(k)) \in Quorum
           agreeIndexes == { k \in 1..Len(log[i]): IsAgreed(k) }
           lastEntry    == Max(agreeIndexes)
       IN /\ agreeIndexes /= {}
          /\ \/ \* witnessSubterm never exceeds currentSubterm following specification
                /\ currentSubterm[i] > witnessSubterm[i]
                /\ Send([mtype           |-> AppendEntriesToWitnessRequest,
                         mterm           |-> currentTerm[i],
                         mlogTerm        |-> log[i][lastEntry].term,
                         mlogSubterm     |-> log[i][lastEntry].subterm,
                         mreplicationSet |-> replicationSet[i],
                         mindex          |-> lastEntry,
                         \* mlog and mentries are used as history variable for
                         \* the proof. They do not exist in a real implementation.
                         mlog            |-> log[i],
                         mentries        |-> SubSeq(log[i], 1, lastEntry),
                         msource         |-> i,
                         mdest           |-> WitnessServer])
             \/ \* shortcut replication
                /\ currentSubterm[i] = witnessSubterm[i]
                /\ Send([mtype           |-> AppendEntriesResponse,
                         mterm           |-> currentTerm[i],
                         msuccess        |-> TRUE,
                         mmatchIndex     |-> lastEntry,
                         msource         |-> WitnessServer,
                         mdest           |-> i,
                         mshortcut       |-> TRUE])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, witnessVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ currentSubterm' = [currentSubterm EXCEPT ![i] = 0]
    /\ replicationSet' = [replicationSet EXCEPT ![i] = NonWitnessServer]
    /\ witnessSubterm' = [witnessSubterm EXCEPT ![i] = 0]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, witnessAcks, votedFor, candidateVars, logVars, witnessVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry  == [term       |-> currentTerm[i],
                      subterm    |-> currentSubterm[i],
                      value      |-> v]
           newLog == Append(log[i], entry)
        IN log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars, 
                   leaderVars, commitIndex, witnessVars>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
                 /\ log[i][Max(agreeIndexes)].subterm = currentSubterm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, witnessVars>>

\* Adjust replication set on leader i. This action updates leader's replication
\* set by a new one. 
AdjustReplicationSet(i, s) ==
    /\ state[i] = Leader
    /\ replicationSet[i] /= s
    /\ replicationSet' = [ replicationSet EXCEPT ![i] = s ]
    /\ currentSubterm' = [currentSubterm EXCEPT ![i] = @ + 1]    
    /\ UNCHANGED <<messages, serverVars, candidateVars, nextIndex, matchIndex,
                   elections, witnessSubterm, witnessAcks, log, commitIndex, 
                   witnessVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, witnessVars>>

\* Witness receives a RequestWitnessVote request from server j with
\* m.mterm <= currentTerm[WitnessServer].
HandleRequestWitnessVoteRequest(j, m) ==
    LET logOk == \/ m.mlastLogTerm > witnessLastLogTerm
                 \/ /\ m.mlastLogTerm = witnessLastLogTerm
                    /\ m.mlastLogSubterm > witnessLastLogSubterm
                 \/ /\ m.mlastLogTerm = witnessLastLogTerm
                    /\ m.mlastLogSubterm = witnessLastLogSubterm
                    /\ m.mvotesGranted \subseteq witnessReplicationSet
        grant == /\ m.mterm = currentTerm[WitnessServer]
                 /\ logOk
                 /\ votedFor[WitnessServer] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[WitnessServer]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![WitnessServer] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[WitnessServer],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[WitnessServer],
                 msource      |-> WitnessServer,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, 
                      logVars, witnessVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, witnessVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              Max({@, m.mcommitIndex})]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, witnessVars>>

\* Witness receives an AppendEntriesToWitnessRequest from server j with
\* m.mterm <= currentTerm[WitnessServer]. 
HandleAppendEntriesToWitnessRequest(j, m) ==
    /\ m.mterm <= currentTerm[WitnessServer]
    /\ \/ \* reject request
          /\ m.mterm < currentTerm[WitnessServer]
          /\ Reply([mtype           |-> AppendEntriesResponse,
                    mterm           |-> currentTerm[WitnessServer],
                    msuccess        |-> FALSE,
                    mmatchIndex     |-> 0,
                    msource         |-> WitnessServer,
                    mdest           |-> j],
                    m)
          /\ UNCHANGED <<serverVars, logVars, witnessVars>>
       \/ \* accept request, always no conflict.
          /\ m.mterm = currentTerm[WitnessServer]
          /\ \/ m.mlogTerm > witnessLastLogTerm
             \/ /\ m.mlogTerm = witnessLastLogTerm
                /\ m.mlogSubterm > witnessLastLogSubterm
          /\ witnessReplicationSet' = m.mreplicationSet
          /\ witnessLastLogTerm' = m.mlogTerm
          /\ witnessLastLogSubterm' = m.mlogSubterm
          \* log will not be modified in real implementation. It is only
          \* used here for the proof.
          /\ log' = [log EXCEPT![WitnessServer] = m.mentries]
          /\ Reply([mtype           |-> AppendEntriesResponse,
                    mterm           |-> currentTerm[WitnessServer],
                    msuccess        |-> TRUE,
                    mmatchIndex     |-> m.mindex,
                    msource         |-> WitnessServer,
                    mdest           |-> j],
                    m)
          /\ UNCHANGED <<serverVars, commitIndex>>
    /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = Max({@, m.mmatchIndex + 1})]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex})]
          /\ IF j = WitnessServer /\ log[i][m.mmatchIndex].subterm = currentSubterm[i] THEN 
                witnessSubterm' = [witnessSubterm EXCEPT ![i] = currentSubterm[i]]
             ELSE 
                UNCHANGED <<witnessSubterm>>
          /\ IF j = WitnessServer /\ "mshortcut" \notin DOMAIN m THEN 
                witnessAcks' = witnessAcks \cup {<<m.mterm, m.mmatchIndex>>}
             ELSE 
                UNCHANGED <<witnessAcks>>
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, witnessSubterm, witnessAcks>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections, 
                   currentSubterm, replicationSet, witnessVars>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, witnessVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, witnessVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestWitnessVoteRequest
          /\ HandleRequestWitnessVoteRequest(j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesToWitnessRequest
          /\ HandleAppendEntriesToWitnessRequest(j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, witnessVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, witnessVars>>

\* History variable that tracks every log ever:
allLogs == {log[i] : i \in Server}
    

----

NextRequestVoteRequest == \E m \in DOMAIN messages : m.mtype = RequestVoteRequest /\ Receive(m)
NextRequestVoteResponse == \E m \in DOMAIN messages : m.mtype = RequestVoteResponse /\ Receive(m)
NextRequestWitnessVoteRequest == \E m \in DOMAIN messages : m.mtype = RequestWitnessVoteRequest /\ Receive(m)
NextAppendEntriesRequest == \E m \in DOMAIN messages : m.mtype = AppendEntriesRequest /\ Receive(m)
NextAppendEntriesResponse == \E m \in DOMAIN messages : m.mtype = AppendEntriesResponse /\ Receive(m)
NextAppendEntriesToWitnessRequest == \E m \in DOMAIN messages : m.mtype = AppendEntriesToWitnessRequest /\ Receive(m)
NextDuplicateMessage == \E m \in DOMAIN messages : DuplicateMessage(m)
NextDropMessage == \E m \in DOMAIN messages : DropMessage(m)

\* Defines how the variables may transition.
Next == \/ \E i \in NonWitnessServer : Restart(i)
        \/ \E i \in NonWitnessServer : Timeout(i) 
        \/ \E i,j \in NonWitnessServer : RequestVote(i, j)
        \/ \E i \in NonWitnessServer : BecomeLeader(i)
        \/ \E i \in NonWitnessServer, v \in Value : ClientRequest(i, v)
        \/ \E i \in NonWitnessServer : AdvanceCommitIndex(i)
        \/ \E i,j \in NonWitnessServer : AppendEntries(i, j)
        \/ \E i \in NonWitnessServer: \E s \in ReplicationSets[i] : AdjustReplicationSet(i, s)
        \/ \E i \in NonWitnessServer : RequestWitnessVote(i)
        \/ \E i \in NonWitnessServer : AppendEntriesToWitness(i)
        \/ NextRequestVoteRequest
        \/ NextRequestVoteResponse
        \/ NextRequestWitnessVoteRequest
        \/ NextAppendEntriesRequest
        \/ NextAppendEntriesResponse
        \/ NextAppendEntriesToWitnessRequest
        \/ NextDuplicateMessage
        \/ NextDropMessage


\* The specification must start with the initial state and transition according
\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars


(***************************************************************************)
(* The main safety properties are below                                    *)
(***************************************************************************)

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == IF i = WitnessServer THEN log[i] ELSE SubSeq(log[i],1,commitIndex[i])

\* The prefix of the log of server i that has been committed up to term x
CommittedTermPrefix(i, x) ==
    \* Only if log of i is non-empty, and if there exists an entry up to the term x
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN
      \* then, we use the subsequence up to the maximum committed term of the leader
      LET maxTermIndex ==
          CHOOSE y \in DOMAIN log[i] :
            /\ log[i][y].term <= x
            /\ \A z \in DOMAIN log[i] : log[i][z].term <= x  => y >= z
      IN SubSeq(log[i], 1, Min({maxTermIndex, commitIndex[i]}))
    \* Otherwise the prefix is the empty tuple
    ELSE << >>

\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Server :
        \/ IsPrefix(Committed(i),Committed(j)) 
        \/ IsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => []LogInv

\* There is only ever one leader per term.  However, this does not preclude multiple
\* servers being leader at the same time, i.e., |{s \in Server: state[s] = Leader}| > 1,
\* as long as each server is leader in a different term.
\*
\* However, this invariant is not violated if two servers *atomically* trade places as
\* leader in the same term, i.e., state' = [state EXCEPT ![s] = Follower, ![t] = Leader]
\* with state[s]=Leader /\ state[t]#Leader.  For that, we would need a suitable action
\* property.
MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* If a candidate has a chance of being elected, there
\* are no log entries with that candidate's term
CandidateTermNotInLogInv ==
    \A i \in Server :
        (/\ state[i] = Candidate
         /\ {j \in Server :
                /\ currentTerm[j] = currentTerm[i]
                /\ votedFor[j] = i
            } \in Quorum
        )
        =>
        \A j \in Server :
        \A n \in DOMAIN log[j] :
             log[j][n].term /= currentTerm[i]

\* A leader always has the greatest index for its current term (this does not
\* mean all of its log will survive if it is not committed)
ElectionSafetyInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            LET FilterAndMax(a, b) == 
                    IF a.term = currentTerm[i] THEN Max({a.term, b}) ELSE b
            IN FoldSeq(FilterAndMax, 0, log[i]) >= FoldSeq(FilterAndMax, 0, log[j])

----
\* Every (index, term) pair determines a log prefix.
\* From page 8 of the Raft paper: "If two logs contain an entry with the same index and term, then the logs are identical in all preceding entries."
LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        \A n \in 1..Min({Len(log[i]), Len(log[j])}) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)
----
\* A leader has all committed entries in its log. This is expressed
\* by LeaderCompleteness below. The inductive invariant for
\* that property is the conjunction of LeaderCompleteness with the
\* other three properties below.

\* All committed entries are contained in the log
\* of at least one server in every quorum if the last committed entry
\* is not shortcut replicated.
QuorumLogInv ==
    \A i \in Server :
        LET committed == Committed(i)
        IN  (\/ LastSubterm(committed) = 0 
             \/ <<LastTerm(committed),Len(committed)>> \in witnessAcks) =>
                \A S \in Quorum :
                    \E j \in S :
                        IsPrefix(Committed(i), log[j])

\* The committed entries in every log are a prefix of the
\* leader's log up to the leader's term (since a next Leader may already be
\* elected without the old leader stepping down yet)
LeaderCompletenessInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            IsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])

\* Each server's term should be equal to or greater than the terms of messages it has sent
MonoTermInv ==
    \A m \in DOMAIN messages: currentTerm[m.msource] >= m.mterm

\* Terms in logs increase monotonically.
MonoLogInv ==
    \A i \in Server :
       log[i] # <<>> => 
           /\ LastTerm(log[i]) <= currentTerm[i]
           /\ \A k \in 1..Len(log[i])-1 : log[i][k].term <= log[i][k+1].term


------------------------------------------------------------------------------
\* Properties

\* Each server's committed log is append-only
CommittedLogAppendOnlyProp ==
    [][\A i \in Server :
        IsPrefix(Committed(i), Committed(i)')]_vars

\* Note that CommittedLogAppendOnlyProp checks for safety violations across time
\* This is a key safety invariant and should always be checked
THEOREM Spec => CommittedLogAppendOnlyProp

\* Each server's commit index is monotonically increasing
\* This is weaker form of CommittedLogAppendOnlyProp so it is not checked by default
MonotonicCommitIndexProp ==
    [][\A i \in Server :
        commitIndex'[i] >= commitIndex[i]]_vars

MonotonicTermProp ==
    [][\A i \in Server :
        currentTerm'[i] >= currentTerm[i]]_vars

MonotonicMatchIndexProp ==
    \* Figure 2, page 4 in the raft paper:
     \* "Volatile state on leaders, reinitialized after election. For each server,
     \*  index of the highest log entry known to be replicated on server. Initialized
     \*  to 0, increases monotonically".  In other words, matchIndex never decrements
     \* unless the current action is a node becoming leader or restarted.
    [][(~ \E i \in NonWitnessServer: <<BecomeLeader(i) \/ Restart(i)>>_vars) => 
            (\A i \in NonWitnessServer, j \in Server : 
                matchIndex'[i][j] >= matchIndex[i][j])]_vars

StateTransitionsProp ==
    [][\A i \in Server :
        /\ state[i] = Nil => state'[i] \in {Nil, Follower}
        /\ state[i] = Follower => state'[i] \in {Follower, Candidate}
        /\ state[i] = Candidate => state'[i] \in {Follower, Candidate, Leader}
        /\ state[i] = Leader => state'[i] \in {Follower, Leader}
        ]_vars

\* Leader commits log entries in during its term and current subterm.
NeverCommitEntryPrevSubtermsProp ==
    [][\A i \in { s \in Server : state[s] = Leader }:
        \* If the commitIndex of a leader changes, the log entry's term and subterm that 
        \* the new commitIndex points to equals the leader's term and subterm, respectively.
        commitIndex'[i] > commitIndex[i] => 
            /\ log[i][commitIndex'[i]].term = currentTerm'[i] 
            /\ log[i][commitIndex'[i]].subterm = currentSubterm'[i]]_vars

LogMatchingProp ==
    \A i, j \in Server : []<>(log[i] = log[j])

LeaderProp ==
    []<><<\E i \in Server : state[i] = Leader>>_vars

===============================================================================

\* Changelog:
\* 2024-01-24:
\* - Extend the algorithm to support witness.
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
