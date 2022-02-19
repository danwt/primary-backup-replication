---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache, typedefs
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC, tlcFolds

(*
@typeAlias: PID = Int;

@typeAlias: MSG = [
    nature : Str,
    guid : Int, 
    value : Int
]
*)

NullInt == 0
NullStr == "NullStr"

_sync = "sync"
_response = "response"
_updateHist = "updateHist"

VARIABLES
    \* @type: PID -> Bool;
    crashed,
    \* @type: PID -> Set(PID);
    servers,
    \* @type: <<PID, PID>> -> Seq(MSG);
    fifo


SERVERS == 1..3
CLIENT == 0

Init == x = 1

Fail ==
    \E p, pCorrect \in SERVERS: 
    /\ p # pCorrect
    /\ ~crashed[pCorrect]
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]

NotifyFail ==
    \E p \in SERVERS \cup {CLIENT}, pCrashed \in SERVERS:
    /\ p # pCrashed
    /\ crashed[pCrashed]
    /\ pCrashed \in servers[p]
    /\ servers' = [servers EXCEPT ![p] = @ \ {pCrashed}]
    
CompleteSync ==
    \E p \in SERVERS:
    

Next ==
    \/ Fail
    \/ NotifyFail
    \/ CompleteSync

Inv == x # 1

====