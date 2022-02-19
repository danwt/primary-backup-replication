---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache, typedefs
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC, tlcFolds

(*

@typeAlias: PID = Int;

@typeAlias: MSG = [
    nature : Str,
    guid : Int, 
    value : Int
];

@typeAlias: RESPONSE = [
    m : MSG,
    src : PID
];

*)

NullInt == 0
NullStr == "NullStr"

_sync = "sync"
_response = "response"
_updateHist = "updateHist"

sync(guid, value) ==       [nature |-> _sync,       guid |-> guid, value |-> value]
response(guid) ==          [nature |-> _response,   guid |-> guid, value |-> NullInt]
updateHist(guid, value) == [nature |-> _updateHist, guid |-> guid, value |-> value]

VARIABLES
(*Global*)
    \* @type: Int;
    nextGUID,
    \* @type: PID -> Bool;
    crashed,
    \* @type: <<PID, PID>> -> Seq(MSG);
    fifo,
(*Local*)
    \* @type: PID -> Set(PID);
    servers,
    \* @type: PID -> Set(RESPONSE);
    responses,
    \* @type: PID -> Int;
    value,


SERVERS == 1..3
CLIENT == 0

Init == x = 1

Fail ==
    \E p, pCorrect \in SERVERS: 
    /\ p # pCorrect
    /\ ~crashed[pCorrect]
    /\ ~crashed[p]
    /\ UNCHANGED nextGUID
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED responses
    /\ UNCHANGED value

NotifyFail ==
    \E p \in SERVERS \cup {CLIENT}, pCrashed \in SERVERS:
    /\ p # pCrashed
    /\ crashed[pCrashed]
    /\ pCrashed \in servers[p]
    /\ UNCHANGED nextGUID
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ servers' = [servers EXCEPT ![p] = @ \ {pCrashed}]
    /\ UNCHANGED responses
    /\ UNCHANGED value

ReceiveResponse == 
    \E p, other \in SERVERS:
    /\ p # other
    /\ 0 < Len(fifo[other, p])
    /\ LET m == Head(fifo[other, p])
        IN
        /\ m.nature = _response
        /\ UNCHANGED nextGUID
        /\ UNCHANGED crashed
        /\ fifo' = [ fifo EXCEPT ![other, p] = Tail(@)]
        /\ UNCHANGED servers
        /\ responses' = [responses EXCEPT ![p] = @ \cup {[m|->m, src|->other]}]
        /\ UNCHANGED value
    
ReceiveSync ==
    \E p, primary \in SERVERS:
    /\ p # primary
    /\ 0 < Len(fifo[primary, p])
    /\ LET m == Head(fifo[primary, p])
        IN
        /\ m.nature = _sync
        /\ UNCHANGED nextGUID
        /\ UNCHANGED crashed
        /\ fifo' = [
                fifo EXCEPT
                ![primary, p] = Tail(@),
                ![p, primary] = 
                    CASE primary \in servers[p] -> @ \o <<response(m.guid)>>
                      [] OTHER                  -> @
                    

            ]
        /\ servers' = [servers EXCEPT ![p] = @ \ 1..primary ]
        /\ UNCHANGED responses
        /\ value' = [value EXCEPT
                ![p] =
                    CASE primary \in servers[p] -> m.value
                      [] OTHER                  -> @
            ]

Next ==
    \/ Fail
    \/ NotifyFail
    \/ CompleteSync

Inv == x # 1

====