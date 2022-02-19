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

_sync == "sync"
_response == "response"
_updateHist == "updateHist"

sync(guid, value) ==     [nature |-> _sync,       guid |-> guid,    value |-> value]
response(guid, value) == [nature |-> _response,   guid |-> guid,    value |-> value]
updateHist(value) ==     [nature |-> _updateHist, guid |-> NullInt, value |-> value]

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
    \* @type: Int;
    clientPrimary


SERVERS == 1..3
CLIENT == 0

Init == 
    /\ nextGUID = 0
    /\ crashed = [p \in SERVERS |-> FALSE]
    /\ fifo = [p \in ((SERVERS \cup {CLIENT}) \X (SERVERS \cup {CLIENT})) |-> <<>>]
    /\ servers = [p \in (SERVERS \cup {CLIENT}) |-> SERVERS]
    /\ responses = [p \in (SERVERS \cup {CLIENT}) |-> {}]
    /\ value = [p \in (SERVERS \cup {CLIENT}) |-> NullInt]
    /\ clientPrimary = NullInt

Fail ==
    \E p, pCorrect \in SERVERS: 
    /\ p # pCorrect
    (*Always leave at least 1 correct process remaining*)
    /\ ~crashed[pCorrect]
    /\ ~crashed[p]
    /\ UNCHANGED nextGUID
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED responses
    /\ UNCHANGED value
    /\ UNCHANGED clientPrimary

NotifyFail ==
    \E p \in SERVERS \cup {CLIENT}, pCrashed \in SERVERS:
    /\ p # CLIENT => ~crashed[p]
    /\ p # pCrashed
    /\ crashed[pCrashed]
    /\ pCrashed \in servers[p]
    /\ UNCHANGED nextGUID
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ servers' = [servers EXCEPT ![p] = @ \ {pCrashed}]
    /\ UNCHANGED responses
    /\ UNCHANGED value
    /\ UNCHANGED clientPrimary

ReceiveResponse == 
    \E p \in SERVERS \cup {CLIENT}, other \in SERVERS:
    /\ p # CLIENT => ~crashed[p]
    /\ p # other
    /\ 0 < Len(fifo[other, p])
    /\ LET m == Head(fifo[other, p]) IN
        /\ m.nature = _response
        /\ UNCHANGED nextGUID
        /\ UNCHANGED crashed
        /\ fifo' = [ fifo EXCEPT ![other, p] = Tail(@)]
        /\ UNCHANGED servers
        /\ responses' = [responses EXCEPT ![p] = @ \cup {[m|->m, src|->other]}]
        /\ UNCHANGED value
        /\ UNCHANGED clientPrimary
    
ReceiveSync ==
    \E p, primary \in SERVERS:
    /\ ~crashed[p]
    /\ p # primary
    /\ 0 < Len(fifo[primary, p])
    /\ LET m == Head(fifo[primary, p]) IN
        /\ m.nature = _sync
        /\ UNCHANGED nextGUID
        /\ UNCHANGED crashed
        /\ fifo' = [
                fifo EXCEPT
                ![primary, p] = Tail(@),
                ![p, primary] = 
                    CASE primary \in servers[p] -> @ \o <<response(m.guid, m.value)>>
                      [] OTHER                  -> @
                    

            ]
        /\ servers' = [servers EXCEPT ![p] = {e \in @ : primary <= e} ]
        /\ UNCHANGED responses
        /\ value' = [value EXCEPT
                ![p] =
                    CASE primary \in servers[p] -> m.value
                      [] OTHER                  -> @
            ]
        /\ UNCHANGED clientPrimary

PrimaryBeginUpdate ==
    \E p \in SERVERS:
    /\ ~crashed[p]
    /\ 0 < Len(fifo[CLIENT, p])
    /\ LET m == Head(fifo[CLIENT, p]) IN
        /\ m.nature = _updateHist
        /\ nextGUID' = nextGUID + 1
        /\ UNCHANGED crashed
        /\ fifo' = LET
            v == IF value[p] = NullInt THEN m.value ELSE value[p]
            IN
            [
                pair \in ({p} \X (servers[p] \ {p})) |-> fifo[pair] \o <<sync(nextGUID, v)>>
            ] @@ fifo
        /\ servers' = [servers EXCEPT ![p] = {e \in @ : p <= e}]
        /\ UNCHANGED responses
        /\ UNCHANGED value
        /\ UNCHANGED clientPrimary

PrimaryCompleteUpdate ==
    \E p \in SERVERS:
    \E r \in responses[p]:
    /\ ~crashed[p]
    /\ \A other \in servers[p] : (\E r_ \in responses[p] : r_.src = other /\ r_.m.guid = r.m.guid)
    /\ UNCHANGED nextGUID
    /\ UNCHANGED crashed
    /\ fifo' = [fifo EXCEPT ![p, CLIENT] = @ \o <<response(r.m.guid, r.m.value)>>]
    /\ UNCHANGED servers
    /\ responses' = [responses EXCEPT ![p] = @ - {e \in @ : e.m.guid = r.m.guid}]
    /\ value' = [value EXCEPT ![p] = r.m.value]
    /\ UNCHANGED clientPrimary

ClientSend == 
    \E v \in 1..2:
    /\ LET primary == CHOOSE e \in servers[CLIENT] : (\A x \in servers[CLIENT] : e <= x) IN
        /\ UNCHANGED nextGUID
        /\ UNCHANGED crashed
        /\ fifo' = [fifo EXCEPT ![CLIENT, primary] = @ \o <<updateHist(v)>>]
        /\ UNCHANGED servers
        /\ UNCHANGED responses
        /\ UNCHANGED value
        /\ clientPrimary' = primary

ClientGiveup == 
    /\ clientPrimary # NullInt
    /\ clientPrimary \notin servers[CLIENT]
    /\ UNCHANGED nextGUID
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED responses
    /\ UNCHANGED value
    /\ clientPrimary' = NullInt

ClientSucceed == 
    \E r \in responses[CLIENT]:
    /\ UNCHANGED nextGUID
    /\ UNCHANGED crashed
    /\ UNCHANGED fifo
    /\ UNCHANGED servers
    /\ UNCHANGED responses
    /\ value' = [value EXCEPT ![CLIENT] = r.m.value]
    /\ clientPrimary' = 777

Next ==
    \/ Fail
    \/ NotifyFail
    \/ ReceiveResponse
    \/ ReceiveSync
    \/ PrimaryBeginUpdate
    \/ PrimaryCompleteUpdate
    \/ ClientSend
    \/ ClientGiveup
    \/ ClientSucceed


Sanity0 == clientPrimary # 777
Sanity1 == value[1] # 1

Validity ==
    clientPrimary = 777 => 
    \/ (\A p \in SERVERS \cup {CLIENT} : value[p] = 1)
    \/ (\A p \in SERVERS \cup {CLIENT} : value[p] = 2)

Inv == Sanity0



====