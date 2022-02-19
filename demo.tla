---- MODULE demo ----

VARIABLES
    x,
    y,
    z,
    w

Init ==
    /\ x = 1 
    /\ y = 1
    /\ z = 1
    /\ w = 1

Next == 
    /\ UNCHANGED x
    /\ LET Foo == 42
        IN
        /\ y' = Foo
        /\ UNCHANGED z
    /\ w' = 1

====