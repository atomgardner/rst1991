(*
MODULE rst1991 implements 'the C system', a causal unicast protocol, described
in

        Michel Raynal, Andre Schiper, and Sam Toueg.
        The causal ordering abstraction and a simple way to implement it.
        Information Processing Letters, 39(6):343–350, September 1991.

We also show & repair a weakness in the protocol (discovered by Lindsey Kuper):
if a process delivers a self-addressed message, the process eventually becomes
unable to deliver messages.
*)

----------------------------- MODULE rst1991 ------------------------------

EXTENDS Naturals, FiniteSets, Integers

CONSTANT proc
VARIABLES procState, sent, delivered

Max(x, y) == IF x > y THEN x ELSE y

\* A simple vector clock implementation based on Schwarz and Mattern 1992.
VectorClock == [ proc -> Nat ]
VectorClockInternal(p) == [ procState[p].time EXCEPT ![p] = @ + 1 ]
VectorClockSend(p) == VectorClockInternal(p)
VectorClockReceive(receiver, vc) == LET rc == VectorClockInternal(receiver) IN
        [ p \in proc |-> Max(rc[p], vc[p]) ]
VectorClockLessThan(a, b) == /\ a # b
                             /\ \A p \in proc: a[p] =< b[p]

\* The C system.
Delivered == [ proc -> Nat ]
\* TODO: This would almost certainly be nicer as a Cartesian product.
Sent      == [ proc -> Delivered ] \* msg.time[p][q] reads as "to p from q"
ProcState == [
        sent: Sent,
        delivered: Delivered,
        (*
          The time field is not used in or required by the C system; it is used
          only to verify the CausalityOK invariant.
          TODO: consider factoring out into an independent variable.
        *)
        time: VectorClock
]

Message          == [ from: proc, to: proc, time: Sent ]
\* TODO: Probably lots of redundancy here.
SentMessage      == [ msg: Message, tx: VectorClock ]
DeliveredMessage == [ msg: Message, tx: VectorClock, rx: VectorClock ]

\* PendingDeliveries is the set of sent messages that have not yet been
\* delivered.
PendingDeliveries == { a \in sent: \A b \in delivered: a.msg # b.msg }

\* MergeSent uses msgs's causal metadata to update the recipient's local time.
MergeSent(msg) == [ to \in proc |->
        [ from \in proc |->
                Max(
                        procState[msg.to].sent[to][from]
                                + IF /\ to = msg.to
                                     /\ from = msg.from
                                  THEN 1 ELSE 0,
                        msg.time[to][from]
                )
        ]
]

\* MergeSentFixed corrects the merge condition to ensure DeliversOK invariant is
\* not violated.
MergeSentFixed(msg) == [ to \in proc |->
        [ from \in proc |->
                Max(
                        procState[msg.to].sent[to][from]
                                \* Don't bump sent for self-addressed messages.
                                + IF /\ to # from
                                     /\ to = msg.to
                                     /\ from = msg.from
                                  THEN 1 ELSE 0,
                        msg.time[to][from]
                )
        ]
]


\* IsDeliverable is the deliverability condition. A process will not action a
\* pending message unless the deliverability condition is true.
IsDeliverable(msg) == \A q \in proc: msg.time[msg.to][q] <= procState[msg.to].delivered[q]

ProcSend == \E from \in proc:
              \E to \in proc:
                LET   t == VectorClockInternal(from)
                    msg == [
                         from |-> from,
                         to   |-> to,
                         time |-> procState[from].sent
                    ]
                 IN /\ procState' = [ procState EXCEPT ![from] = [
                          sent      |-> [ @.sent EXCEPT ![to] = [ @ EXCEPT ![from] = @ + 1] ],
                          delivered |-> @.delivered,
                          time      |-> t
                     ]]
                    /\ sent' = sent \cup {[ msg |-> msg, tx |-> t ]}
                    /\ UNCHANGED << delivered >>

ProcDeliver == \E m \in PendingDeliveries:
                LET msg == m.msg
                      t == VectorClockReceive(msg.to, m.tx)
                IN
                  /\ IsDeliverable(msg)
                  /\ procState' = [ procState EXCEPT ![msg.to] = [
                          delivered |-> [ procState[msg.to].delivered EXCEPT ![msg.from] = @ + 1 ],
                          sent      |-> MergeSentFixed(msg),
                          time      |-> t
                     ]]
                  /\ delivered' = delivered \cup {[ msg |-> msg, tx |-> m.tx, rx |-> t ]}
                  /\ UNCHANGED << sent >>

Init == /\ procState = [ p \in proc |-> [
                sent      |-> [ to \in proc |-> [ from \in proc |-> 0 ] ],
                delivered |-> [ from \in proc |-> 0 ],
                time      |-> [ x \in proc |-> 0 ]
           ]]
        /\ delivered = {}
        /\ sent = {}

Next == \/ ProcSend
        \/ ProcDeliver

Spec == /\ Init
        /\ [][Next]_<< procState, delivered, sent >>
        /\ WF_<< procState, delivered >> (ProcDeliver)
        /\ WF_<< procState, sent >> (ProcSend)

TypeOK == /\ procState \in [ proc -> ProcState ]
          /\ \A msg \in sent: msg \in SentMessage
          /\ \A msg \in delivered: msg \in DeliveredMessage

DeliveryOK == PendingDeliveries = {} \/ ENABLED ProcDeliver

CausalityOK == \A m \in delivered:
                 \A n \in delivered \ {m}:
                   (n.msg.to = m.msg.to) =>
                       (VectorClockLessThan(m.tx, n.tx) => VectorClockLessThan(m.rx, n.rx))
====
