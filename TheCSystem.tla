----------------------------- MODULE TheCSystem ------------------------------
(*
MODULE TheCSystem implements 'the C system', a causal unicast protocol, described
in

        Michel Raynal, Andre Schiper, and Sam Toueg.
        The causal ordering abstraction and a simple way to implement it.
        Information Processing Letters, 39(6):343–350, September 1991.

We also repair a minor bug in the protocol: if a process delivers a
self-addressed message, the process eventually becomes unable to deliver
messages.
*)

EXTENDS Naturals, FiniteSets, Integers
CONSTANT procs
VARIABLES procState, sentMessages, deliveredMessages
VectorTime == INSTANCE VectorTime WITH procs <- procs

Max(x, y) == IF x > y THEN x ELSE y

(*
The C system has each process maintain two pieces of causal metadata,
`Delivered` and `Sent`.
*)

(*
A `Sent` tracks local knowledge about the number of messages sent between
processes.

A process attaches its `sent` to every message it transmits, and merges the
`sent` from every message it delivers.
*)
Sent == [procs -> [procs -> Nat]]

SentIncr(sent, to, from) == [sent EXCEPT ![to] = [@ EXCEPT ![from] = @ + 1]]

SentMerge(sent, msg) == [to \in procs |-> [from \in procs |->
	LET
		loc == sent[to][from]
			+ IF /\ to = msg.to /\ from = msg.from
			\* fix bug in paper; comment out to violate DeliveryOK
			/\ from # to
			THEN 1 ELSE 0
		env == msg.sent[to][from]
	IN
		Max(loc, env)]]

(*
Delivered is a per-process count of messages "delivered" by this process.
*)
Delivered == [procs -> Nat]

DeliveredIncr(x, from) == [x EXCEPT ![from] = @ + 1 ]

ProcState == [
	\* The number of sends to `p` from `q` when indexed like, `sent[p][q]`.
        sent: Sent,
	\* The number of messages delivered from `p`.
        delivered: Delivered,

        (*
          The time field is not used in or required by the C system; it is used
          only to verify the CausalityOK invariant.
          TODO: consider factoring out into an independent variable.
        *)
        time: VectorTime!T
]

Message == [
	from: procs,
	to:   procs,
	sent: Sent
]

(*
MessageIsDeliverable tests whether delivering a given message would eventually
break causality.

If the test message knows about a message that hasn't yet been received, that
message must have been sent causally-before the test message. And so the
receiving process must delay delivery of the test message until a sufficient
number of messages have been delivered.
*)
MessageIsDeliverable(msg) == \A from \in procs:
	msg.sent[msg.to][from] <= procState[msg.to].delivered[from]

PendingDeliveries == { a \in sentMessages: \A b \in deliveredMessages: a.msg # b.msg }

\* These are not part of the C system. They're used by CausalityOK.
SentMessage      == [ msg: Message, tx: VectorTime!T ]
DeliveredMessage == [ msg: Message, tx: VectorTime!T, rx: VectorTime!T ]

ProcSend ==
	\E from \in procs:
	\E to \in procs:
	LET
		t   == VectorTime!Send(procState[from].time, from)
		msg == [from |-> from,
			to   |-> to,
			sent |-> procState[from].sent]
	IN
		/\ procState' = [procState EXCEPT ![from] = [
			  sent      |-> SentIncr(@.sent, to, from),
			  delivered |-> @.delivered,
			  time      |-> t]]
		/\ sentMessages' = sentMessages \cup {[ msg |-> msg, tx |-> t ]}
		/\ UNCHANGED << deliveredMessages >>


ProcDeliver ==
	\E s \in PendingDeliveries:
	LET
		msg     == s.msg
		from    == msg.from
		to      == msg.to
		pt      == procState[to].time
		mt      == s.tx
		t       == VectorTime!Receive(pt, to, mt)
		sent    == procState[to].sent
		rxmsg   == [msg |-> msg, tx |-> mt, rx |-> t]
	IN
		/\ MessageIsDeliverable(msg)
		/\ procState' = [ procState EXCEPT ![to] = [
			delivered |-> DeliveredIncr(@.delivered, from),
			sent      |-> SentMerge(sent, msg),
			time      |-> t]]
		/\ deliveredMessages' = deliveredMessages \cup { rxmsg }
		/\ UNCHANGED << sentMessages >>

ProcInit ==
	[sent     |-> [to \in procs |-> [from \in procs |-> 0]],
	delivered |-> [from \in procs |-> 0 ],
	time      |-> [p \in procs |-> 0 ]]

ProcsInit == [p \in procs |-> ProcInit]

Init == /\ procState = ProcsInit
	/\ deliveredMessages = {}
	/\ sentMessages = {}

Next == \/ ProcSend
	\/ ProcDeliver

Spec == /\ Init
	/\ [][Next]_<< procState, deliveredMessages, sentMessages >>
	/\ WF_<< procState, deliveredMessages >> (ProcDeliver)
	/\ WF_<< procState, sentMessages >> (ProcSend)

TypeOK ==
	/\ procState \in [ procs -> ProcState ]
	/\ \A msg \in sentMessages: msg \in SentMessage
	/\ \A msg \in deliveredMessages: msg \in DeliveredMessage

DeliveryOK == PendingDeliveries = {} \/ ENABLED ProcDeliver

CausalityOK ==
	\A m \in deliveredMessages:
	\A n \in deliveredMessages \ {m}:
	(n.msg.to = m.msg.to) =>
		(VectorTime!Before(m.tx, n.tx) => VectorTime!Before(m.rx, n.rx))
====
