----------------------------- MODULE VectorTime ------------------------------
(*
This implementation is lifted from Schwarz and Mattern 1992―the Holy Grail
paper.

Vector time tracks cardinalities of causal histories.

Each process maintains its own vector time―an accounting of the local operations
each process has performed.

A process increments its vector time when it performs a local operation―eg,
sending or receiving a message.

A process attaches its vector time to all out-going messages.

Received messages carry information about operations other processes have
performed. A process merges the local and message vector times by taking the max
of their components.
*)
EXTENDS Naturals
CONSTANTS procs

T == [ procs -> Nat ]

LOCAL Max(a, b) == IF a < b THEN b ELSE a

LOCAL Internal(vt, p) == [ vt EXCEPT ![p] = @ + 1 ]

Send(vt, p) == Internal(vt, p)

\* TODO: how to nicely enforce that `m \in SentMessage`?
Receive(vt, to, mt) ==
	LET wt == Internal(vt, to)
	IN [ q \in procs |-> Max(wt[q], mt[q]) ]

Before(a, b) ==
	/\ a # b
	/\ \A p \in procs: a[p] =< b[p]
====
