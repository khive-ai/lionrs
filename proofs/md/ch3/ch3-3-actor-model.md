# 3.3 Actor Model Foundation

_[Previous: WebAssembly Isolation Theorem](ch3-2-theorem-3.1.md) |
[Next: Deadlock Freedom Theorem](ch3-4-theorem-3.2.md)_

---

## 3.3.1 Formal Actor Model Definition

The Lion concurrency system implements a hierarchical actor model designed for
deadlock-free execution.

**Actor System Components**:

$$\text{Actor\_System} = (\text{Actors}, \text{Messages}, \text{Supervisors}, \text{Scheduler})$$

where:

- $\textbf{Actors} = \{A_1, A_2, \ldots, A_n\}$ (concurrent entities, each with
  its own mailbox and state)
- $\textbf{Messages} = \{m: \text{sender} \times \text{receiver} \times \text{payload}\}$
  (asynchronous messages passed between actors)
- $\textbf{Supervisors}$ = a hierarchical tree of fault handlers (each actor may
  have a supervisor to handle its failures)
- $\textbf{Scheduler}$ = a fair task scheduling mechanism with support for
  priorities

### Actor Properties

1. **Isolation**: Each actor has private state, accessible only through message
   passing (no shared memory between actor states)
2. **Asynchrony**: Message sending is non-blocking – senders do not wait for
   receivers to process messages
3. **Supervision**: The actor hierarchy provides fault tolerance via supervisors
   that can restart or manage failing actors without bringing down the system
4. **Fairness**: The scheduler ensures that all actors get CPU time (no actor is
   starved indefinitely, assuming finite tasks)

This actor model is formalized by specifying transition rules for message send,
receive, actor spawn, and actor restart. Each actor processes one message at a
time (ensuring internal sequential consistency). Deadlock-freedom will emerge
from two aspects: absence of blocking waits (actors don't block on receive; they
handle messages when they arrive) and the supervision strategy that prevents
cyclic waiting (since any waiting on a response is managed by either eventual
message delivery or by a supervisor intervening).

## 3.3.2 Message Passing Semantics

### Message Ordering Guarantee

$$\forall A, B \in \text{Actors}, \forall m_1, m_2 \in \text{Messages}: \text{Send}(A, B, m_1) < \text{Send}(A, B, m_2) \Rightarrow \text{Deliver}(B, m_1) < \text{Deliver}(B, m_2)$$

If actor $A$ sends two messages to actor $B$ in order, they will be delivered to
$B$ in the same order (assuming $B$'s mailbox is FIFO for messages from the same
sender). This is a reasonable guarantee to simplify reasoning: actors do not see
messages from a single peer out of order, preventing certain concurrency
anomalies.

### Reliability Guarantee

Lion's messaging uses a persistent queue; thus, if actor $A$ sends a message to
$B$, eventually $B$ will receive it (unless $B$ terminates), assuming the system
makes progress. There is no message loss in the in-memory message queue. (In a
distributed setting, we would incorporate retries or acknowledgments, but within
a single node Lion actor system, message passing is reliable by design.)

### Scheduling and Execution

The scheduler picks an actor that is not currently processing a message (or that
has become unblocked due to a supervisor action) and delivers the next message
in its mailbox. Because actors do not block on internal locks (no shared
memory), the only waiting is for messages. The scheduler ensures that if an
actor has a message, it will eventually get scheduled to process it.

We provide two important formal properties of the scheduling system relevant to
deadlock-freedom:

1. **Progress**: If any actor has an undelivered message in its mailbox, the
   system will eventually schedule that actor to process a message (fair
   scheduling)
2. **Supervision intervention**: If an actor is waiting indefinitely for a
   message that will never arrive (e.g., because the sender died), the
   supervisor detects this and may restart the waiting actor or take corrective
   action

These properties will be used in the deadlock-freedom proof to show that the
system cannot reach a state where all actors are waiting for each other
indefinitely.

---

_Next: [Deadlock Freedom Theorem](ch3-4-theorem-3.2.md)_
