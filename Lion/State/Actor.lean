/-
Lion/State/Actor.lean
======================

Actor runtime for message-passing concurrency (Theorems 003, 007).
-/

import Lion.Core.Identifiers
import Lion.Core.SecurityLevel

namespace Lion

/-! =========== MESSAGES (007) =========== -/

/-- Opaque message payload -/
opaque Data : Type

/-- Message between actors -/
structure Message where
  id    : MsgId
  src   : PluginId
  dst   : PluginId
  level : SecurityLevel
  body  : Data
-- Note: Cannot derive Repr due to opaque Data type

/-- Message queue (FIFO) -/
abbrev Queue (α : Type) := List α

/-! =========== ACTOR RUNTIME (003, 007) =========== -/

/-- Runtime state of an actor -/
structure ActorRuntime where
  pending     : Queue Message      -- Router queue (in transit)
  mailbox     : Queue Message      -- Delivered, ready to process
  capacity    : Nat                -- Mailbox capacity (bounded)
  blockedOn   : Option ActorId     -- Wait-for graph edge (003)
  pendingSend : Option Message     -- Message waiting to be delivered
-- Note: Cannot derive Repr due to Message containing opaque Data

namespace ActorRuntime

/-- Empty actor runtime -/
def empty (capacity : Nat) : ActorRuntime where
  pending := []
  mailbox := []
  capacity := capacity
  blockedOn := none
  pendingSend := none

/-- Actor can receive (mailbox not empty) -/
def can_receive (ar : ActorRuntime) : Bool :=
  !ar.mailbox.isEmpty

/-- Actor can send (pending queue not full) -/
def can_send (ar : ActorRuntime) (targetCapacity : Nat) : Bool :=
  ar.pending.length < targetCapacity

/-- Mailbox has space -/
def mailbox_has_space (ar : ActorRuntime) : Bool :=
  ar.mailbox.length < ar.capacity

/-- Enqueue message to pending -/
def enqueue_pending (ar : ActorRuntime) (msg : Message) : ActorRuntime :=
  { ar with pending := ar.pending ++ [msg] }

/-- Deliver message from pending to mailbox -/
def deliver (ar : ActorRuntime) : ActorRuntime :=
  match ar.pending with
  | [] => ar
  | msg :: rest =>
      if ar.mailbox.length < ar.capacity then
        { ar with pending := rest, mailbox := ar.mailbox ++ [msg] }
      else
        ar  -- Drop if full (or block sender)

/-- Consume message from mailbox -/
def consume (ar : ActorRuntime) : ActorRuntime × Option Message :=
  match ar.mailbox with
  | [] => (ar, none)
  | msg :: rest => ({ ar with mailbox := rest }, some msg)

/-- Set blocked state (for deadlock analysis) -/
def set_blocked (ar : ActorRuntime) (on : ActorId) : ActorRuntime :=
  { ar with blockedOn := some on }

/-- Clear blocked state -/
def unblock (ar : ActorRuntime) : ActorRuntime :=
  { ar with blockedOn := none }

end ActorRuntime

/-! =========== WAIT-FOR GRAPH (003) =========== -/

/-- Wait-for graph edge predicate -/
def waits_for (actors : ActorId → ActorRuntime) (a b : ActorId) : Prop :=
  (actors a).blockedOn = some b

/-- No cycles in wait-for graph (deadlock freedom prerequisite) -/
def no_cycles (actors : ActorId → ActorRuntime) : Prop :=
  ∀ a, ¬ ∃ path : List ActorId,
      path.head? = some a ∧
      path.getLast? = some a ∧
      ∀ i, (h : i + 1 < path.length) →
        waits_for actors
          (path.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) h⟩)
          (path.get ⟨i + 1, h⟩)

/-! =========== ACTORRUNTIME OPERATION LEMMAS (Issue #668) =========== -/

namespace ActorRuntime

/-- consume decreases mailbox length when non-empty -/
theorem consume_decreases_mailbox (ar : ActorRuntime)
    (h_nonempty : ar.mailbox ≠ []) :
    (ar.consume.1).mailbox.length < ar.mailbox.length := by
  unfold consume
  match hm : ar.mailbox with
  | [] => exact absurd hm h_nonempty
  | _ :: rest =>
    simp only [List.length_cons]
    omega

/-- consume preserves capacity -/
theorem consume_preserves_capacity (ar : ActorRuntime) :
    (ar.consume.1).capacity = ar.capacity := by
  unfold consume
  cases ar.mailbox <;> rfl

/-- consume preserves blockedOn -/
theorem consume_preserves_blockedOn (ar : ActorRuntime) :
    (ar.consume.1).blockedOn = ar.blockedOn := by
  unfold consume
  cases ar.mailbox <;> rfl

/-- consume preserves pending -/
theorem consume_preserves_pending (ar : ActorRuntime) :
    (ar.consume.1).pending = ar.pending := by
  unfold consume
  cases ar.mailbox <;> rfl

/-- enqueue_pending increases pending length -/
theorem enqueue_pending_increases (ar : ActorRuntime) (msg : Message) :
    (ar.enqueue_pending msg).pending.length = ar.pending.length + 1 := by
  unfold enqueue_pending
  simp [List.length_append]

/-- enqueue_pending preserves mailbox -/
theorem enqueue_pending_preserves_mailbox (ar : ActorRuntime) (msg : Message) :
    (ar.enqueue_pending msg).mailbox = ar.mailbox := by
  unfold enqueue_pending
  rfl

/-- enqueue_pending preserves capacity -/
theorem enqueue_pending_preserves_capacity (ar : ActorRuntime) (msg : Message) :
    (ar.enqueue_pending msg).capacity = ar.capacity := by
  unfold enqueue_pending
  rfl

/-- enqueue_pending preserves blockedOn -/
theorem enqueue_pending_preserves_blockedOn (ar : ActorRuntime) (msg : Message) :
    (ar.enqueue_pending msg).blockedOn = ar.blockedOn := by
  unfold enqueue_pending
  rfl

/-- set_blocked sets blockedOn -/
theorem set_blocked_sets (ar : ActorRuntime) (on : ActorId) :
    (ar.set_blocked on).blockedOn = some on := by
  unfold set_blocked
  rfl

/-- set_blocked preserves mailbox -/
theorem set_blocked_preserves_mailbox (ar : ActorRuntime) (on : ActorId) :
    (ar.set_blocked on).mailbox = ar.mailbox := by
  unfold set_blocked
  rfl

/-- set_blocked preserves pending -/
theorem set_blocked_preserves_pending (ar : ActorRuntime) (on : ActorId) :
    (ar.set_blocked on).pending = ar.pending := by
  unfold set_blocked
  rfl

/-- set_blocked preserves capacity -/
theorem set_blocked_preserves_capacity (ar : ActorRuntime) (on : ActorId) :
    (ar.set_blocked on).capacity = ar.capacity := by
  unfold set_blocked
  rfl

/-- unblock clears blockedOn -/
theorem unblock_clears (ar : ActorRuntime) :
    ar.unblock.blockedOn = none := by
  unfold unblock
  rfl

/-- unblock preserves mailbox -/
theorem unblock_preserves_mailbox (ar : ActorRuntime) :
    ar.unblock.mailbox = ar.mailbox := by
  unfold unblock
  rfl

/-- unblock preserves pending -/
theorem unblock_preserves_pending (ar : ActorRuntime) :
    ar.unblock.pending = ar.pending := by
  unfold unblock
  rfl

/-- unblock preserves capacity -/
theorem unblock_preserves_capacity (ar : ActorRuntime) :
    ar.unblock.capacity = ar.capacity := by
  unfold unblock
  rfl

/-- deliver decreases pending when successful -/
theorem deliver_decreases_pending (ar : ActorRuntime)
    (h_nonempty : ar.pending ≠ [])
    (h_space : ar.mailbox.length < ar.capacity) :
    (ar.deliver).pending.length < ar.pending.length := by
  unfold deliver
  match hp : ar.pending with
  | [] => exact absurd hp h_nonempty
  | _ :: rest =>
    simp only [h_space, if_true]
    simp only [List.length_cons]
    omega

/-- deliver increases mailbox when successful -/
theorem deliver_increases_mailbox (ar : ActorRuntime)
    (h_nonempty : ar.pending ≠ [])
    (h_space : ar.mailbox.length < ar.capacity) :
    (ar.deliver).mailbox.length = ar.mailbox.length + 1 := by
  unfold deliver
  match hp : ar.pending with
  | [] => exact absurd hp h_nonempty
  | _ :: _ =>
    simp only [h_space, if_true]
    simp [List.length_append]

end ActorRuntime

end Lion
