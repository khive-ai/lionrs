---- MODULE CapabilityModel ----
----
---- Lion Microkernel Capability Management System
---- Based on Theorem A1 Theoretical Foundations
---- Issue #33: TLA+ Architecture Theorem A1 Verification
----

EXTENDS TLC, Sequences, FiniteSets, Naturals, LionCore

----
---- Capability System Constants
----

CONSTANTS
  CapabilitySet,       \* Set of all possible capabilities
  AuthoritySet,        \* Set of all possible authorities
  ObjectSet,           \* Set of all protected objects
  MaxCapabilities,     \* Maximum number of capabilities
  MaxDerivationDepth   \* Maximum capability derivation depth

----
---- Capability Type Definitions
----

Capability == [
  id: Nat,
  object: ObjectSet,
  authority: SUBSET AuthoritySet,
  derivation_path: Seq(Nat),
  constraints: SUBSET STRING,
  holder: CoreComponents,
  creation_time: Nat,
  expiration_time: Nat \cup {-1},  \* -1 means no expiration
  revoked: BOOLEAN
]

CapabilityOperation == [
  operation_type: {"Create", "Derive", "Attenuate", "Delegate", "Revoke", "Invoke"},
  source_capability: Nat \cup {-1},  \* -1 for initial creation
  target_capability: Nat \cup {-1},  \* -1 if not applicable
  requester: CoreComponents,
  timestamp: Nat,
  parameters: [STRING -> STRING]
]

CapabilityTransformation == [
  transformation_type: {"Attenuation", "Constraint_Addition", "Time_Restriction"},
  source_authority: SUBSET AuthoritySet,
  target_authority: SUBSET AuthoritySet,
  added_constraints: SUBSET STRING,
  time_bounds: [Nat, Nat]  \* [start, end]
]

----
---- Capability System State
----

VARIABLES
  capability_store,    \* Repository of all capabilities
  capability_holders,  \* Mapping of components to their capabilities
  derivation_graph,    \* Graph of capability derivations
  revocation_list,     \* List of revoked capabilities
  operation_log        \* Log of all capability operations

CapabilitySystemState == [
  active_capabilities: [Nat -> Capability],
  holder_mappings: [CoreComponents -> SUBSET Nat],
  derivation_relationships: [Nat -> SUBSET Nat],
  revoked_capabilities: SUBSET Nat,
  operation_history: Seq(CapabilityOperation)
]

----
---- Fundamental Capability Operations
----

\* Capability Creation (Initial Capabilities Only)
CreateInitialCapability(cap_id, object, authority, holder) ==
  /\ cap_id \notin DOMAIN capability_store.active_capabilities
  /\ object \in ObjectSet
  /\ authority \subseteq AuthoritySet
  /\ holder \in CoreComponents
  /\ holder \in TCB  \* Only TCB can create initial capabilities
  /\ capability_store' = [capability_store EXCEPT 
      !.active_capabilities = @ @@ (cap_id :> [
        id |-> cap_id,
        object |-> object,
        authority |-> authority,
        derivation_path |-> <<>>,
        constraints |-> {},
        holder |-> holder,
        creation_time |-> 0,
        expiration_time |-> -1,
        revoked |-> FALSE
      ]),
      !.holder_mappings = [@ EXCEPT ![holder] = @ \cup {cap_id}],
      !.derivation_relationships = @ @@ (cap_id :> {})
    ]
  /\ operation_log' = Append(operation_log, [
      operation_type |-> "Create",
      source_capability |-> -1,
      target_capability |-> cap_id,
      requester |-> holder,
      timestamp |-> 0,
      parameters |-> [object |-> ToString(object), authority |-> ToString(authority)]
    ])
  /\ UNCHANGED <<capability_holders, derivation_graph, revocation_list>>

\* Capability Derivation with Attenuation
DeriveCapability(parent_id, child_id, new_authority, new_constraints, requester) ==
  /\ parent_id \in DOMAIN capability_store.active_capabilities
  /\ child_id \notin DOMAIN capability_store.active_capabilities
  /\ parent_id \notin capability_store.revoked_capabilities
  /\ new_authority \subseteq capability_store.active_capabilities[parent_id].authority
  /\ requester = capability_store.active_capabilities[parent_id].holder
  /\ Len(capability_store.active_capabilities[parent_id].derivation_path) < MaxDerivationDepth
  /\ capability_store' = [capability_store EXCEPT 
      !.active_capabilities = @ @@ (child_id :> [
        id |-> child_id,
        object |-> capability_store.active_capabilities[parent_id].object,
        authority |-> new_authority,
        derivation_path |-> Append(capability_store.active_capabilities[parent_id].derivation_path, parent_id),
        constraints |-> capability_store.active_capabilities[parent_id].constraints \cup new_constraints,
        holder |-> requester,
        creation_time |-> Len(capability_store.operation_history) + 1,
        expiration_time |-> capability_store.active_capabilities[parent_id].expiration_time,
        revoked |-> FALSE
      ]),
      !.holder_mappings = [@ EXCEPT ![requester] = @ \cup {child_id}],
      !.derivation_relationships = [@ EXCEPT 
        ![parent_id] = @ \cup {child_id},
        ![child_id] = {}
      ]
    ]
  /\ operation_log' = Append(operation_log, [
      operation_type |-> "Derive",
      source_capability |-> parent_id,
      target_capability |-> child_id,
      requester |-> requester,
      timestamp |-> Len(capability_store.operation_history) + 1,
      parameters |-> [authority |-> ToString(new_authority), constraints |-> ToString(new_constraints)]
    ])
  /\ UNCHANGED <<capability_holders, derivation_graph, revocation_list>>

\* Capability Delegation (Transfer to Another Component)
DelegateCapability(cap_id, new_holder, requester) ==
  /\ cap_id \in DOMAIN capability_store.active_capabilities
  /\ cap_id \notin capability_store.revoked_capabilities
  /\ requester = capability_store.active_capabilities[cap_id].holder
  /\ new_holder \in CoreComponents
  /\ new_holder # requester
  /\ capability_store' = [capability_store EXCEPT 
      !.active_capabilities = [@ EXCEPT ![cap_id] = [@ EXCEPT !.holder = new_holder]],
      !.holder_mappings = [@ EXCEPT 
        ![requester] = @ \ {cap_id},
        ![new_holder] = @ \cup {cap_id}
      ]
    ]
  /\ operation_log' = Append(operation_log, [
      operation_type |-> "Delegate",
      source_capability |-> cap_id,
      target_capability |-> cap_id,
      requester |-> requester,
      timestamp |-> Len(capability_store.operation_history) + 1,
      parameters |-> [new_holder |-> ToString(new_holder)]
    ])
  /\ UNCHANGED <<capability_holders, derivation_graph, revocation_list>>

\* Capability Revocation
RevokeCapability(cap_id, requester) ==
  /\ cap_id \in DOMAIN capability_store.active_capabilities
  /\ cap_id \notin capability_store.revoked_capabilities
  /\ \/ requester = capability_store.active_capabilities[cap_id].holder
     \/ requester \in TCB  \* TCB can revoke any capability
     \/ \E parent_id \in DOMAIN capability_store.active_capabilities:
          /\ cap_id \in capability_store.derivation_relationships[parent_id]
          /\ requester = capability_store.active_capabilities[parent_id].holder
  /\ capability_store' = [capability_store EXCEPT 
      !.active_capabilities = [@ EXCEPT ![cap_id] = [@ EXCEPT !.revoked = TRUE]],
      !.revoked_capabilities = @ \cup {cap_id},
      !.holder_mappings = [@ EXCEPT ![capability_store.active_capabilities[cap_id].holder] = @ \ {cap_id}]
    ]
  /\ revocation_list' = revocation_list \cup {cap_id}
  /\ operation_log' = Append(operation_log, [
      operation_type |-> "Revoke",
      source_capability |-> cap_id,
      target_capability |-> -1,
      requester |-> requester,
      timestamp |-> Len(capability_store.operation_history) + 1,
      parameters |-> [reason |-> "Revocation"]
    ])
  /\ UNCHANGED <<capability_holders, derivation_graph>>

\* Capability Invocation
InvokeCapability(cap_id, operation, requester) ==
  /\ cap_id \in DOMAIN capability_store.active_capabilities
  /\ cap_id \notin capability_store.revoked_capabilities
  /\ requester = capability_store.active_capabilities[cap_id].holder
  /\ operation \in capability_store.active_capabilities[cap_id].authority
  /\ \A constraint \in capability_store.active_capabilities[cap_id].constraints:
      EvaluateConstraint(constraint, operation, requester)
  /\ capability_store.active_capabilities[cap_id].expiration_time = -1 \/
     Len(capability_store.operation_history) < capability_store.active_capabilities[cap_id].expiration_time
  /\ operation_log' = Append(operation_log, [
      operation_type |-> "Invoke",
      source_capability |-> cap_id,
      target_capability |-> -1,
      requester |-> requester,
      timestamp |-> Len(capability_store.operation_history) + 1,
      parameters |-> [operation |-> ToString(operation)]
    ])
  /\ UNCHANGED <<capability_store, capability_holders, derivation_graph, revocation_list>>

----
---- Capability Security Properties
----

\* Capability Confinement: Authority can only be attenuated, never amplified
CapabilityConfinement ==
  \A cap_id \in DOMAIN capability_store.active_capabilities:
    \A parent_id \in Range(capability_store.active_capabilities[cap_id].derivation_path):
      capability_store.active_capabilities[cap_id].authority \subseteq 
      capability_store.active_capabilities[parent_id].authority

\* Capability Unforgeability: All capabilities must have valid derivation paths
CapabilityUnforgeability ==
  \A cap_id \in DOMAIN capability_store.active_capabilities:
    \/ capability_store.active_capabilities[cap_id].derivation_path = <<>>  \* Initial capability
    \/ \A parent_id \in Range(capability_store.active_capabilities[cap_id].derivation_path):
         /\ parent_id \in DOMAIN capability_store.active_capabilities
         /\ \E op \in Range(operation_log):
              /\ op.operation_type = "Derive"
              /\ op.source_capability = parent_id
              /\ op.target_capability = cap_id

\* Capability Transitivity: Derivation relationships form a DAG
CapabilityTransitivity ==
  \A cap_id \in DOMAIN capability_store.active_capabilities:
    \A i, j \in 1..Len(capability_store.active_capabilities[cap_id].derivation_path):
      i < j => 
        capability_store.active_capabilities[cap_id].derivation_path[i] #
        capability_store.active_capabilities[cap_id].derivation_path[j]

\* No Capability Cycles: Prevents circular derivations
NoCapabilityCycles ==
  \A cap_id \in DOMAIN capability_store.active_capabilities:
    cap_id \notin Range(capability_store.active_capabilities[cap_id].derivation_path)

----
---- Single-Node Capability Operations
----

\* Direct Capability Operation Execution (No Consensus Needed)
ExecuteCapabilityOperationDirect(operation) ==
  CASE operation.operation_type = "Create" -> 
         CreateInitialCapability(operation.target_capability, 
                                operation.parameters.object, 
                                operation.parameters.authority,
                                operation.requester)
    [] operation.operation_type = "Derive" ->
         DeriveCapability(operation.source_capability,
                         operation.target_capability,
                         operation.parameters.authority,
                         operation.parameters.constraints,
                         operation.requester)
    [] operation.operation_type = "Delegate" ->
         DelegateCapability(operation.source_capability,
                           operation.parameters.new_holder,
                           operation.requester)
    [] operation.operation_type = "Revoke" ->
         RevokeCapability(operation.source_capability, operation.requester)
    [] OTHER -> UNCHANGED <<capability_store, operation_log>>

----
---- Helper Functions
----

EvaluateConstraint(constraint, operation, requester) ==
  TRUE  \* Placeholder for constraint evaluation logic


----
---- Capability System Initialization
----

CapabilityInit ==
  /\ capability_store = [
      active_capabilities |-> [cap \in {} |-> CHOOSE c \in Capability: TRUE],
      holder_mappings |-> [comp \in CoreComponents |-> {}],
      derivation_relationships |-> [cap \in {} |-> {}],
      revoked_capabilities |-> {},
      operation_history |-> <<>>
    ]
  /\ capability_holders = [comp \in CoreComponents |-> {}]
  /\ derivation_graph = [cap \in {} |-> {}]
  /\ revocation_list = {}
  /\ operation_log = <<>>

----
---- Capability System Invariants
----

\* Type Invariant
CapabilityTypeInvariant ==
  /\ capability_store \in CapabilitySystemState
  /\ capability_holders \in [CoreComponents -> SUBSET Nat]
  /\ derivation_graph \in [Nat -> SUBSET Nat]
  /\ revocation_list \in SUBSET Nat
  /\ operation_log \in Seq(CapabilityOperation)

\* Capability System Integrity
CapabilitySystemIntegrity ==
  /\ CapabilityTypeInvariant
  /\ CapabilityConfinement
  /\ CapabilityUnforgeability
  /\ CapabilityTransitivity
  /\ NoCapabilityCycles

\* Capability System Properties
CapabilitySystemProperties ==
  /\ []CapabilitySystemIntegrity
  /\ \A cap_id \in DOMAIN capability_store.active_capabilities:
      <>(\/ cap_id \in capability_store.revoked_capabilities
         \/ \E op \in Range(operation_log): op.source_capability = cap_id)

====