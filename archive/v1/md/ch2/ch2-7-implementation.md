# 2.7 Implementation Perspective

Each of the above theorems has direct correspondence in the implementation:

- Theorem 2.1's guarantees are reflected in how the message-passing system is
  designed (capability handles, cryptographic unforgeability).
- Theorem 2.2 justifies a modular development process: we can verify components
  in isolation and be confident combining them (e.g., each plugin can be
  verified independently, and then a system of plugins inherits their security).
- Theorem 2.3 underpins Lion's decision to eschew ambient global variables or
  default credentials, which is evident in the API (there's no global "admin
  context"; all privileges come from tokens).
- Theorem 2.4 is partially enforced by the Rust compiler (static checks) and by
  lion\_capability at runtime (ensuring no broad capabilities are created when
  narrow ones will do).

Throughout the development of Lion, these formal results guided design choices.
For example, the capability manager's API for delegation requires specifying a
subset of rights (enforcing Lemma 2.4.2), and the policy engine's integration
ensures no operation bypasses a check (supporting Theorem 2.1's policy
compliance considerations).
