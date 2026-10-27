# Lean 4 reference model

An executable model of fresh initialization and all 17 post-constructor
state-changing operations in the [K specification](../k-framework/hcs.k).
It uses only Lean's bundled standard library.

## Build and read

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake build
```

[`lean-toolchain`](lean-toolchain) pins Lean 4.35.0. The default build checks every
module and treats warnings as errors. Proofs use ordinary kernel-checked terms;
there are no `sorry`, `admit`, custom axioms, or `native_decide` proofs.

| Source | Purpose |
| --- | --- |
| [Examples](HederaStablecoin/Examples.lean), [SpendingExamples](HederaStablecoin/SpendingExamples.lean) | Successful and rejected transactions, boundary cases, and mixed traces. |
| [Model](HederaStablecoin/Model.lean) | State, initialization, execution, and reachability. |
| [Balances](HederaStablecoin/Balances.lean), [Allowances](HederaStablecoin/Allowances.lean) | Storage operations and their arithmetic properties. |
| [Invariants](HederaStablecoin/Invariants.lean) | Initialization, preservation, transfer, mint, and burn proofs. |
| [Compliance](HederaStablecoin/Compliance.lean), [Roles](HederaStablecoin/Roles.lean) | Authorization, eligibility, and exact state updates. |
| [Delegation](HederaStablecoin/Delegation.lean), [Enforcement](HederaStablecoin/Enforcement.lean) | Allowances, delegated transfers, and wiping. |

## Execution

`create roles supply` initializes a fresh state. `execute s tx` returns
`.ok next` or `.error reason`, with no successor state on failure. `executeAll`
processes a list in order, stopping at the first error and returning a final state
only if every transaction succeeds. It is a trace evaluator, not an HCS batch API.

Addresses and amounts are natural numbers; arithmetic does not wrap. Balances are
a finite list with zero-default lookup, allowing an explicit finite sum without
Mathlib. Use small symbolic account identifiers when executing examples.
Allowances and compliance flags are total functions. Creation sets allowances to
zero, all accounts unfrozen, KYC true only for the four roles, and `proposedOwner`
to zero (no proposal). Supply belongs to the supply manager.

Below, **compliant** means KYC-approved and unfrozen; **eligible** additionally
means nonzero. Every operation requires an initialized state (a nonzero owner).

| Operation | Guards and effects |
| --- | --- |
| `transfer` | Both accounts compliant; sufficient funds. Self-transfer validates but leaves balances unchanged. |
| `mint`, `burn` | Owner or supply manager; update the current supply manager's balance and supply. Check that balance does not exceed supply; mint also checks the supply bound, burn checks funds. |
| `setKycPassed`, `unfreeze` | Owner or compliance manager; update any target's corresponding flag. |
| `unsetKycPassed`, `freeze` | Same authority; reject all current role accounts as targets. |
| `proposeOwner` | Owner; eligible candidate. Replace the pending proposal without changing ownership. |
| `claimOwnership` | Pending candidate; recheck eligibility, change owner, clear proposal. |
| `changeSupplyManager`, `changeComplianceManager`, `changeEnforcementManager` | Owner; eligible candidate. Reassign one role without moving balances or clearing proposals; roles may overlap. |
| `approveAllowance` | Compliant caller and spender; replace the allowance without an upper bound. |
| `increaseAllowance`, `decreaseAllowance` | Same compliance checks; increase must stay within `maxValue`, decrease requires sufficient allowance. |
| `transferFrom` | Caller, holder, and recipient compliant; sufficient balance and holder-to-caller allowance. Consume allowance even for self-transfers, which leave balances unchanged. |
| `wipe` | Owner or enforcement manager; sufficient target balance. Reduce balance and supply without checking flags or protecting role accounts. |

Flag operations permit repeated calls and zero targets. Only the fields described
above change; other state is preserved.

## Proven properties

```text
sum(balances) = totalSupply
and totalSupply ≤ 2^256 - 1
and roles are nonzero
```

`create_invariant` establishes this invariant. `execute_preserves_invariant` and
`executeAll_preserves_invariant` preserve it across successful transactions and
arbitrary finite transaction lists. `created_reachable_invariant` covers every
state reachable from successful creation. These theorems quantify over states
and traces; concrete examples are additional checks.

Operation theorems establish authorization, guards, exact updates, and preservation
of unrelated accounts. They include compliance rejection even for zero/self
transfers, rechecking ownership candidates, exact allowance consumption, and wipe
effects under supply conservation. There is no global allowance bound because
approval accepts arbitrary natural amounts.

## Relationship to K

This is a manually reconstructed reference model, with no K/Lean correspondence
proof or verification of the Java implementation. The K rejection-rule
[correction](../k-framework/README.md#delegated-transfer-correction) is documented separately.

- Creation requires distinct, nonzero roles and supply at most `maxValue = 2^256 - 1`.
  K explicitly checks nonzero roles and nonnegative supply, but neither distinctness
  nor the upper bound. Its sequential balance writes can overwrite the supply
  allocation when roles overlap. Lean avoids that constructor case;
  `create_roles_distinct` proves initial distinctness. Subsequent role changes may
  overlap, so distinctness is not an invariant.
- Lean only creates fresh states. Repeated construction, metadata, and the separate
  getter API are omitted; modeled state is directly inspectable.
- Natural-number inputs and total lookups abstract K's integers and partial maps.
  Negative inputs and map membership are outside the model. Lean supports aliased
  participants explicitly; correspondence with K's multiple-entry map patterns is
  not established. Error reasons and ordering are Lean API choices.
- Preservation also covers supplied states with arbitrary flags and pending
  proposals, provided the invariant holds. A pending candidate need not remain
  compliant until claiming.
- Wiping inconsistent states may produce negative supply in K. Lean subtraction
  saturates at zero; exact subtraction is proved under supply conservation.
