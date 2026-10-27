import HederaStablecoin.Compliance
import HederaStablecoin.Roles

namespace HederaStablecoin.Examples

private def roles : Roles := ⟨1, 2, 3, 4⟩

/-- Observe supply and balances without comparing the state's flag functions. -/
private def snapshot (result : Except Error State) : Except Error (Nat × Balances) :=
  result.map fun s => (s.totalSupply, s.balances)

private def run (txs : List Transaction) : Except Error (Nat × Balances) :=
  snapshot ((create roles 100).bind fun s => executeAll s txs)

private def runRoles (txs : List Transaction) : Except Error (Roles × Address) :=
  ((create roles 100).bind fun s => executeAll s txs).map fun s => (s.roles, s.proposedOwner)

private def roleAppointments (caller target : Address) : List Transaction :=
  [.proposeOwner caller target, .changeSupplyManager caller target,
   .changeComplianceManager caller target, .changeEnforcementManager caller target]

-- Initialization allocates all tokens to the supply manager.
example : run [] = .ok (100, [0, 0, 100]) := by rfl

-- Owner mint/burn act on the supply manager's balance, even after transfers.
example : run [.mint 1 20, .transfer 2 1 30, .burn 1 15] =
    .ok (105, [0, 30, 75]) := by rfl

example : run [.transfer 2 3 20, .transfer 3 4 5] =
    .ok (100, [0, 0, 80, 15, 5]) := by rfl

example : run [.mint 2 5, .burn 2 105] = .ok (0, [0, 0, 0]) := by rfl

-- Self-transfers still check funds; successful ones do not change balances.
example : run [.transfer 2 2 100] = .ok (100, [0, 0, 100]) := by rfl
example : run [.transfer 2 2 101] = .error .insufficientBalance := by rfl
example : run [.transfer 2 1 101] = .error .insufficientBalance := by rfl
example : run [.burn 1 101] = .error .insufficientBalance := by rfl

example : run [.mint 3 1] = .error .unauthorized := by rfl
example : run [.burn 3 0] = .error .unauthorized := by rfl

-- A zero amount does not bypass compliance; absent accounts have no KYC.
example : run [.transfer 2 5 0] = .error .transferRestricted := by rfl
example : run [.transfer 5 2 0] = .error .transferRestricted := by rfl
example : snapshot ((create roles 100).bind fun s =>
    execute { s with frozen := fun a => a == 2 } (.transfer 2 1 1)) =
    .error .transferRestricted := by rfl
example : snapshot ((create roles 100).bind fun s =>
    execute { s with frozen := fun a => a == 1 } (.transfer 2 1 1)) =
    .error .transferRestricted := by rfl

-- Approve an ordinary account, fund it, and freeze it. Both transfer directions
-- fail; unfreezing the retained state permits a subsequent transfer.
example : ((create roles 100).bind fun s => executeAll s
    [.setKycPassed 3 5, .transfer 2 5 30, .freeze 1 5]).map (fun s =>
      (snapshot (execute s (.transfer 5 2 10)),
       snapshot (execute s (.transfer 2 5 10)),
       snapshot (executeAll s [.unfreeze 3 5, .transfer 5 2 10]))) =
    .ok (.error .transferRestricted, .error .transferRestricted,
      .ok (100, [0, 0, 80, 0, 0, 20])) := by rfl

-- Revoking KYC blocks either transfer direction. Unfreezing does not grant KYC;
-- granting it again restores transfers if the account is unfrozen.
example : run [.setKycPassed 1 5, .transfer 2 5 30,
    .unsetKycPassed 3 5, .transfer 5 2 10] = .error .transferRestricted := by rfl
example : run [.setKycPassed 3 5, .unsetKycPassed 1 5,
    .unfreeze 1 5, .transfer 2 5 1] = .error .transferRestricted := by rfl
example : run [.setKycPassed 3 5, .unsetKycPassed 1 5,
    .setKycPassed 1 5, .transfer 2 5 10] = .ok (100, [0, 0, 90, 0, 0, 10]) := by rfl

-- Granting KYC does not unfreeze an account, even for a zero self-transfer.
example : run [.freeze 3 5, .setKycPassed 1 5, .transfer 5 5 0] =
    .error .transferRestricted := by rfl

-- Changing one account's flags leaves the other account's flags intact.
example : ((create roles 100).bind fun s => executeAll s
    [.setKycPassed 3 5, .setKycPassed 1 6, .freeze 3 5, .freeze 1 6,
     .unsetKycPassed 1 5, .unfreeze 3 5]).map
    (fun s => (s.kycPassed 5, s.frozen 5, s.kycPassed 6, s.frozen 6)) =
    .ok (false, false, true, true) := by rfl

-- Enforcement and supply management do not confer compliance authority.
example : [Transaction.setKycPassed 4 5, .unsetKycPassed 4 5,
    .freeze 4 5, .unfreeze 4 5].map (fun tx => run [tx]) =
    List.replicate 4 (.error .unauthorized) := by rfl
example : run [.freeze 2 5] = .error .unauthorized := by rfl
example : run [.setKycPassed 5 5] = .error .unauthorized := by rfl

-- Every role is protected from freezing and KYC revocation, for both callers.
example : [1, 2, 3, 4].map (fun target => run [.freeze 1 target]) =
    List.replicate 4 (.error .privilegedAccount) := by rfl
example : [1, 2, 3, 4].map (fun target => run [.unsetKycPassed 3 target]) =
    List.replicate 4 (.error .privilegedAccount) := by rfl

-- KYC approval and unfreezing permit privileged targets and repeated calls.
example : run [.setKycPassed 3 1, .setKycPassed 3 1,
    .unfreeze 1 3, .unfreeze 1 3] = .ok (100, [0, 0, 100]) := by rfl
example : run [.freeze 3 5, .freeze 3 5, .unsetKycPassed 1 5,
    .unsetKycPassed 1 5] = .ok (100, [0, 0, 100]) := by rfl

-- These operations do not add a zero-target restriction to the K guards.
example : ((create roles 100).bind fun s => executeAll s
    [.setKycPassed 1 0, .freeze 3 0]).map (fun s => (s.kycPassed 0, s.frozen 0)) =
    .ok (true, true) := by rfl

-- The initialization guard also applies to each new operation.
example : [Transaction.setKycPassed 1 5, .unsetKycPassed 1 5,
    .freeze 1 5, .unfreeze 1 5].map (fun tx => snapshot ((create roles 100).bind fun s =>
      execute { s with roles := { roles with owner := 0 } } tx)) =
    List.replicate 4 (.error .uninitialized) := by rfl

-- A replacement proposal leaves the current owner in place, rejects the first
-- candidate, and lets the new candidate claim ownership and clear the proposal.
example : ((create roles 100).bind fun s => executeAll s
    [.setKycPassed 3 5, .setKycPassed 3 6, .proposeOwner 1 5, .proposeOwner 1 6]).map
    (fun s => (s.roles.owner, s.proposedOwner,
      snapshot (execute s (.claimOwnership 5)),
      (execute s (.claimOwnership 6)).map fun next => (next.roles.owner, next.proposedOwner))) =
    .ok (1, 6, .error .unauthorized, .ok (6, 0)) := by rfl

-- A proposal grants no authority, and claiming requires a pending proposal.
example : run [.setKycPassed 3 5, .proposeOwner 1 5, .changeSupplyManager 5 2] =
    .error .unauthorized := by rfl
example : run [.claimOwnership 1] = .error .unauthorized := by rfl
example : run [.proposeOwner 1 2, .claimOwnership 2, .claimOwnership 2] =
    .error .unauthorized := by rfl
example : runRoles [.proposeOwner 1 1, .claimOwnership 1] = .ok (roles, 0) := by rfl

-- A pending candidate can lose compliance; restoring it allows the same proposal
-- to be claimed. Both freezing and KYC revocation are rechecked at claim time.
example : [Transaction.freeze 3 5, .unsetKycPassed 3 5].map (fun block =>
    run [.setKycPassed 3 5, .proposeOwner 1 5, block, .claimOwnership 5]) =
    List.replicate 2 (.error .roleRestricted) := by rfl
example : runRoles [.setKycPassed 3 5, .proposeOwner 1 5,
    .freeze 3 5, .unfreeze 3 5, .claimOwnership 5] = .ok (⟨5, 2, 3, 4⟩, 0) := by rfl

-- The former owner's authority ends at handover unless it holds another role
-- that authorizes the operation. Here it can retain compliance authority.
example : run [.setKycPassed 3 5, .proposeOwner 1 5, .claimOwnership 5, .mint 1 1] =
    .error .unauthorized := by rfl
example : run [.setKycPassed 3 5, .changeComplianceManager 1 1,
    .proposeOwner 1 5, .claimOwnership 5, .freeze 1 6] = .ok (100, [0, 0, 100]) := by rfl

-- Supply management changes no balances. Later mint/burn use the new manager;
-- it cannot burn the tokens still held by the former manager.
example : run [.setKycPassed 3 5, .changeSupplyManager 1 5] =
    .ok (100, [0, 0, 100]) := by rfl
example : run [.setKycPassed 3 5, .changeSupplyManager 1 5, .mint 1 20, .burn 5 5] =
    .ok (115, [0, 0, 100, 0, 0, 15]) := by rfl
example : run [.setKycPassed 3 5, .changeSupplyManager 1 5, .burn 5 1] =
    .error .insufficientBalance := by rfl
example : run [.setKycPassed 3 5, .changeSupplyManager 1 5, .mint 2 1] =
    .error .unauthorized := by rfl

-- Compliance authority and protection follow the current assignments. A former
-- manager can be frozen, unless it still holds another privileged role.
example : run [.setKycPassed 3 5, .changeComplianceManager 1 5, .freeze 3 6] =
    .error .unauthorized := by rfl
example : run [.setKycPassed 3 5, .changeComplianceManager 1 5, .freeze 5 3] =
    .ok (100, [0, 0, 100]) := by rfl
example : run [.setKycPassed 3 5, .changeEnforcementManager 1 3,
    .changeComplianceManager 1 5, .freeze 5 3] = .error .privilegedAccount := by rfl

-- All roles may converge on one account after distinct-role initialization.
example : runRoles [.setKycPassed 3 5, .changeSupplyManager 1 5,
    .changeComplianceManager 1 5, .changeEnforcementManager 1 5,
    .proposeOwner 1 5, .claimOwnership 5] = .ok (⟨5, 5, 5, 5⟩, 0) := by rfl

-- Appointments require the current owner and a nonzero, compliant target.
example : (roleAppointments 2 5).map (fun tx => run [tx]) =
    List.replicate 4 (.error .unauthorized) := by rfl
example : (roleAppointments 1 0).map (fun tx => run [.setKycPassed 3 0, tx]) =
    List.replicate 4 (.error .invalidAddress) := by rfl
example : (roleAppointments 1 5).map (fun tx => run [tx]) =
    List.replicate 4 (.error .roleRestricted) := by rfl
example : (roleAppointments 1 5).map (fun tx =>
    run [.setKycPassed 3 5, .freeze 3 5, tx]) =
    List.replicate 4 (.error .roleRestricted) := by rfl

-- Zero cannot claim an empty proposal, even if granted KYC. An uninitialized
-- state also rejects all five operations before considering their other guards.
example : run [.setKycPassed 3 0, .claimOwnership 0] = .error .invalidAddress := by rfl
example : (roleAppointments 1 5 ++ [Transaction.claimOwnership 5]).map (fun tx =>
    snapshot ((create roles 100).bind fun s =>
      execute { s with roles := { roles with owner := 0 } } tx)) =
    List.replicate 5 (.error .uninitialized) := by rfl

-- Minting may reach the bound, but exceeding it fails.
example : ((create roles 0).bind fun s => execute s (.mint 1 maxValue)).map
    (fun s => s.totalSupply) = .ok maxValue := by rfl
example : snapshot ((create roles maxValue).bind fun s => execute s (.mint 1 1)) =
    .error .supplyOverflow := by rfl
example : snapshot (create roles (maxValue + 1)) = .error .supplyOverflow := by rfl

example : snapshot (create ⟨0, 2, 3, 4⟩ 100) = .error .invalidRoles := by rfl
example : snapshot (create ⟨2, 2, 3, 4⟩ 100) = .error .invalidRoles := by rfl

-- Stop on the first error, even if a later transaction would also fail.
example : run [.mint 3 1, .burn 1 101] = .error .unauthorized := by rfl

-- The universal preservation theorem applies to the executable examples.
example (s next : State) (txs : List Transaction)
    (init : create roles 100 = .ok s) (success : executeAll s txs = .ok next) :
    next.balances.sum = next.totalSupply :=
  (executeAll_preserves_invariant txs s next (create_invariant roles 100 s init) success).1

end HederaStablecoin.Examples
