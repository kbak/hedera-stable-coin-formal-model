import HederaStablecoin.Delegation
import HederaStablecoin.Enforcement

namespace HederaStablecoin.SpendingExamples

private def roles : Roles := ⟨1, 2, 3, 4⟩

private def run (txs : List Transaction) : Except Error State :=
  (create roles 100).bind fun s => executeAll s txs

private def snapshot (txs : List Transaction) : Except Error (Nat × Balances × Nat) :=
  (run txs).map fun s => (s.totalSupply, s.balances, s.allowances 2 3)

-- Approval replaces the entry; allowance adjustments leave supply and balances alone.
example : snapshot [] = .ok (100, [0, 0, 100], 0) := by rfl
example : snapshot [.approveAllowance 2 3 50, .approveAllowance 2 3 20] =
    .ok (100, [0, 0, 100], 20) := by rfl
example : snapshot [.approveAllowance 2 3 50, .increaseAllowance 2 3 10,
    .decreaseAllowance 2 3 25] = .ok (100, [0, 0, 100], 35) := by rfl

-- Delegation spends exactly one allowance entry, including on self-transfers.
example : snapshot [.approveAllowance 2 3 60, .transferFrom 3 2 4 25] =
    .ok (100, [0, 0, 75, 0, 25], 35) := by rfl
example : snapshot [.approveAllowance 2 3 80, .transferFrom 3 2 2 40] =
    .ok (100, [0, 0, 100], 40) := by rfl
example : (run [.approveAllowance 2 3 50, .approveAllowance 2 4 70,
    .approveAllowance 3 2 90, .transferFrom 3 2 1 20]).map
    (fun s => (s.allowances 2 3, s.allowances 2 4, s.allowances 3 2)) =
    .ok (30, 70, 90) := by rfl

-- Exhausting allowance and exhausting balance are independent failure cases.
example : snapshot [.approveAllowance 2 3 30, .transferFrom 3 2 1 20,
    .transferFrom 3 2 1 11] = .error .insufficientAllowance := by rfl
example : snapshot [.approveAllowance 2 3 200, .transferFrom 3 2 1 101] =
    .error .insufficientBalance := by rfl
example : snapshot [.approveAllowance 2 3 200, .transferFrom 3 2 2 101] =
    .error .insufficientBalance := by rfl
example : snapshot [.transferFrom 1 2 4 1] = .error .insufficientAllowance := by rfl
example : snapshot [.decreaseAllowance 2 3 1] = .error .insufficientAllowance := by rfl

-- Zero spending needs no positive allowance, but still checks compliance.
example : snapshot [.transferFrom 3 2 1 0] = .ok (100, [0, 0, 100], 0) := by rfl
example : snapshot [.transferFrom 3 2 5 0] = .error .transferRestricted := by rfl

-- The total-map reference model also handles aliased participants explicitly.
example : (run [.approveAllowance 2 2 10, .transferFrom 2 2 3 5]).map
    (fun s => (s.balances, s.allowances 2 2)) = .ok ([0, 0, 95, 5], 5) := by rfl
example : snapshot [.approveAllowance 2 3 30, .transferFrom 3 2 3 25] =
    .ok (100, [0, 0, 75, 25], 5) := by rfl
example : (run [.approveAllowance 2 2 10, .transferFrom 2 2 2 10]).map
    (fun s => (s.balances, s.allowances 2 2)) = .ok ([0, 0, 100], 0) := by rfl

-- Approval is unbounded in K; only increases check MAXVALUE. Decreases reject
-- underflow, and can bring an oversized approved allowance back into range.
example : (run [.approveAllowance 2 3 (maxValue + 1)]).map
    (fun s => s.allowances 2 3) = .ok (maxValue + 1) := by rfl
example : (run [.increaseAllowance 2 3 maxValue]).map
    (fun s => s.allowances 2 3) = .ok maxValue := by rfl
example : snapshot [.increaseAllowance 2 3 maxValue, .increaseAllowance 2 3 1] =
    .error .allowanceOverflow := by rfl
example : snapshot [.approveAllowance 2 3 (maxValue + 1), .increaseAllowance 2 3 0] =
    .error .allowanceOverflow := by rfl
example : (run [.approveAllowance 2 3 (maxValue + 1), .decreaseAllowance 2 3 1]).map
    (fun s => s.allowances 2 3) = .ok maxValue := by rfl

private def delegated : List Transaction :=
  [.setKycPassed 3 5, .setKycPassed 3 6, .setKycPassed 3 7,
   .transfer 2 5 40, .approveAllowance 5 6 30]

-- Freezing or revoking KYC of any participant blocks delegated spending.
example : [Transaction.freeze 3 5, .freeze 3 6, .freeze 3 7,
    .unsetKycPassed 3 5, .unsetKycPassed 3 6, .unsetKycPassed 3 7].map
    (fun block => snapshot (delegated ++ [block, .transferFrom 6 5 7 10])) =
    List.replicate 6 (.error .transferRestricted) := by rfl

-- All three allowance updates check both parties, even when setting/reducing to zero.
example : [Transaction.freeze 3 5, .freeze 3 6,
    .unsetKycPassed 3 5, .unsetKycPassed 3 6].flatMap (fun block =>
      [Transaction.approveAllowance 5 6 0, .increaseAllowance 5 6 0,
       .decreaseAllowance 5 6 30].map (fun tx => snapshot (delegated ++ [block, tx]))) =
    List.replicate 12 (.error .transferRestricted) := by rfl

-- Wiping works on frozen/non-KYC accounts and does not alter their allowances or flags.
example : (run (delegated ++ [.freeze 3 5, .unsetKycPassed 3 5, .wipe 4 5 15])).map
    (fun s => (s.totalSupply, s.balances, s.allowances 5 6, s.kycPassed 5, s.frozen 5)) =
    .ok (85, [0, 0, 60, 0, 0, 25], 30, false, true) := by rfl
example : snapshot [.wipe 1 2 100] = .ok (0, [0, 0, 0], 0) := by rfl
example : snapshot [.wipe 4 2 101] = .error .insufficientBalance := by rfl
example : snapshot [.wipe 3 2 1] = .error .unauthorized := by rfl
example : snapshot [.wipe 2 2 1] = .error .unauthorized := by rfl
example : snapshot [.wipe 4 0 0] = .ok (100, [0, 0, 100], 0) := by rfl

-- Enforcement authority follows reassignment, while the owner remains authorized.
example : snapshot [.setKycPassed 3 5, .changeEnforcementManager 1 5, .wipe 4 2 1] =
    .error .unauthorized := by rfl
example : snapshot [.setKycPassed 3 5, .changeEnforcementManager 1 5, .wipe 5 2 10] =
    .ok (90, [0, 0, 90], 0) := by rfl

-- A mixed trace combines delegation, compliance, wiping, mint/burn, and handover.
example : (run (delegated ++ [.transferFrom 6 5 7 10, .freeze 3 5, .wipe 4 5 5,
    .changeSupplyManager 1 7, .mint 1 20, .burn 7 10,
    .proposeOwner 1 6, .claimOwnership 6])).map
    (fun s => (s.totalSupply, s.balances, s.allowances 5 6, s.roles)) =
    .ok (105, [0, 0, 60, 0, 0, 25, 0, 20], 20, ⟨6, 7, 3, 4⟩) := by rfl

-- Every new operation retains the global initialization guard.
example : [Transaction.approveAllowance 2 3 1, .increaseAllowance 2 3 1,
    .decreaseAllowance 2 3 1, .transferFrom 3 2 1 1, .wipe 4 2 1].map
    (fun tx => ((create roles 100).bind fun s =>
      execute { s with roles := { roles with owner := 0 } } tx).map (fun s => s.totalSupply)) =
    List.replicate 5 (.error .uninitialized) := by rfl

end HederaStablecoin.SpendingExamples
