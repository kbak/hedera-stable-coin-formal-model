import HederaStablecoin.Invariants

namespace HederaStablecoin

/-- Only the current owner can propose an eligible successor; the old proposal is replaced. -/
theorem proposeOwner_spec (s next : State) (caller target : Address)
    (h : execute s (.proposeOwner caller target) = .ok next) :
    caller = s.roles.owner ∧ target ≠ 0 ∧
    s.kycPassed target = true ∧ s.frozen target = false ∧
    next = { s with proposedOwner := target } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all [transferAllowed]

/-- The proposed owner must still be eligible when claiming; success clears the proposal. -/
theorem claimOwnership_spec (s next : State) (caller : Address)
    (h : execute s (.claimOwnership caller) = .ok next) :
    caller = s.proposedOwner ∧ caller ≠ 0 ∧
    s.kycPassed caller = true ∧ s.frozen caller = false ∧
    next = { s with roles := { s.roles with owner := caller }, proposedOwner := 0 } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all [transferAllowed]

/-- Reassigning supply management leaves all balances, supply, and flags unchanged. -/
theorem changeSupplyManager_spec (s next : State) (caller target : Address)
    (h : execute s (.changeSupplyManager caller target) = .ok next) :
    caller = s.roles.owner ∧ target ≠ 0 ∧
    s.kycPassed target = true ∧ s.frozen target = false ∧
    next = { s with roles := { s.roles with supplyManager := target } } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all [transferAllowed]

theorem changeComplianceManager_spec (s next : State) (caller target : Address)
    (h : execute s (.changeComplianceManager caller target) = .ok next) :
    caller = s.roles.owner ∧ target ≠ 0 ∧
    s.kycPassed target = true ∧ s.frozen target = false ∧
    next = { s with roles := { s.roles with complianceManager := target } } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all [transferAllowed]

theorem changeEnforcementManager_spec (s next : State) (caller target : Address)
    (h : execute s (.changeEnforcementManager caller target) = .ok next) :
    caller = s.roles.owner ∧ target ≠ 0 ∧
    s.kycPassed target = true ∧ s.frozen target = false ∧
    next = { s with roles := { s.roles with enforcementManager := target } } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all [transferAllowed]

/-- A pending proposal cannot bypass a later freeze or KYC revocation. -/
theorem claimOwnership_rechecks_compliance (s : State) (caller : Address)
    (initialized : s.roles.owner ≠ 0) (nonzero : caller ≠ 0)
    (proposed : caller = s.proposedOwner)
    (blocked : s.kycPassed caller = false ∨ s.frozen caller = true) :
    execute s (.claimOwnership caller) = .error .roleRestricted := by
  simp only [execute, ite_eq_right initialized, ite_eq_right nonzero, ite_eq_left proposed]
  rcases blocked with blocked | blocked <;>
    simp [transferAllowed, blocked]

end HederaStablecoin
