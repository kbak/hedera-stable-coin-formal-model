import HederaStablecoin.Invariants

namespace HederaStablecoin

/-- Successful KYC approval requires authority and changes only the target's KYC flag. -/
theorem setKycPassed_spec (s next : State) (caller target : Address)
    (h : execute s (.setKycPassed caller target) = .ok next) :
    (caller = s.roles.owner ∨ caller = s.roles.complianceManager) ∧
    next = { s with kycPassed := fun a => if a = target then true else s.kycPassed a } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- Revocation additionally requires a target that holds none of the four roles. -/
theorem unsetKycPassed_spec (s next : State) (caller target : Address)
    (h : execute s (.unsetKycPassed caller target) = .ok next) :
    (caller = s.roles.owner ∨ caller = s.roles.complianceManager) ∧
    s.roles.isPrivileged target = false ∧
    next = { s with kycPassed := fun a => if a = target then false else s.kycPassed a } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- Freezing has the same authority and target restrictions as KYC revocation. -/
theorem freeze_spec (s next : State) (caller target : Address)
    (h : execute s (.freeze caller target) = .ok next) :
    (caller = s.roles.owner ∨ caller = s.roles.complianceManager) ∧
    s.roles.isPrivileged target = false ∧
    next = { s with frozen := fun a => if a = target then true else s.frozen a } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- Authorized callers may unfreeze any target, including privileged accounts. -/
theorem unfreeze_spec (s next : State) (caller target : Address)
    (h : execute s (.unfreeze caller target) = .ok next) :
    (caller = s.roles.owner ∨ caller = s.roles.complianceManager) ∧
    next = { s with frozen := fun a => if a = target then false else s.frozen a } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- Even zero-amount and self-transfers must respect freezing. -/
theorem transfer_rejected_when_frozen (s : State) (caller recipient amount : Nat)
    (initialized : s.roles.owner ≠ 0)
    (blocked : s.frozen caller = true ∨ s.frozen recipient = true) :
    execute s (.transfer caller recipient amount) = .error .transferRestricted := by
  rcases blocked with blocked | blocked <;> simp [execute, initialized, transferAllowed, blocked]

theorem transfer_rejected_without_kyc (s : State) (caller recipient amount : Nat)
    (initialized : s.roles.owner ≠ 0)
    (blocked : s.kycPassed caller = false ∨ s.kycPassed recipient = false) :
    execute s (.transfer caller recipient amount) = .error .transferRestricted := by
  rcases blocked with blocked | blocked <;> simp [execute, initialized, transferAllowed, blocked]

end HederaStablecoin
