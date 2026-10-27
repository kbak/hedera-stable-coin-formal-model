import HederaStablecoin.Invariants

namespace HederaStablecoin

/-- Approval replaces this caller/spender entry, with no upper bound in the K rule. -/
theorem approveAllowance_spec (s next : State) (caller spender : Address) (amount : Nat)
    (h : execute s (.approveAllowance caller spender amount) = .ok next) :
    transferAllowed s caller = true ∧ transferAllowed s spender = true ∧
    next = { s with allowances := s.allowances.set caller spender amount } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

theorem increaseAllowance_spec (s next : State) (caller spender : Address) (amount : Nat)
    (h : execute s (.increaseAllowance caller spender amount) = .ok next) :
    transferAllowed s caller = true ∧ transferAllowed s spender = true ∧
    s.allowances caller spender + amount ≤ maxValue ∧
    next = { s with
      allowances := s.allowances.set caller spender (s.allowances caller spender + amount) } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

theorem decreaseAllowance_spec (s next : State) (caller spender : Address) (amount : Nat)
    (h : execute s (.decreaseAllowance caller spender amount) = .ok next) :
    transferAllowed s caller = true ∧ transferAllowed s spender = true ∧
    amount ≤ s.allowances caller spender ∧
    next = { s with
      allowances := s.allowances.set caller spender (s.allowances caller spender - amount) } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- All three participants must be compliant; spending requires funds and delegation. -/
theorem transferFrom_spec (s next : State) (caller holder recipient : Address) (amount : Nat)
    (h : execute s (.transferFrom caller holder recipient amount) = .ok next) :
    transferAllowed s caller = true ∧ transferAllowed s holder = true ∧
    transferAllowed s recipient = true ∧ amount ≤ s.balances.get holder ∧
    amount ≤ s.allowances holder caller ∧
    next = { s with
      balances := if holder = recipient then s.balances else
        (s.balances.debit holder amount).credit recipient amount
      allowances := s.allowances.set holder caller (s.allowances holder caller - amount) } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- Every delegated transfer consumes exactly its amount, including self-transfers. -/
theorem transferFrom_allowance (s next : State) (caller holder recipient : Address) (amount : Nat)
    (h : execute s (.transferFrom caller holder recipient amount) = .ok next) :
    next.allowances holder caller + amount = s.allowances holder caller := by
  obtain ⟨_, _, _, _, allowed, rfl⟩ := transferFrom_spec s next caller holder recipient amount h
  simp [Nat.sub_add_cancel allowed]

theorem transferFrom_effect (s next : State) (caller holder recipient : Address) (amount : Nat)
    (different : holder ≠ recipient)
    (h : execute s (.transferFrom caller holder recipient amount) = .ok next) :
    next.balances.get holder + amount = s.balances.get holder ∧
    next.balances.get recipient = s.balances.get recipient + amount ∧
    next.totalSupply = s.totalSupply := by
  obtain ⟨_, _, _, funds, _, rfl⟩ := transferFrom_spec s next caller holder recipient amount h
  simp [different, Balances.get_credit_other, Balances.get_debit_other,
    Nat.sub_add_cancel funds, Ne.symm]

theorem transferFrom_self (s next : State) (caller holder : Address) (amount : Nat)
    (h : execute s (.transferFrom caller holder holder amount) = .ok next) :
    next.balances = s.balances ∧ next.totalSupply = s.totalSupply ∧
    next.allowances holder caller + amount = s.allowances holder caller := by
  obtain ⟨_, _, _, _, allowed, rfl⟩ := transferFrom_spec s next caller holder holder amount h
  simp [Nat.sub_add_cancel allowed]

theorem transferFrom_other_allowance (s next : State)
    (caller holder recipient a b : Address) (amount : Nat)
    (other : a ≠ holder ∨ b ≠ caller)
    (h : execute s (.transferFrom caller holder recipient amount) = .ok next) :
    next.allowances a b = s.allowances a b := by
  obtain ⟨_, _, _, _, _, rfl⟩ := transferFrom_spec s next caller holder recipient amount h
  exact Allowances.set_other _ _ _ _ _ _ other

theorem transferFrom_other_balance (s next : State)
    (caller holder recipient other : Address) (amount : Nat)
    (notHolder : other ≠ holder) (notRecipient : other ≠ recipient)
    (h : execute s (.transferFrom caller holder recipient amount) = .ok next) :
    next.balances.get other = s.balances.get other := by
  obtain ⟨_, _, _, _, _, rfl⟩ := transferFrom_spec s next caller holder recipient amount h
  by_cases same : holder = recipient <;>
    simp [same, Balances.get_credit_other, Balances.get_debit_other, notHolder, notRecipient]

end HederaStablecoin
