import HederaStablecoin.Invariants

namespace HederaStablecoin

/-- Wiping requires owner/enforcement authority and funds, independently of compliance flags. -/
theorem wipe_spec (s next : State) (caller target : Address) (amount : Nat)
    (h : execute s (.wipe caller target amount) = .ok next) :
    (caller = s.roles.owner ∨ caller = s.roles.enforcementManager) ∧
    amount ≤ s.balances.get target ∧
    next = { s with
      balances := s.balances.debit target amount
      totalSupply := s.totalSupply - amount } := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all

/-- Conservation ensures subtraction from supply cannot underflow. -/
theorem wipe_effect (s next : State) (caller target : Address) (amount : Nat)
    (supply : SupplyInvariant s)
    (h : execute s (.wipe caller target amount) = .ok next) :
    next.totalSupply + amount = s.totalSupply ∧
    next.balances.get target + amount = s.balances.get target := by
  obtain ⟨_, funds, rfl⟩ := wipe_spec s next caller target amount h
  have bound := Balances.get_le_sum s.balances target
  unfold SupplyInvariant at supply
  have enough : amount ≤ s.totalSupply := by omega
  simp [Nat.sub_add_cancel enough, Nat.sub_add_cancel funds]

theorem wipe_other_balance (s next : State) (caller target other : Address) (amount : Nat)
    (different : other ≠ target)
    (h : execute s (.wipe caller target amount) = .ok next) :
    next.balances.get other = s.balances.get other := by
  obtain ⟨_, _, rfl⟩ := wipe_spec s next caller target amount h
  exact Balances.get_debit_other _ _ _ _ different

end HederaStablecoin
