import HederaStablecoin.Model

namespace HederaStablecoin

def SupplyInvariant (s : State) : Prop := s.balances.sum = s.totalSupply

/-- Conservation, the supply bound, and nonzero roles. Nonnegative balances are typed. -/
def Invariant (s : State) : Prop :=
  SupplyInvariant s ∧ s.totalSupply ≤ maxValue ∧ s.roles.Valid

theorem create_invariant (roles : Roles) (supply : Nat) (s : State)
    (h : create roles supply = .ok s) : Invariant s := by
  unfold create at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp_all [Invariant, SupplyInvariant, Balances.sum_credit]

/-- Distinct roles are guaranteed at creation, but need not persist after reassignment. -/
theorem create_roles_distinct (roles : Roles) (supply : Nat) (s : State)
    (h : create roles supply = .ok s) : s.roles.Distinct := by
  unfold create at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp_all

private theorem sum_transfer (bs : Balances) (sender recipient amount : Nat)
    (h : amount ≤ bs.get sender) :
    ((bs.debit sender amount).credit recipient amount).sum = bs.sum := by
  rw [Balances.sum_credit, Balances.sum_debit bs sender amount h]
  have := Balances.get_le_sum bs sender
  omega

/-- Every successful operation preserves the invariant, including self-transfers. -/
theorem execute_preserves_invariant (s next : State) (tx : Transaction)
    (inv : Invariant s) (h : execute s tx = .ok next) : Invariant next := by
  rcases inv with ⟨supply, bound, roles⟩
  unfold SupplyInvariant at supply
  cases tx with
  | transfer caller recipient amount =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, sum_transfer]
  | mint caller amount =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, Balances.sum_credit]
  | burn caller amount =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, Balances.sum_debit]
    all_goals omega
  | setKycPassed caller target | unsetKycPassed caller target
  | freeze caller target | unfreeze caller target | proposeOwner caller target =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals exact ⟨supply, bound, roles⟩
  | claimOwnership caller =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, Roles.Valid]
  | changeSupplyManager caller target | changeComplianceManager caller target
  | changeEnforcementManager caller target =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, Roles.Valid]
  | approveAllowance caller spender amount | increaseAllowance caller spender amount
  | decreaseAllowance caller spender amount =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals exact ⟨supply, bound, roles⟩
  | transferFrom caller holder recipient amount =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, sum_transfer]
  | wipe caller target amount =>
    simp only [execute] at h
    repeat' split at h
    all_goals try contradiction
    all_goals cases h
    all_goals simp_all [Invariant, SupplyInvariant, Balances.sum_debit]
    all_goals omega

/-- Induction over an executable list of transactions. -/
theorem executeAll_preserves_invariant (txs : List Transaction) (s next : State)
    (inv : Invariant s) (h : executeAll s txs = .ok next) : Invariant next := by
  induction txs generalizing s with
  | nil =>
    simp only [executeAll, Except.ok.injEq] at h
    exact h ▸ inv
  | cons tx txs ih =>
    simp only [executeAll] at h
    cases step : execute s tx with
    | error e => simp [step, Except.bind] at h
    | ok middle =>
      simp only [step, Except.bind] at h
      exact ih middle (execute_preserves_invariant s middle tx inv step) h

/-- The same guarantee for the relational, reflexive-transitive closure. -/
theorem reachable_preserves_invariant {s next : State}
    (inv : Invariant s) (h : Reachable s next) : Invariant next := by
  induction h with
  | refl => exact inv
  | step _ step ih =>
    obtain ⟨tx, success⟩ := step
    exact execute_preserves_invariant _ _ tx ih success

theorem created_reachable_invariant (roles : Roles) (supply : Nat) (s next : State)
    (init : create roles supply = .ok s) (path : Reachable s next) : Invariant next :=
  reachable_preserves_invariant (create_invariant roles supply s init) path

/-- Successful minting and burning require the owner or supply manager. -/
theorem mint_authorized (s next : State) (caller amount : Nat)
    (h : execute s (.mint caller amount) = .ok next) :
    caller = s.roles.supplyManager ∨ caller = s.roles.owner := by
  simp only [execute] at h
  split at h <;> try contradiction
  split at h <;> simp_all

theorem burn_authorized (s next : State) (caller amount : Nat)
    (h : execute s (.burn caller amount) = .ok next) :
    caller = s.roles.supplyManager ∨ caller = s.roles.owner := by
  simp only [execute] at h
  split at h <;> try contradiction
  split at h <;> simp_all

theorem transfer_compliant (s next : State) (caller recipient amount : Nat)
    (h : execute s (.transfer caller recipient amount) = .ok next) :
    s.kycPassed caller = true ∧ s.frozen caller = false ∧
    s.kycPassed recipient = true ∧ s.frozen recipient = false := by
  simp only [execute] at h
  split at h <;> try contradiction
  split at h <;> simp_all [transferAllowed]

theorem transfer_supply (s next : State) (caller recipient amount : Nat)
    (h : execute s (.transfer caller recipient amount) = .ok next) :
    next.totalSupply = s.totalSupply := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> rfl

/-- A transfer between distinct accounts debits the sender and credits the recipient. -/
theorem transfer_effect (s next : State) (caller recipient amount : Nat)
    (different : caller ≠ recipient)
    (h : execute s (.transfer caller recipient amount) = .ok next) :
    next.balances.get caller + amount = s.balances.get caller ∧
    next.balances.get recipient = s.balances.get recipient + amount := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h
  all_goals simp_all [Balances.get_credit_other, Balances.get_debit_other,
    Nat.sub_add_cancel, Ne.symm]

theorem mint_effect (s next : State) (caller amount : Nat)
    (h : execute s (.mint caller amount) = .ok next) :
    next.totalSupply = s.totalSupply + amount ∧
    next.balances.get s.roles.supplyManager = s.balances.get s.roles.supplyManager + amount := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp

theorem burn_effect (s next : State) (caller amount : Nat)
    (h : execute s (.burn caller amount) = .ok next) :
    next.totalSupply + amount = s.totalSupply ∧
    next.balances.get s.roles.supplyManager + amount = s.balances.get s.roles.supplyManager := by
  simp only [execute] at h
  repeat' split at h
  all_goals try contradiction
  all_goals cases h <;> simp_all [Nat.sub_add_cancel]
  all_goals omega

end HederaStablecoin
