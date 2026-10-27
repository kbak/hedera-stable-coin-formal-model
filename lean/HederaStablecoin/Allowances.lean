import HederaStablecoin.Balances

namespace HederaStablecoin

/-- Allowances are indexed by token holder and spender, with zero at creation. -/
abbrev Allowances := Address → Address → Nat

namespace Allowances

def set (allowances : Allowances) (holder spender : Address) (amount : Nat) : Allowances :=
  fun a b => if a = holder ∧ b = spender then amount else allowances a b

@[simp] theorem set_same (allowances : Allowances) (holder spender : Address) (amount : Nat) :
    (set allowances holder spender amount) holder spender = amount := by
  simp [set]

theorem set_other (allowances : Allowances) (holder spender a b : Address) (amount : Nat)
    (other : a ≠ holder ∨ b ≠ spender) :
    (set allowances holder spender amount) a b = allowances a b := by
  rcases other with other | other <;> simp [set, other]

end Allowances
end HederaStablecoin
