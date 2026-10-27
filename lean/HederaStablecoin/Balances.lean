import Std

namespace HederaStablecoin

/-- Addresses are symbolic account identifiers; zero is the unset-role sentinel. -/
abbrev Address := Nat

/-- A finite balance table, indexed by address. Missing entries have balance zero. -/
abbrev Balances := List Nat

namespace Balances

def get : Balances → Address → Nat
  | [], _ => 0
  | b :: _, 0 => b
  | _ :: bs, a + 1 => get bs a

/-- Credit an account, extending the table with zeros when necessary. -/
def credit : Balances → Address → Nat → Balances
  | [], 0, amount => [amount]
  | [], a + 1, amount => 0 :: credit [] a amount
  | b :: bs, 0, amount => (b + amount) :: bs
  | b :: bs, a + 1, amount => b :: credit bs a amount

/-- The transition function checks sufficient funds before calling `debit`. -/
def debit : Balances → Address → Nat → Balances
  | [], _, _ => []
  | b :: bs, 0, amount => (b - amount) :: bs
  | b :: bs, a + 1, amount => b :: debit bs a amount

theorem sum_credit (bs : Balances) (a amount : Nat) :
    (credit bs a amount).sum = bs.sum + amount := by
  induction a generalizing bs with
  | zero => cases bs <;> simp [credit, Nat.add_assoc, Nat.add_comm]
  | succ a ih => cases bs <;> simp [credit, ih, Nat.add_assoc]

theorem get_le_sum (bs : Balances) (a : Address) : get bs a ≤ bs.sum := by
  induction a generalizing bs with
  | zero => cases bs <;> simp [get]
  | succ a ih =>
    cases bs with
    | nil => simp [get]
    | cons b bs => simpa [get] using Nat.le_add_left_of_le (ih bs)

theorem sum_debit (bs : Balances) (a amount : Nat) (h : amount ≤ get bs a) :
    (debit bs a amount).sum = bs.sum - amount := by
  induction a generalizing bs with
  | zero =>
    cases bs with
    | nil => simp [debit]
    | cons b bs => simp only [get] at h; simp only [debit, List.sum_cons]; omega
  | succ a ih =>
    cases bs with
    | nil => simp [debit]
    | cons b bs =>
      simp only [get] at h
      have := get_le_sum bs a
      simp only [debit, List.sum_cons, ih bs h]
      omega

@[simp] theorem get_credit_same (bs : Balances) (a amount : Nat) :
    get (credit bs a amount) a = get bs a + amount := by
  induction a generalizing bs with
  | zero => cases bs <;> simp [credit, get]
  | succ a ih => cases bs <;> simp [credit, get, ih]

@[simp] theorem get_debit_same (bs : Balances) (a amount : Nat) :
    get (debit bs a amount) a = get bs a - amount := by
  induction a generalizing bs with
  | zero => cases bs <;> simp [debit, get]
  | succ a ih => cases bs <;> simp [debit, get, ih]

theorem get_credit_other (bs : Balances) (a other amount : Nat) (h : other ≠ a) :
    get (credit bs a amount) other = get bs other := by
  induction a generalizing bs other with
  | zero => cases bs <;> cases other <;> simp_all [credit, get]
  | succ a ih => cases bs <;> cases other <;> simp_all [credit, get]

theorem get_debit_other (bs : Balances) (a other amount : Nat) (h : other ≠ a) :
    get (debit bs a amount) other = get bs other := by
  induction a generalizing bs other with
  | zero => cases bs <;> cases other <;> simp_all [debit, get]
  | succ a ih => cases bs <;> cases other <;> simp_all [debit, get]

end Balances
end HederaStablecoin
