import HederaStablecoin.Allowances

namespace HederaStablecoin

/-- The bound used by `MAXVALUE` in `hcs.k`. Arithmetic itself does not wrap. -/
def maxValue : Nat := 2 ^ 256 - 1

structure Roles where
  owner : Address
  supplyManager : Address
  complianceManager : Address
  enforcementManager : Address
  deriving DecidableEq, Repr

/-- Active roles must be nonzero; an account may hold multiple roles. -/
def Roles.Valid (r : Roles) : Prop :=
  r.owner ≠ 0 ∧ r.supplyManager ≠ 0 ∧ r.complianceManager ≠ 0 ∧
  r.enforcementManager ≠ 0

/-- A constructor restriction, not an invariant of role changes; see the README. -/
def Roles.Distinct (r : Roles) : Prop :=
  r.owner ≠ r.supplyManager ∧
  r.owner ≠ r.complianceManager ∧ r.owner ≠ r.enforcementManager ∧
  r.supplyManager ≠ r.complianceManager ∧ r.supplyManager ≠ r.enforcementManager ∧
  r.complianceManager ≠ r.enforcementManager

instance (r : Roles) : Decidable r.Valid := by unfold Roles.Valid; infer_instance
instance (r : Roles) : Decidable r.Distinct := by unfold Roles.Distinct; infer_instance

/-- All four roles are protected from freezing and KYC revocation. -/
def Roles.isPrivileged (r : Roles) (a : Address) : Bool :=
  a == r.owner || a == r.supplyManager ||
    a == r.complianceManager || a == r.enforcementManager

structure State where
  balances : Balances
  totalSupply : Nat
  roles : Roles
  proposedOwner : Address
  allowances : Allowances
  kycPassed : Address → Bool
  frozen : Address → Bool

inductive Error where
  | invalidRoles
  | supplyOverflow
  | uninitialized
  | unauthorized
  | transferRestricted
  | insufficientBalance
  | inconsistentSupply
  | privilegedAccount
  | invalidAddress
  | roleRestricted
  | allowanceOverflow
  | insufficientAllowance
  deriving DecidableEq, Repr

/-- Fresh initialization, rather than an operation on an existing state. -/
def create (roles : Roles) (supply : Nat) : Except Error State :=
  if roles.Valid ∧ roles.Distinct then
    if supply ≤ maxValue then
      .ok {
        balances := Balances.credit [] roles.supplyManager supply
        totalSupply := supply
        roles := roles
        proposedOwner := 0
        allowances := fun _ _ => 0
        kycPassed := roles.isPrivileged
        frozen := fun _ => false
      }
    else .error .supplyOverflow
  else .error .invalidRoles

inductive Transaction where
  | transfer (caller recipient : Address) (amount : Nat)
  | mint (caller : Address) (amount : Nat)
  | burn (caller : Address) (amount : Nat)
  | setKycPassed (caller target : Address)
  | unsetKycPassed (caller target : Address)
  | freeze (caller target : Address)
  | unfreeze (caller target : Address)
  | proposeOwner (caller target : Address)
  | claimOwnership (caller : Address)
  | changeSupplyManager (caller target : Address)
  | changeComplianceManager (caller target : Address)
  | changeEnforcementManager (caller target : Address)
  | approveAllowance (caller spender : Address) (amount : Nat)
  | increaseAllowance (caller spender : Address) (amount : Nat)
  | decreaseAllowance (caller spender : Address) (amount : Nat)
  | transferFrom (caller holder recipient : Address) (amount : Nat)
  | wipe (caller target : Address) (amount : Nat)
  deriving DecidableEq, Repr

def transferAllowed (s : State) (a : Address) : Bool :=
  s.kycPassed a && !s.frozen a

/-- Pure, atomic execution. Errors return no successor state. -/
def execute (s : State) (tx : Transaction) : Except Error State :=
  if s.roles.owner = 0 then .error .uninitialized else
  match tx with
  | .transfer caller recipient amount =>
    if transferAllowed s caller ∧ transferAllowed s recipient then
      if amount ≤ s.balances.get caller then
        if caller = recipient then .ok s else
          .ok { s with balances :=
            (s.balances.debit caller amount).credit recipient amount }
      else .error .insufficientBalance
    else .error .transferRestricted
  | .mint caller amount =>
    if caller = s.roles.supplyManager ∨ caller = s.roles.owner then
      if s.balances.get s.roles.supplyManager ≤ s.totalSupply then
        if s.totalSupply + amount ≤ maxValue then
          .ok { s with
            balances := s.balances.credit s.roles.supplyManager amount
            totalSupply := s.totalSupply + amount }
        else .error .supplyOverflow
      else .error .inconsistentSupply
    else .error .unauthorized
  | .burn caller amount =>
    if caller = s.roles.supplyManager ∨ caller = s.roles.owner then
      if s.balances.get s.roles.supplyManager ≤ s.totalSupply then
        if amount ≤ s.balances.get s.roles.supplyManager then
          .ok { s with
            balances := s.balances.debit s.roles.supplyManager amount
            totalSupply := s.totalSupply - amount }
        else .error .insufficientBalance
      else .error .inconsistentSupply
    else .error .unauthorized
  | .setKycPassed caller target =>
    if caller = s.roles.owner ∨ caller = s.roles.complianceManager then
      .ok { s with kycPassed := fun a => if a = target then true else s.kycPassed a }
    else .error .unauthorized
  | .unsetKycPassed caller target =>
    if caller = s.roles.owner ∨ caller = s.roles.complianceManager then
      if s.roles.isPrivileged target then .error .privilegedAccount else
        .ok { s with kycPassed := fun a => if a = target then false else s.kycPassed a }
    else .error .unauthorized
  | .freeze caller target =>
    if caller = s.roles.owner ∨ caller = s.roles.complianceManager then
      if s.roles.isPrivileged target then .error .privilegedAccount else
        .ok { s with frozen := fun a => if a = target then true else s.frozen a }
    else .error .unauthorized
  | .unfreeze caller target =>
    if caller = s.roles.owner ∨ caller = s.roles.complianceManager then
      .ok { s with frozen := fun a => if a = target then false else s.frozen a }
    else .error .unauthorized
  | .proposeOwner caller target =>
    if caller = s.roles.owner then
      if target = 0 then .error .invalidAddress else
        if transferAllowed s target then .ok { s with proposedOwner := target }
        else .error .roleRestricted
    else .error .unauthorized
  | .claimOwnership caller =>
    if caller = 0 then .error .invalidAddress else
      if caller = s.proposedOwner then
        if transferAllowed s caller then
          .ok { s with roles := { s.roles with owner := caller }, proposedOwner := 0 }
        else .error .roleRestricted
      else .error .unauthorized
  | .changeSupplyManager caller target =>
    if caller = s.roles.owner then
      if target = 0 then .error .invalidAddress else
        if transferAllowed s target then
          .ok { s with roles := { s.roles with supplyManager := target } }
        else .error .roleRestricted
    else .error .unauthorized
  | .changeComplianceManager caller target =>
    if caller = s.roles.owner then
      if target = 0 then .error .invalidAddress else
        if transferAllowed s target then
          .ok { s with roles := { s.roles with complianceManager := target } }
        else .error .roleRestricted
    else .error .unauthorized
  | .changeEnforcementManager caller target =>
    if caller = s.roles.owner then
      if target = 0 then .error .invalidAddress else
        if transferAllowed s target then
          .ok { s with roles := { s.roles with enforcementManager := target } }
        else .error .roleRestricted
    else .error .unauthorized
  | .approveAllowance caller spender amount =>
    if transferAllowed s caller ∧ transferAllowed s spender then
      .ok { s with allowances := s.allowances.set caller spender amount }
    else .error .transferRestricted
  | .increaseAllowance caller spender amount =>
    if transferAllowed s caller ∧ transferAllowed s spender then
      if s.allowances caller spender + amount ≤ maxValue then
        .ok { s with
          allowances := s.allowances.set caller spender (s.allowances caller spender + amount) }
      else .error .allowanceOverflow
    else .error .transferRestricted
  | .decreaseAllowance caller spender amount =>
    if transferAllowed s caller ∧ transferAllowed s spender then
      if amount ≤ s.allowances caller spender then
        .ok { s with
          allowances := s.allowances.set caller spender (s.allowances caller spender - amount) }
      else .error .insufficientAllowance
    else .error .transferRestricted
  | .transferFrom caller holder recipient amount =>
    if transferAllowed s caller ∧ transferAllowed s holder ∧ transferAllowed s recipient then
      if amount ≤ s.balances.get holder then
        if amount ≤ s.allowances holder caller then
          .ok { s with
            balances := if holder = recipient then s.balances else
              (s.balances.debit holder amount).credit recipient amount
            allowances := s.allowances.set holder caller (s.allowances holder caller - amount) }
        else .error .insufficientAllowance
      else .error .insufficientBalance
    else .error .transferRestricted
  | .wipe caller target amount =>
    if caller = s.roles.owner ∨ caller = s.roles.enforcementManager then
      if amount ≤ s.balances.get target then
        .ok { s with
          balances := s.balances.debit target amount
          totalSupply := s.totalSupply - amount }
      else .error .insufficientBalance
    else .error .unauthorized

/-- Execute in order, stopping at the first error. -/
def executeAll (s : State) : List Transaction → Except Error State
  | [] => .ok s
  | tx :: txs => (execute s tx).bind fun next => executeAll next txs

/-- A successful transaction is one step of the reference model. -/
def Step (s next : State) : Prop := ∃ tx, execute s tx = .ok next

/-- Reflexive-transitive closure of successful steps. -/
inductive Reachable : State → State → Prop where
  | refl (s : State) : Reachable s s
  | step {s middle next : State} :
      Reachable s middle → Step middle next → Reachable s next

end HederaStablecoin
