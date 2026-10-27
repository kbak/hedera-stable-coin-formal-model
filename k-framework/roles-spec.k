requires "hcs.k"

module ROLES-SPEC
  imports HCS

/*
  Owner can propose a new owner.

  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * ProposedOwner = addr
*/
claim <k> proposeOwner(ProposedOwner, { caller : Caller } ) => .K ...</k>
     <tokenOwner> Caller </tokenOwner>
     <proposedOwner> _ => ProposedOwner </proposedOwner>
     <kycpassed> ... (ProposedOwner |-> true) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ProposedOwner =/=Int 0

/*
  Proposing owner twice ignores the first call.

  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * ProposedOwner1 != 0x
      * ProposedOwner2 != 0x
      * CheckTransferAllowed(ProposedOwner1)
      * CheckTransferAllowed(ProposedOwner2)

  Post-conditions
      * ProposedOwner = ProposedOwner2
*/
claim <k> proposeOwner(ProposedOwner1, { caller : Caller } )
         ~>
         proposeOwner(ProposedOwner2, { caller : Caller } ) => .K ...</k>
     <tokenOwner> Caller </tokenOwner>
     <proposedOwner> _ => ProposedOwner2 </proposedOwner>
     <kycpassed> ... (ProposedOwner1 |-> true)(ProposedOwner2 |-> true) ... </kycpassed>
     <frozen> ... (ProposedOwner1 |-> false)(ProposedOwner2 |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ProposedOwner1 =/=Int 0 andBool ProposedOwner2 =/=Int 0

// non-owner cannot propose a new owner
claim <k> proposeOwner(ProposedOwner:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <kycpassed> ... (ProposedOwner |-> _:Bool) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> _:Bool) ... </frozen>
  requires TokenOwner =/=Int Caller

/*
  Proposed owner can claim ownership and the proposed owner is then reset.

  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * ProposedOwner = 0
      * Owner = addr
*/
claim <k> proposeOwner(ProposedOwner, { caller : Caller } )
         ~>
         claimOwnership( { caller : ProposedOwner } ) => .K ...</k>
     <tokenOwner> Caller => ProposedOwner </tokenOwner>
     <proposedOwner> _ => 0 </proposedOwner>
     <kycpassed> ... (ProposedOwner |-> true) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ProposedOwner =/=Int 0

// nobody besides the proposed owner can claim ownership
claim <k> proposeOwner(ProposedOwner:Int, { caller : Caller:Int } )
         ~>
         claimOwnership( { caller : AnotherCaller:Int } ) => throw ...</k>
     <tokenOwner> Caller </tokenOwner>
     <proposedOwner> _ => ProposedOwner </proposedOwner>
     <kycpassed> ... (ProposedOwner |-> true)(AnotherCaller |-> _:Bool) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> false)(AnotherCaller |-> _:Bool) ... </frozen>
  requires Caller =/=Int 0
    andBool AnotherCaller =/=Int 0
    andBool ProposedOwner =/=Int 0
    andBool ProposedOwner =/=Int AnotherCaller

/*
  Owner can change supply manager

  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * SupplyManager = addr
*/
claim <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => .K ...</k>
     <tokenOwner> Caller </tokenOwner>
     <supplyManager> _ => SupplyManager </supplyManager>
     <kycpassed> ... (SupplyManager |-> true) ... </kycpassed>
     <frozen> ... (SupplyManager |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool SupplyManager =/=Int 0

// non-owner cannot change supply manager
claim <k> changeSupplyManager(SupplyManager:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <kycpassed> ... (SupplyManager |-> _:Bool) ... </kycpassed>
     <frozen> ... (SupplyManager |-> _:Bool) ... </frozen>
  requires TokenOwner =/=Int Caller

/*
  Owner can change compliance manager.

  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * ComplianceManager = addr
 */
claim <k> changeComplianceManager(ComplianceManager, { caller : Caller } ) =>  .K ...</k>
     <tokenOwner> Caller </tokenOwner>
     <complianceManager> _ => ComplianceManager </complianceManager>
     <kycpassed> ... (ComplianceManager |-> true) ... </kycpassed>
     <frozen> ... (ComplianceManager |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ComplianceManager =/=Int 0

// non-owner cannot change compliance manager
claim <k> changeComplianceManager(ComplianceManager:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <kycpassed> ... (ComplianceManager |-> _:Bool) ... </kycpassed>
     <frozen> ... (ComplianceManager |-> _:Bool) ... </frozen>
  requires TokenOwner =/=Int Caller

  /*
    Owner can change enforcement manager.

    Pre-conditions
        * Owner != 0x
        * caller = Owner
        * addr != 0x
        * CheckTransferAllowed(addr)

    Post-conditions
        * EnforcementManager = addr
   */
  claim <k> changeEnforcementManager(EnforcementManager, { caller : Caller } ) =>  .K ...</k>
       <tokenOwner> Caller </tokenOwner>
       <enforcementManager> _ => EnforcementManager </enforcementManager>
       <kycpassed> ... (EnforcementManager |-> true) ... </kycpassed>
       <frozen> ... (EnforcementManager |-> false) ... </frozen>
    requires Caller =/=Int 0 andBool EnforcementManager =/=Int 0

  // non-owner cannot change enforcement manager
  claim <k> changeEnforcementManager(EnforcementManager:Int, { caller : Caller } ) => throw ...</k>
       <tokenOwner> TokenOwner </tokenOwner>
       <kycpassed> ... (EnforcementManager |-> _:Bool) ... </kycpassed>
       <frozen> ... (EnforcementManager |-> _:Bool) ... </frozen>
    requires TokenOwner =/=Int Caller

endmodule
