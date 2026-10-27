requires "hcs.k"

module TRANSFER-FROM-REGRESSION-SPEC
  imports HCS

  // A distinct-account transfer with insufficient allowance must reject.
  claim <k> transferFrom(2, 5, 1, {caller: 3}) => throw ...</k>
        <tokenOwner> 1 </tokenOwner>
        <allowance>
          <allower> 2 </allower>
          <spenders> 3 |-> 0 </spenders>
        </allowance>
        <balances> (2 |-> 100) (5 |-> 0) </balances>
        <kycpassed> (2 |-> true) (3 |-> true) (5 |-> true) </kycpassed>
        <frozen> (2 |-> false) (3 |-> false) (5 |-> false) </frozen>
    [label(distinct-insufficient-allowance)]

  // Cover every failure guard with distinct source, recipient, and spender.
  claim <k> transferFrom(2, 5, Value:Int, {caller: 3}) => throw ...</k>
        <tokenOwner> Owner:Int </tokenOwner>
        <allowance>
          <allower> 2 </allower>
          <spenders> 3 |-> Allowance:Int </spenders>
        </allowance>
        <balances> (2 |-> Balance:Int) (5 |-> _RecipientBalance:Int) </balances>
        <kycpassed> (2 |-> FromKyc:Bool) (3 |-> CallerKyc:Bool) (5 |-> ToKyc:Bool) </kycpassed>
        <frozen> (2 |-> FromFrozen:Bool) (3 |-> CallerFrozen:Bool) (5 |-> ToFrozen:Bool) </frozen>
    requires Owner ==Int 0 orBool Value <Int 0
      orBool Balance <Int Value orBool Allowance <Int Value
      orBool (notBool FromKyc) orBool (notBool CallerKyc) orBool (notBool ToKyc)
      orBool FromFrozen orBool CallerFrozen orBool ToFrozen
    [label(distinct-invalid)]

  // Self-transfer rejection must work without a third account in the maps.
  claim <k> transferFrom(2, 2, Value:Int, {caller: 3}) => throw ...</k>
        <tokenOwner> Owner:Int </tokenOwner>
        <allowance>
          <allower> 2 </allower>
          <spenders> 3 |-> Allowance:Int </spenders>
        </allowance>
        <balances> 2 |-> Balance:Int </balances>
        <kycpassed> (2 |-> FromKyc:Bool) (3 |-> CallerKyc:Bool) </kycpassed>
        <frozen> (2 |-> FromFrozen:Bool) (3 |-> CallerFrozen:Bool) </frozen>
    requires Owner ==Int 0 orBool Value <Int 0
      orBool Balance <Int Value orBool Allowance <Int Value
      orBool (notBool FromKyc) orBool (notBool CallerKyc)
      orBool FromFrozen orBool CallerFrozen
    [label(self-invalid)]

  // An unrelated frozen account cannot reject a valid self-transfer.
  // Balances stay fixed, but allowance is still consumed.
  claim <k> transferFrom(2, 2, Value:Int, {caller: 3}) => .K ...</k>
        <tokenOwner> 1 </tokenOwner>
        <allowance>
          <allower> 2 </allower>
          <spenders> 3 |-> (Allowance:Int => Allowance -Int Value) </spenders>
        </allowance>
        <balances> 2 |-> Balance:Int </balances>
        <kycpassed> (2 |-> true) (3 |-> true) (5 |-> false) </kycpassed>
        <frozen> (2 |-> false) (3 |-> false) (5 |-> true) </frozen>
    requires Value >=Int 0 andBool Balance >=Int Value andBool Allowance >=Int Value
    [label(self-ignores-unrelated-account)]

endmodule
