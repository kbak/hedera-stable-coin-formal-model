# K Framework model

The original HCS stablecoin specification, updated for K 7.1.337 and its Haskell
proof backend, with the delegated-transfer correction below. See the
[repository overview](../README.md) for attribution and the companion Lean model.

## Build and prove

From the repository root, with Docker installed:

```sh
make -C k-framework docker-verify
```

This compiles the model and proves all 57 claims in ten specification files. The
[Makefile](Makefile) pins the official K 7.1.337 Ubuntu 24.04 image by version and
digest. Docker downloads it on first use; proof execution runs without network
access. Outputs belong to the calling user in the ignored `.build/` directory.

To compile only or prove one specification:

```sh
make -C k-framework docker-build
make -C k-framework docker-verify SPECS=mintable-spec.k
```

Successful prover invocations print `#Top`; failed proofs stop the build. Labeled
claims run individually, avoiding expensive mutual circularity search for the
seven cross-cutting claims. The build checks that every claim in a labeled file
has a label so none are silently omitted.

With [K 7.1.337](https://github.com/runtimeverification/k/releases/tag/v7.1.337)
and its dependencies installed locally, use `make -C k-framework` instead.
Run `make -C k-framework clean` before switching K versions. Docker includes the
matching solver dependencies.

## Changes from the historical version

The obsolete Ubuntu Bionic/Java toolchain is replaced by the Haskell backend.
Syntax updates use `claim` for proof obligations and `.K` for empty computations,
and remove the obsolete `unused="true"` cell attribute.

Role claims annotate anonymous KYC/freeze values as `_:Bool`, making their
well-typed-state assumption explicit; malformed flags are outside those claims.
Cross-cutting labels only affect proof selection. These toolchain changes retain
the transition semantics; original sources and build instructions remain in Git history.

## Delegated-transfer correction

The historical rejection rule matched `transferFrom(From, From, ...)` while
referencing an unrelated `To`. A transfer from account 2 to 5, caller 3, with zero
allowance reproduced a stuck configuration instead of `throw`.

Corrected rules separate distinct-account and self-transfer failures, checking
the actual recipient or only the source and caller, respectively. This also
prevents unrelated noncompliant accounts from rejecting valid self-transfers.
Successful transfer rules are unchanged.

[Four regression claims](transfer-from-regression-spec.k) cover the reproduction,
symbolic failure guards for both cases, and a valid self-transfer with an unrelated
noncompliant account. They check unchanged balances/allowances on failure and
allowance consumption without token movement on successful self-transfer.
The original 53 claims remain in the suite.

Original license terms and attribution notices remain in [LICENSE](../LICENSE).
