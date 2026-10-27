# Hedera Stablecoin — Formal Models

[![Formal models](https://github.com/kbak/hedera-stable-coin-formal-model/actions/workflows/verify.yml/badge.svg?branch=master)](https://github.com/kbak/hedera-stable-coin-formal-model/actions/workflows/verify.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-blue)](lean/lean-toolchain)
[![K 7.1.337](https://img.shields.io/badge/K-7.1.337-blue)](k-framework/Makefile)

**Executable formal models of Hedera's HCS stablecoin in K Framework and Lean 4.**

Explore the transaction semantics, run examples, and check proofs of supply
conservation, authorization, and operation effects. This repository concerns the
historical Hedera Consensus Service stablecoin described in
[Quantstamp's 2020 case study](https://quantstamp.com/blog/quantstamp-stablecoin-case-study-formally-verifying-hedera-hashgraphs-stablecoin-framework).

## Models

| Directory | Contents |
| --- | --- |
| [`k-framework/`](k-framework/README.md) | Original specification, updated for K's Haskell backend; 57 claims, including regression proofs for a corrected delegated-transfer rejection rule. |
| [`lean/`](lean/README.md) | Fresh initialization and all 17 state-changing operations; invariant proofs and executable examples, using only Lean's standard library. |

Lean proves that successful transaction sequences preserve balance/supply equality,
bounded supply, and nonzero roles. It is a manually reconstructed reference model;
K/Lean equivalence and Java implementation verification are outside its scope.
See the [model assumptions](lean/README.md#relationship-to-k) for the precise boundaries.

## Check the models

With [elan](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/kbak/hedera-stable-coin-formal-model.git
cd hedera-stable-coin-formal-model/lean
lake build
```

The pinned toolchain checks every Lean proof and example. Start reading with
[examples](lean/HederaStablecoin/Examples.lean), then the
[model](lean/HederaStablecoin/Model.lean) and
[invariant proofs](lean/HederaStablecoin/Invariants.lean).

To check all K claims with Docker, run from the repository root:

```sh
make -C k-framework docker-verify
```

[CI](.github/workflows/verify.yml) checks both models.
[K build instructions](k-framework/README.md) cover local installation and individual proofs.

## Background and license

Jan Gorzny, Kacper Bak, Ed Zulkoski, and Don Ho of Quantstamp developed the
[original formalization](https://github.com/hashgraph/hedera-stable-coin-formal-model),
based on Grigore Rosu's [ERC-20 Formal Model](https://github.com/runtimeverification/erc20-semantics).
Kacper Bak maintains this fork and its Lean formalization as an independent continuation.
The original license terms and attribution notices are retained in [LICENSE](LICENSE).

The historical Java implementation survives in
[this pinned revision](https://github.com/thomascherickal/hedera-stable-coin/tree/01cfd8cae395bad358f699dda4c6688ca6917965).
Hedera Token Service and Stablecoin Studio are outside this project's scope.

Questions or corrections are welcome through [issues](https://github.com/kbak/hedera-stable-coin-formal-model/issues).
