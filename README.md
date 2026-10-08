# Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields

Public materials for **Counterexamples to Beyond-Johnson Proximity Gaps over
Binary Fields**, by Quang Dao, Scott Duke Kominers, Justin Thaler, and
Kai Zhe Zheng.

Read the [paper](binary-field-counterexamples.pdf) for the constructions and
their consequences for hash-based SNARKs over binary fields. This repository
supplies the Lean formalization of its results and exact recomputations of its
concrete parameters.

## Lean formalization

The [Lean project](formalization/README.md) proves every numbered theorem,
proposition, corollary and lemma in the paper. Its 3,135 public declarations
are proved without `sorry`, and their axiom reports contain only Lean's
standard `propext`, `Classical.choice` and `Quot.sound`. The
[coverage table](formalization/README.md#coverage) maps each paper statement to
the Lean module and declarations that prove it.

Install [elan](https://github.com/leanprover/elan), then run:

```sh
cd formalization
lake exe cache get
lake build
```

Lake uses Lean 4.34.0 and pinned revisions of Mathlib and
[ArkLib](https://github.com/Verified-zkEVM/ArkLib). The expected result is
`Build completed successfully`. After the build, check the axiom boundary from
the repository root:

```sh
python3 scripts/check_lean_contract_axioms.py
```

## Concrete parameters

Two scripts recompute the finite parameters printed in the paper with exact
arithmetic, independently of the Lean proofs. They need only Python 3.10 or
newer:

```sh
python3 scripts/verify_main_parameters.py
python3 scripts/verify_fixed_extension.py
```

## Repository guide

| Material | Where to start |
|---|---|
| Results and proofs | [Paper](binary-field-counterexamples.pdf) |
| Paper statements mapped to Lean declarations | [Coverage table](formalization/README.md#coverage) |
| Main theorem statements in Lean | [`MainTheorems/`](formalization/BinaryFieldCounterexamples/MainTheorems) |
| Definitions of agreement, exceptional challenges and lists | [`PaperSemantics.lean`](formalization/BinaryFieldCounterexamples/PaperSemantics.lean) |

The paper's source is maintained privately. Please report corrections through
this repository's issues.

## License

The Lean formalization and scripts are licensed under **Apache-2.0**. The paper
and explanatory documentation are licensed under **CC BY 4.0**. See
[LICENSE.md](LICENSE.md).
