# NorinVerification

Formalization and CNF-generation utilities for the Norin conjecture encodings in Lean 4.

## Prerequisites

1. Lean toolchain from `lean-toolchain`
2. Lake (bundled with Lean)

## Build

```bash
lake build
```

## CNF generation

The executable is `NorinCNFGen` (see `Main.lean`).

### Generate both `Phi_n` and `Psi_n`

```bash
lake exe NorinCNFGen -n 7
```

This writes:
- `phi7.cnf`
- `psi7.cnf`



### Generate conjecture 2 encoding with symmetry-breaking controls

```bash
lake exe NorinCNFGen -n 7 --simplified-conjecture2 --tmp-file n7sb.cnf --partial-sym-break 20
```

Optional flag:
- `--first-vertex-min-degree`

## SAT solver usage

Example with Kissat:

```bash
kissat phi7.cnf
kissat psi7.cnf
```

## Main Lean modules

- `NorinVerification/NorinCNF.lean`: core CNF model and correctness statements for `Phi_n` / `Psi_n`
- `NorinVerification/NorinSimplified.lean`: simplified encoder and related lemmas
- `NorinVerification/SymmetryBreaking.lean`: symmetry-breaking formalization
- `NorinVerification/SimplifiedSymmetryBreaking.lean`: simplified symmetry-breaking theorems
- `NorinVerification/Cnf.lean`: CNF infrastructure
- `NorinVerification/fHat.lean`: auxiliary formalization for the `fHat` side results

## Entry points

- Library root: `NorinVerification.lean`
- CLI: `Main.lean`
- Lake configuration: `lakefile.toml`
