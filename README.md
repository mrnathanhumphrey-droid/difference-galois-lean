# Difference-Galois theory in Lean 4

A [Lean 4](https://leanprover.github.io/) + [mathlib](https://github.com/leanprover-community/mathlib4)
formalization of **difference (σ-) algebra** — difference rings and modules, their rigid tensor
structure, difference ideals, and the construction of a **Picard–Vessiot ring** for a linear
difference system `σ(Y) = A·Y` — together with one fully worked example: the level-1
difference-Galois group of the substitution `σ : z ↦ z³` over `ℚ(z)`.

The whole development **compiles with no `sorry` and no added axioms** on
`leanprover/lean4:v4.30.0` with the pinned mathlib revision (see `lean-toolchain` and
`lake-manifest.json`).

> The worked example arises from a research problem about the Syracuse/Collatz stationary
> measure. **That is the motivation, not a claim.** This repository proves theorems of
> difference algebra; it asserts *nothing* about the Collatz conjecture or the arithmetic
> nature of any Syracuse constant. See **Scope and non-claims** below.

## What is formalized

Everything below is stated and proved in Lean; the file each lives in is given.

**The difference-algebra foundations**
- `DiffGalois/Basic.lean` — `DifferenceRing R`: a commutative ring with a distinguished ring
  automorphism `σ`; the subring `constants` of `σ`-fixed elements.
- `DiffGalois/Module.lean` — `DifferenceModule`: an `R`-module with a `σ`-semilinear bijection
  `Φ` (`Φ (r • m) = σ r • Φ m`); `FiniteDifferenceModule`; `rank`.
- `DiffGalois/Matrix.lean` — the difference module attached to an invertible matrix `A` (the
  system `σ(Y) = A·Y`); `matrixToDiffModule`, with `matrixΦ` proved bijective.
- `DiffGalois/Dual.lean` — the dual of a difference module (`contraMap_bijective`, `dual`).
- `DiffGalois/Tensor.lean` — tensor products of difference modules and the unit object
  (`tensorΦ_bijective`, `tensor`, `unit`) — the rigid tensor structure.

**Picard–Vessiot theory**
- `DiffGalois/PicardVessiot.lean` — `IsDifferenceIdeal`, `IsSigmaSimple`,
  `exists_maximal_differenceIdeal` (a proper difference ideal is contained in a maximal one),
  and the predicate `IsPicardVessiot`.
- `DiffGalois/PicardVessiotRing.lean` — the universal solution ring `R₀ = k[X_ij, 1/det]` with
  its substitution automorphism `pvσ`; `genDet` is `σ`-associated to itself
  (`pvσ_genDet_associated`), giving the automorphism on the localization; and the headline
  existence theorem:
  - **`exists_isPicardVessiot`** — for an invertible `A`, the system `σ(Y) = A·Y` admits a
    Picard–Vessiot ring (a `σ`-simple quotient of `R₀[1/det]` realizing a full solution matrix).

**The worked example — `σ : z ↦ z³` on `ℚ(z)`**
- `DiffGalois/Coboundary.lean` — the σ-engine on `RatFunc ℚ` (`σ (X^n) = X^(3n)`), and the
  **coboundary criterion**:
  - **`W1`** — for a finitely supported family, `Σ_j r_j · z^(−2·3^j)` is a σ-coboundary
    (`∃ ψ, σ ψ − ψ = target`) **iff** `Σ_j r_j = 0`.
- `DiffGalois/QDiff2.lean` — the two facts that pin the level-1 group of this example:
  - **`QDiff2.P1_coboundary`** — `∃ y, σ y = z⁴ · y` (the diagonal scaling `z⁴` *is* a coboundary; the
    multiplicative/reductive part `𝔾ₘ` collapses).
  - **`QDiff2.P2_not_coboundary`** — `¬ ∃ ψ, σ ψ − ψ = z^(−2)` (the off-diagonal source is *not* a
    coboundary; the additive/unipotent part `𝔾ₐ` survives), via a `rootMultiplicity`/pole-order
    argument.

  Together these identify the level-1 difference-Galois group of the example as the additive
  group `𝔾ₐ` — a proper subgroup of the affine group `𝔾ₐ ⋊ 𝔾ₘ`.

## Main results at a glance

| Lean name | file | statement (informal) |
|---|---|---|
| `exists_isPicardVessiot` | `PicardVessiotRing.lean` | every invertible `σ(Y)=A·Y` has a Picard–Vessiot ring |
| `exists_maximal_differenceIdeal` | `PicardVessiot.lean` | a proper difference ideal sits in a maximal one |
| `W1` | `Coboundary.lean` | `Σ r_j z^(−2·3^j)` is a σ-coboundary ⇔ `Σ r_j = 0` |
| `QDiff2.P1_coboundary` | `QDiff2.lean` | `z⁴` is a σ-coboundary (`𝔾ₘ` collapses) |
| `QDiff2.P2_not_coboundary` | `QDiff2.lean` | `z^(−2)` is not a σ-coboundary (`𝔾ₐ` survives) |

## Scope and non-claims

This is a formalization of **standard difference-Galois machinery** plus **one computed
example**. To keep the record honest:

- **No claim about the Collatz conjecture.** Nothing here bears on whether Collatz orbits
  reach 1. The substitution `z ↦ z³` and the exponents `2·3^j` come from a Syracuse
  stationary-measure recurrence, but that is background motivation only.
- **No claim about the value or arithmetic type of any Syracuse constant.** The example
  computes a *Galois group of a difference module*; it does not evaluate, and makes no
  rationality/transcendence assertion about, any limit constant.
- **The example is level 1.** `P1`/`P2` pin the difference-Galois group of the level-1
  truncation. The full tower and any consequence for a limiting object are **not** part of
  this repository.
- **The Picard–Vessiot side is the ring-existence layer.** `exists_isPicardVessiot` constructs
  a PV ring; the full Galois-group/torsor correspondence is not formalized here.

If any of the difference-algebra constructions overlap existing or in-progress mathlib work,
please point it out — feedback is very welcome (see below).

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager); it will
fetch `leanprover/lean4:v4.30.0` from `lean-toolchain` automatically.

```sh
lake exe cache get     # download the pinned mathlib build (recommended; avoids compiling mathlib)
lake build             # builds the whole development
```

A successful run ends with `Build completed successfully`. The development has no `sorry` and
introduces no axioms beyond mathlib's.

## Feedback

Questions, corrections, and pointers to overlapping mathlib work are welcome via GitHub issues,
or on the [Lean Zulip](https://leanprover.zulipchat.com/).

## License

Apache License 2.0 — see `LICENSE`. © 2026 Nathan Humphrey.
