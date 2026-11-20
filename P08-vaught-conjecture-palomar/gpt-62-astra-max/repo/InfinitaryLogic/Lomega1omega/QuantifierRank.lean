/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Operations
public import PalomarProof.Infinitary.QuantifierRank
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Lω₁ω Quantifier Rank

This file defines the quantifier rank of Lω₁ω formulas and the "agree up to rank α"
relation between structures.

## Main Definitions

- `BoundedFormulaω.qrank`: The quantifier rank of an Lω₁ω formula.
- `EquivQRω`: Two structures are equivalent up to quantifier rank α if they satisfy
  the same sentences of quantifier rank ≤ α.

## Main Results

- `EquivQRω.refl`, `EquivQRω.symm`, `EquivQRω.trans`: Equivalence relation properties.
- `EquivQRω.monotone`: Higher rank equivalence implies lower rank equivalence.
- `qrank_einf`, `qrank_esup`: Quantifier rank of encoded infinitary connectives.
- `qrank_castLE`, `BoundedFormulaω.qrank_relabel`, `BoundedFormulaω.qrank_mapFreeVars`: the
  variable operations preserve quantifier rank.
- `BoundedFormula.qrank_toLω_lt_omega0`: the `Lω₁ω` image of a first-order formula has finite
  quantifier rank.
- `BoundedFormulaω.qrank_lt_omega1`, `Sentenceω.qrank_lt_omega1`: every `Lω₁ω` formula has
  countable quantifier rank, for every language.

## References

- [Mar16]
- [KK04]
-/

@[expose] public section

universe u v w w' u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Ordinal

/-! ### Quantifier Rank -/

/-- The quantifier rank of an Lω₁ω formula: the carrier-generic
`BoundedFormulaInf.qrank`, specialized at the branching carrier `ℕ`.

Because the rank is valued in the carrier's own ordinal universe, the `ℕ` specialization
lands in `Ordinal.{0}` exactly — no lifting, which is what Scott analysis needs.

This is an `abbrev`, so it is the upstream rank rather than a parallel copy of it (gated by
`rfl` below). The ω-facing lemmas beneath keep their historical statements: `qrank_all` and
`qrank_ex` are still stated with `+ 1` rather than `Order.succ`, so downstream sees no
proposition-level change. Only code that relied on the old definition unfolding by `rfl` is
affected.

The quantifier rank of an `Lω₁ω` formula is always a countable ordinal (`< ω₁`):
`BoundedFormulaω.qrank_lt_omega1`. -/
noncomputable abbrev BoundedFormulaω.qrank : L.BoundedFormulaω α n → Ordinal.{0} :=
  BoundedFormulaInf.qrank

/-- Quantifier rank of a sentence. -/
noncomputable abbrev Sentenceω.qrank (φ : L.Sentenceω) : Ordinal.{0} :=
  BoundedFormulaω.qrank φ

/-! ### Gate: the ω rank IS the upstream rank

Must close by `rfl` — that is what certifies this is the carrier-generic rank specialized at `ℕ`
rather than a parallel recursive copy that happens to agree. -/

/-! ### Quantifier Rank Lemmas -/

/-! ### The first-order image has finite rank -/

/-! ### The rank is countable -/

/-- **Every `Lω₁ω` formula has countable quantifier rank.**  Atoms have rank `0`, implication
takes the maximum, a quantifier adds one, and the countable connectives take a supremum over `ℕ`,
which stays below `ω₁` by regularity of `ℵ₁`.  No hypothesis on the language. -/
theorem BoundedFormulaω.qrank_lt_omega1 {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n), φ.qrank < Ordinal.omega 1
  | _, .falsum => Ordinal.omega_pos 1
  | _, .equal _ _ => Ordinal.omega_pos 1
  | _, .rel _ _ => Ordinal.omega_pos 1
  | _, .imp φ ψ => by
    exact max_lt (qrank_lt_omega1 φ) (qrank_lt_omega1 ψ)
  | _, .all φ => by
    exact (Cardinal.isSuccLimit_omega 1).add_one_lt (qrank_lt_omega1 φ)
  | _, .iSup φs => by
    exact Ordinal.iSup_lt_omega_one fun k ↦ qrank_lt_omega1 (φs k)
  | _, .iInf φs => by
    exact Ordinal.iSup_lt_omega_one fun k ↦ qrank_lt_omega1 (φs k)

/-! ### Equivalence up to Quantifier Rank -/

end Language

end FirstOrder
