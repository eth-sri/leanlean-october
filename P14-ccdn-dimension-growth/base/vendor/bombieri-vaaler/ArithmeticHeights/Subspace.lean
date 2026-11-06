/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Absolute
public import ArithmeticHeights.Arakelov
public import ArithmeticHeights.Plucker

/-!
# The height of a linear subspace

Schmidt's height of a subspace `V : Submodule K (ι → K)`: the height of its Plücker point
`Submodule.pluckerPoint`, a point of `Projectivization K (Set.powersetCard ι k → K)`, in each of
the three normalizations the roadmap carries — Mathlib's sup-norm height, the Arakelov height of
Layer 0.1, and the absolute height of Layer 0.4 — with the logarithmic form of each alongside.

The definition is Bombieri–Gubler 2.8.4 and Schmidt 1967, §1. What makes it the right definition
is `Submodule.mulHeight_span_singleton`: the height of a line is the projective height of the
point that spans it.

## Main definitions

* `Submodule.mulHeight`, `Submodule.logHeight`: the height of a subspace of `ι → K`, over any
  field with `Height.AdmissibleAbsValues`.
* `Submodule.arakelovMulHeight`, `Submodule.arakelovLogHeight`: the ℓ²-at-infinity variant, over a
  number field.
* `Submodule.absMulHeight`, `Submodule.absLogHeight`: the absolute variant, over a field of
  algebraic numbers.

## Main results

* `Submodule.mulHeight_span_singleton`: `Submodule.mulHeight (span K {x}) = Height.mulHeight x`
  for `x ≠ 0`, and the same for the other three heights. This is the compatibility that fixes the
  definition; it is `exteriorPower.plucker_one_comp` of Layer 3.1 read through
  `Height.mulHeight_comp_equiv`.
* `Submodule.mulHeight_span_range`: the height of the span of a linearly independent family is
  the height of its tuple of Plücker coordinates, which by `exteriorPower.plucker_apply` is its
  tuple of maximal minors. This is the form the matrix dictionary of 3.3 consumes.
* `Submodule.mulHeight_bot` and `Submodule.mulHeight_top`: the two degenerate ranks, where the
  exterior power is a line, have height `1`.
* `Submodule.one_le_mulHeight`, and positivity and nonnegativity beside it.
* `Submodule.mulHeight_eq_mulHeight_pluckerPoint`: the definition, re-typed along any proof that
  the rank of `V` is `k`. Every proof enters through this rather than through the definition.
* `Submodule.absMulHeight_eq`: over a number field the absolute height of a subspace is the
  relative one normalized by the degree, as it is for tuples and for projective points.
* `Submodule.mulHeight_le_arakelovMulHeight`: the height of a subspace is at most its Arakelov
  height, the comparison of Layer 0.2 read at the Plücker point.

`Set.powersetCard.subsingleton_iff` and `Projectivization.mulHeight_eq_one_of_subsingleton` are
stated here because Mathlib has neither, although both are about Mathlib's own objects — the first
sits beside `Set.powersetCard.nontrivial_iff`, the second beside
`Projectivization.mulHeight`. They belong upstream rather than in this library.

## Implementation notes

The rank is not a parameter of the definition. `Submodule.mulHeight V` is
`Projectivization.mulHeight (V.pluckerPoint rfl)`, taking `k := Module.finrank K V`, so it is a
total function of `V` alone: `Submodule.mulHeight (V ⊓ W)` is well formed without producing a rank
for `V ⊓ W` first, which is what the submodularity of 3.6 needs.
`Submodule.mulHeight_eq_mulHeight_pluckerPoint` re-types it along an arbitrary
`hV : Module.finrank K V = k` — by `subst`, since `k` is a variable — and that lemma, not the
definition, is what every proof below uses.

Both degenerate cases are one argument, and neither is a computation of Plücker coordinates: for
`Module.finrank K V = 0` and for `Module.finrank K V = Fintype.card ι` the index type
`Set.powersetCard ι (Module.finrank K V)` is a subsingleton — only `∅`, only `Finset.univ` — so
every tuple over it has height `1` by the product formula. In particular `mulHeight ⊤ = 1` does
not go through `exteriorPower.plucker_fin_eq_det`, which is stated for `ι = Fin n`.

The four height families are separate sections rather than one definition parametrized by a
height, because their hypotheses differ: `Height.AdmissibleAbsValues K` for the first,
`NumberField K` for the Arakelov height, and `CharZero K` with `Algebra.IsAlgebraic ℚ K` for the
absolute one. As the roadmap's convention records, the duplication is in the statements only.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.8.4 for the height of a subspace and Definition 2.8.11 for its Arakelov normalization; their
`h(V)` and `h_Ar(V)` are absolute, ours relative, as everywhere in this development.
W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §1, where the height of a subspace is defined through its
Grassmann coordinates for the first time.

This is Layer 3.2 of the `ArithmeticHeights` roadmap.
-/

public section

open Module

/-!
### Two lemmas that belong upstream

`Set.powersetCard.nontrivial_iff` is in Mathlib; its negation is not, and it is what makes the two
degenerate ranks of a subspace height degenerate. Mathlib's `Projectivization.mulHeight` has no
subsingleton lemma either, although the tuple-level `Height.mulHeight_eq_one_of_subsingleton` is
there.
-/

namespace Set.powersetCard

/-- A type of `n`-element subsets is a subsingleton exactly when there is at most one such subset:
`n = 0`, when only `∅` qualifies, or `n` at least the cardinality, when only `Finset.univ` does.
This is the negation of `Set.powersetCard.nontrivial_iff`. -/
theorem subsingleton_iff {α : Type*} [Finite α] {n : ℕ} :
    Subsingleton (Set.powersetCard α n) ↔ n = 0 ∨ Nat.card α ≤ n := by
  rw [← not_nontrivial_iff_subsingleton, nontrivial_iff]
  omega

end Set.powersetCard

namespace Projectivization

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-- On a subsingleton index type every point of projective space has height `1`; the projective
form of `Height.mulHeight_eq_one_of_subsingleton`. -/
@[simp]
theorem mulHeight_eq_one_of_subsingleton [Subsingleton ι] (x : Projectivization K (ι → K)) :
    mulHeight x = 1 := by
  rw [← x.mk_rep, mulHeight_mk]
  exact Height.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_eq_zero_of_subsingleton [Subsingleton ι] (x : Projectivization K (ι → K)) :
    logHeight x = 0 := by
  simp [logHeight_eq_log_mulHeight]

end Projectivization

namespace Submodule

open exteriorPower

section Degenerate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {V : Submodule K (ι → K)}

/-- The index type of the Plücker coordinates collapses to a point exactly in the two degenerate
ranks. Every `= 1` statement below is this lemma followed by the product formula. -/
private lemma subsingleton_powersetCard_finrank
    (h : finrank K V = 0 ∨ Fintype.card ι ≤ finrank K V) :
    Subsingleton (Set.powersetCard ι (finrank K V)) :=
  Set.powersetCard.subsingleton_iff.2 (by rwa [Nat.card_eq_fintype_card])

end Degenerate

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

/-!
### The height of a subspace
-/

section Relative

variable [Height.AdmissibleAbsValues K]

/-- **The multiplicative height of a linear subspace of `ι → K`**: the projective height of its
Plücker point, following Schmidt. The rank is read off `V` rather than supplied, so this is a
total function of `V`. -/
noncomputable def mulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.mulHeight (V.pluckerPoint rfl)

/-- **The logarithmic height of a linear subspace of `ι → K`.** -/
noncomputable def logHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.logHeight (V.pluckerPoint rfl)

theorem logHeight_eq_log_mulHeight (V : Submodule K (ι → K)) :
    V.logHeight = Real.log V.mulHeight :=
  Projectivization.logHeight_eq_log_mulHeight _

/-- The zero subspace has height `1`: its exterior power is the line spanned by the empty wedge,
whose single coordinate is indexed by `∅`. -/
@[simp]
theorem mulHeight_bot : (⊥ : Submodule K (ι → K)).mulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (.inl (finrank_bot K (ι → K)))
  Projectivization.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_bot : (⊥ : Submodule K (ι → K)).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_bot, Real.log_one]

/-- The whole space has height `1`: its exterior power is the line spanned by the wedge of the
standard basis, whose single coordinate is indexed by `Finset.univ`. -/
@[simp]
theorem mulHeight_top : (⊤ : Submodule K (ι → K)).mulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (V := (⊤ : Submodule K (ι → K)))
    (.inr (by rw [finrank_top, finrank_fintype_fun_eq_card]))
  Projectivization.mulHeight_eq_one_of_subsingleton _

@[simp]
theorem logHeight_top : (⊤ : Submodule K (ι → K)).logHeight = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_top, Real.log_one]

end Relative

/-!
### The Arakelov height of a subspace

The same definition with the ℓ² norm at the archimedean places, which is the normalization the
Siegel-lemma literature states its constants in.
-/

section Arakelov

variable [NumberField K]

/-- **The multiplicative Arakelov height of a linear subspace of `ι → K`**, `H_Ar(V)` of
Bombieri–Gubler 2.8.11. -/
noncomputable def arakelovMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovMulHeight (V.pluckerPoint rfl)

/-- **The logarithmic Arakelov height of a linear subspace of `ι → K`.** -/
noncomputable def arakelovLogHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.arakelovLogHeight (V.pluckerPoint rfl)

theorem arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint (hV : finrank K V = k) :
    V.arakelovMulHeight = Projectivization.arakelovMulHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

theorem arakelovLogHeight_eq_log_arakelovMulHeight (V : Submodule K (ι → K)) :
    V.arakelovLogHeight = Real.log V.arakelovMulHeight :=
  Projectivization.arakelovLogHeight_eq_log_arakelovMulHeight _

@[simp]
theorem arakelovMulHeight_bot : (⊥ : Submodule K (ι → K)).arakelovMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (.inl (finrank_bot K (ι → K)))
  Projectivization.arakelovMulHeight_eq_one_of_subsingleton _

@[simp]
theorem arakelovLogHeight_bot : (⊥ : Submodule K (ι → K)).arakelovLogHeight = 0 := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_bot, Real.log_one]

@[simp]
theorem arakelovMulHeight_top : (⊤ : Submodule K (ι → K)).arakelovMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (V := (⊤ : Submodule K (ι → K)))
    (.inr (by rw [finrank_top, finrank_fintype_fun_eq_card]))
  Projectivization.arakelovMulHeight_eq_one_of_subsingleton _

@[simp]
theorem arakelovLogHeight_top : (⊤ : Submodule K (ι → K)).arakelovLogHeight = 0 := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovMulHeight_top, Real.log_one]

/-- **The Arakelov height of the span of a linearly independent family is the Arakelov height of
its tuple of maximal minors.** -/
theorem arakelovMulHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (plucker k v) := by
  have hV : finrank K (span K (Set.range v)) = k :=
    (finrank_span_eq_card hv).trans (Fintype.card_fin k)
  rw [arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint hV, pluckerPoint_span_range hv hV,
    Projectivization.arakelovMulHeight_mk]

end Arakelov

/-!
### The absolute height of a subspace

The variant that does not depend on the field the subspace is written over; it is the one the
literature's `h(V)` is, and one of the six Northcott statements of 3.7.
-/

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- **The absolute multiplicative height of a linear subspace of `ι → K`**, `h(V)` of
Bombieri–Gubler 2.8.4. -/
noncomputable def absMulHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.absMulHeight (V.pluckerPoint rfl)

/-- **The absolute logarithmic height of a linear subspace of `ι → K`.** -/
noncomputable def absLogHeight (V : Submodule K (ι → K)) : ℝ :=
  Projectivization.absLogHeight (V.pluckerPoint rfl)

theorem absLogHeight_eq_log_absMulHeight (V : Submodule K (ι → K)) :
    V.absLogHeight = Real.log V.absMulHeight :=
  Projectivization.absLogHeight_eq_log_absMulHeight _

@[simp]
theorem absMulHeight_bot : (⊥ : Submodule K (ι → K)).absMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (.inl (finrank_bot K (ι → K)))
  Projectivization.absMulHeight_eq_one_of_subsingleton _

@[simp]
theorem absLogHeight_bot : (⊥ : Submodule K (ι → K)).absLogHeight = 0 := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_bot, Real.log_one]

@[simp]
theorem absMulHeight_top : (⊤ : Submodule K (ι → K)).absMulHeight = 1 :=
  have := subsingleton_powersetCard_finrank (V := (⊤ : Submodule K (ι → K)))
    (.inr (by rw [finrank_top, finrank_fintype_fun_eq_card]))
  Projectivization.absMulHeight_eq_one_of_subsingleton _

@[simp]
theorem absLogHeight_top : (⊤ : Submodule K (ι → K)).absLogHeight = 0 := by
  rw [absLogHeight_eq_log_absMulHeight, absMulHeight_top, Real.log_one]

end Absolute

end Submodule

/-!
### Worked examples
-/

section Examples

open Submodule

end Examples

end
