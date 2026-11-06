/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/

import ArithmeticHeights.Absolute
import ArithmeticHeights.Arakelov
import ArithmeticHeights.Plucker

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

open Module

/-!
### Two lemmas that belong upstream

`Set.powersetCard.nontrivial_iff` is in Mathlib; its negation is not, and it is what makes the two
degenerate ranks of a subspace height degenerate. Mathlib's `Projectivization.mulHeight` has no
subsingleton lemma either, although the tuple-level `Height.mulHeight_eq_one_of_subsingleton` is
there.
-/

namespace Submodule

open exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}
  {V : Submodule K (ι → K)}

/-!
### The height of a subspace
-/

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

theorem arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint (hV : finrank K V = k) :
    V.arakelovMulHeight = Projectivization.arakelovMulHeight (V.pluckerPoint hV) := by
  subst hV
  rfl

/-- **The Arakelov height of the span of a linearly independent family is the Arakelov height of
its tuple of maximal minors.** -/
theorem arakelovMulHeight_span_range {v : Fin k → (ι → K)} (hv : LinearIndependent K v) :
    (span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (plucker k v) := by
  have hV :=
    (finrank_span_eq_card hv).trans (Fintype.card_fin k)
  rw [arakelovMulHeight_eq_arakelovMulHeight_pluckerPoint hV, (show pluckerPoint (Submodule.span K (Set.range v)) hV =
        Projectivization.mk K (plucker k v) (plucker_ne_zero hv) by
      have hfun :=
        funext fun i ↦ congrArg Subtype.val (Basis.span_apply hv i)
      rw [pluckerPoint_eq_mk hV (Basis.span hv) (by rw [hfun]; exact plucker_ne_zero hv)]
      simp),
    Projectivization.arakelovMulHeight_mk]

/-!
### The absolute height of a subspace

The variant that does not depend on the field the subspace is written over; it is the one the
literature's `h(V)` is, and one of the six Northcott statements of 3.7.
-/

/-!
### Worked examples
-/

