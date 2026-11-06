/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# A lattice basis adapted to a flag

Let `L` be a discrete `ℤ`-submodule of a finite-dimensional real normed space `E`, and let
`v 0, …, v (n - 1)` be `ℝ`-linearly independent vectors of `L`, with `n = finrank ℝ E`. This file
builds a `ℤ`-basis `b 0, …, b (n - 1)` of `L` adapted to the flag the `v i` span: for every `j`,
the first `j` members of `b` are a `ℤ`-basis of `L ∩ span ℝ (v 0, …, v (j - 1))`.

## Main definitions

* `ZLattice.flagPart`: the `j`-th step `L ∩ span ℝ (v 0, …, v (j - 1))` of the flag, as a
  `ℤ`-submodule. The construction below is an induction along it, and so is the basis from the
  successive minima of Layer 4.6.

## Main results

* `ZLattice.exists_basis_adapted`: the adapted basis, stated both integrally — the `ℤ`-span of the
  first `j` basis vectors is exactly the part of `L` in the span of the first `j` of the `v i` —
  and in the weaker `ℝ`-form, that the two flags of subspaces coincide.
* `ZLattice.exists_basis_mem_span_int_of_mem_span_real`: the consequence the geometry of numbers
  uses, that a lattice point in the span of the first `j` of the `v i` is an *integer* combination
  of the first `j` basis vectors.
* `ZLattice.exists_extending`: the induction step in isolation — across a saturated step of rank
  one, a single vector `y` generates the quotient, in the form `Basis.mkFinSnocOfLE` consumes.
* `ZLattice.extending_congr`: that generating vector is determined only modulo the smaller
  module, which is the freedom Layer 4.6 spends on making the new basis vector short.
* `ZLattice.discreteTopology_of_le` and `ZLattice.finrank_int_eq_finrank_real`: the two facts about
  a submodule of a discrete lattice that the construction rests on, stated at arbitrary rank — it
  is discrete, and its `ℤ`-rank is the `ℝ`-dimension of its span. Minkowski's second theorem needs
  both for the sublattices cut out by the flag.

## Implementation notes

The construction is the modern one and not Cassels': the part `flagPart L v j` of `L` in the
`j`-th subspace of the flag is saturated in `flagPart L v (j + 1)` — no nonzero multiple of a
lattice point lies in it unless the point does, because the subspaces are `ℝ`-subspaces — so the
quotient is finitely generated and torsion-free, hence free, and its rank is `1` by the
rank-nullity theorem. A generator of that quotient extends a basis of `flagPart L v j` to a basis
of `flagPart L v (j + 1)` through Mathlib's `Basis.mkFinSnocOfLE`, and `n` steps reach `L` itself.

⚠ **All the analysis is in one rank computation.** Discreteness is used twice: to know that the
parts of `L` are finitely generated over `ℤ`, which is Mathlib's
`instModuleFinite_of_discrete_submodule`, and — indispensably — for
`finrank ℤ (flagPart L v j) = finrank ℝ (span ℝ (flagPart L v j))`, which is Mathlib's
`Real.finrank_eq_int_finrank_of_discrete`. A non-discrete subgroup such as `ℤ + ℤ √2 ⊆ ℝ` is
finitely generated but has `ℤ`-rank larger than the dimension of its span, and then the quotients
above are free of rank `> 1` and no single vector extends the basis. The induction step is
therefore stated with no topology at all: it asks for the rank as a hypothesis.

⚠ **`IsZLattice ℝ L` is not needed.** The independent family already spans `E` over `ℝ`, so a
lattice that contains it spans `E`; asking for the instance would be asking for a consequence of
the hypotheses.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter I,
Theorem I: for a sublattice `Λ` of a lattice `M` and a basis `a 1, …, a n` of `Λ`, a basis
`b 1, …, b n` of `M` with `a i = ∑_{j ≤ i} v i j • b j` and `v i i ≠ 0` (part B; part A is the
converse, the Hermite normal form of a sublattice). That triangular shape is the `ℝ`-form below,
and the integral form follows from it because the `b i` are a basis of `M`.

This is the lattice content of Chapter VIII, Lemma 2 — the basis such that `F x < λ i` forces `x`
to be an integer combination of `b 1, …, b (i - 1)` — which is Cassels' Theorem I of Chapter I
applied to the family of Lemma 1, the family realizing the successive minima.

This is infrastructure for Layers 4.2 and 4.6 of the `ArithmeticHeights` roadmap.
-/

public section

open Module Set Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ZLattice

/-! ### Discreteness and rank -/

omit [NormedSpace ℝ E] in
/-- A `ℤ`-submodule of a discrete one is discrete: the inclusion is a continuous injection. This
is stated for a submodule of arbitrary rank, which is what the sublattices cut out by a flag of
subspaces need; Mathlib's instances for lattices assume full rank. -/
theorem discreteTopology_of_le {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) :
    DiscreteTopology N := by
  refine DiscreteTopology.of_continuous_injective (f := fun x : N ↦ (⟨(x : E), h x.2⟩ : L))
    (continuous_subtype_val.subtype_mk _) fun x y hxy ↦ ?_
  have hxy' : (x : E) = (y : E) := congrArg (fun z : L ↦ (z : E)) hxy
  exact Subtype.ext hxy'

/-- The `ℤ`-rank of a submodule of a discrete lattice is the `ℝ`-dimension of its span. This is
the step discreteness is indispensable for: `ℤ + ℤ √2` has `ℤ`-rank two inside a line. -/
theorem finrank_int_eq_finrank_real [FiniteDimensional ℝ E] {L N : Submodule ℤ E}
    [DiscreteTopology L] (h : N ≤ L) : finrank ℤ N = finrank ℝ (span ℝ (N : Set E)) := by
  have hdisc : DiscreteTopology (span ℤ (N : Set E)) := by
    rw [Submodule.span_eq]
    exact discreteTopology_of_le h
  have h2 := Real.finrank_eq_int_finrank_of_discrete hdisc
  rw [Set.finrank, Set.finrank, Submodule.span_eq] at h2
  exact h2.symm

/-! ### The flag of an independent family -/

/-! ### The induction step -/

/-! ### The adapted basis -/

end ZLattice
