/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Shortest lattice vectors, greedy flags and Blichfeldt's bound

## Main results

* `ZLattice.exists_shortest_vector_notMem`: if a real subspace `U` of a finite-dimensional
  normed space does not contain the full-rank lattice `L`, some vector of `L` outside `U` has
  minimal norm among the vectors of `L` outside `U`. Iterating this gives the greedy
  successive-minima flag of `L`.
* `ZLattice.measureReal_le_covolume`: Blichfeldt's principle; a measurable set whose distinct
  points never differ by a lattice vector has volume at most the covolume.

The greedy flag is built one vector at a time with `Fin.snoc`; the following lemmas describe the
initial segments of such a tuple, and count the pairs of its indices:

* `Fin.snoc_image_Iio_castSucc`: `Fin.snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i`.
* `Fin.snoc_image_Iio_last`: `Fin.snoc v x '' Set.Iio (Fin.last k) = Set.range v`.
* `Fin.sum_card_Ioi`: there are `n.choose 2` pairs `i < j` in `Fin n`.
-/

namespace Fin

variable {α : Type*} {k : ℕ}

variable (v : Fin k → α) (x : α)

/-- Below `i.castSucc`, `Fin.snoc v x` takes the same values as `v` below `i`. -/
theorem snoc_image_Iio_castSucc (i : Fin k) :
    snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i := by
  rw [← image_castSucc_Iio, Set.image_image]
  simp

/-- Below `Fin.last k`, `Fin.snoc v x` takes exactly the values of `v`. -/
theorem snoc_image_Iio_last :
    snoc v x '' Set.Iio (last k) = Set.range v := by
  have h : Set.Iio (last k) = Set.range castSucc := by aesop
  rw [h, ← Set.range_comp, snoc_comp_castSucc]

end Fin

namespace ZLattice

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a real subspace `U` does not contain the full-rank lattice `L`, some lattice vector outside
`U` has minimal norm among all lattice vectors outside `U`. -/
theorem exists_shortest_vector_notMem
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (U : Submodule ℝ E) (hU : U ≠ ⊤) :
    ∃ v : E, v ∈ L ∧ v ∉ U ∧
      ∀ x : E, x ∈ L → x ∉ U → ‖v‖ ≤ ‖x‖ := by
  have hex : ∃ x : E, x ∈ L ∧ x ∉ U := by
    by_contra! h
    have hh := Submodule.span_le.mpr h
    rw [IsZLattice.span_top] at hh
    grind
  obtain ⟨x₀, hx₀, hx₀U⟩ := hex
  let S : Set E := {x | x ∈ L ∧ x ∉ U ∧ ‖x‖ ≤ ‖x₀‖}
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S norm (by
    have hf : (Metric.closedBall 0 ‖x₀‖ ∩ (L : Set E)).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall L.toAddSubgroup.isClosed_of_discreteTopology
    exact hf.subset fun x hx => ⟨by aesop, hx.1⟩) ⟨x₀, hx₀, hx₀U, le_rfl⟩
  refine ⟨v, hv.1, hv.2.1, ?_⟩
  intro x hx hxU
  by_cases hh : ‖x‖ ≤ ‖x₀‖
  · grind
  · grind

open MeasureTheory in
/-- Blichfeldt's principle: a measurable set whose distinct points never differ by a lattice vector
has volume at most the covolume of the lattice. -/
theorem measureReal_le_covolume [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {S : Set E} (hS : MeasurableSet S)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ L → x = y) :
    μ.real S ≤ ZLattice.covolume L μ := by
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF := ZLattice.isAddFundamentalDomain b μ
  have hle : μ S ≤ μ F := by
    by_contra! hlt
    let : MeasurableVAdd L E := inferInstanceAs (MeasurableVAdd L.toAddSubgroup E)
    let : VAddInvariantMeasure L E μ :=
      inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
    obtain ⟨a, b, hab, hdis⟩ :=
      exists_pair_mem_lattice_not_disjoint_vadd hF hS.nullMeasurableSet hlt
    obtain ⟨z, ⟨x, hx, hax⟩, y, hy, hby⟩ := Set.not_disjoint_iff.mp hdis
    change a + x = z at hax
    change b + y = z at hby
    have hdiff : x - y = b - a := by grind
    have hxy := hsep x hx y hy (hdiff ▸ L.sub_mem b.property a.property)
    grind
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hF]
  exact ENNReal.toReal_mono
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne hle

