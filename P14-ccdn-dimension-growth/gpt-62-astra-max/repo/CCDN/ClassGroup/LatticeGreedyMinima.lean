/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
import CCDN.ForMathlib.ZLattice

/-! Greedy successive minima: at each step choose a shortest lattice vector
outside the real span of the preceding vectors. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure GreedyLatticeFamily (L : Submodule ℤ E) {k : ℕ} (v : Fin k → E) : Prop where
  independent : LinearIndependent ℝ v
  mem : ∀ i, v i ∈ L
  norm_le : ∀ i x, x ∈ L → x ∉ span ℝ (v '' Set.Iio i) → ‖v i‖ ≤ ‖x‖

/-- The successive minima are already monotone. -/
theorem GreedyLatticeFamily.monotone {L : Submodule ℤ E} {k : ℕ} {v : Fin k → E}
    (h : GreedyLatticeFamily L v) : Monotone fun i => ‖v i‖ :=
  fun _ j hij => h.norm_le _ _ (h.mem j) (h.independent.notMem_span_image (not_lt_of_ge hij))

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem exists_greedy_family (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∃ v : Fin k → E, GreedyLatticeFamily L v := by
  induction k with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih (by omega)
    have hU : span ℝ (Set.range v) ≠ ⊤ := by
      have := finrank_span_eq_card hv.independent
      grind [finrank_top, Fintype.card_fin]
    obtain ⟨x, hx, hxU, hmin⟩ := ZLattice.exists_shortest_vector_notMem L _ hU
    refine ⟨Fin.snoc v x, hv.independent.finSnoc hxU, ?_, ?_⟩
    · exact Fin.lastCases (by simpa) (fun i => by simpa using hv.mem i)
    · exact Fin.lastCases (by simpa [Fin.snoc_image_Iio_last] using hmin) (fun i => by
        simpa [Fin.snoc_image_Iio_castSucc] using hv.norm_le i)

/-- A full lattice admits a basis realizing its successive minima. -/
theorem exists_greedy_lattice_basis {n : ℕ} (hn : Module.finrank ℝ E = n) :
    ∃ b : Basis (Fin n) ℝ E, GreedyLatticeFamily L b := by
  obtain ⟨v, hv⟩ := exists_greedy_family L n hn.ge
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simpa using hn.symm)
  exact ⟨b, by simpa [b] using hv⟩

end
end CCDN
