/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
import CCDN.ForMathlib.ZLattice

/-! Choose lattice vectors successively of minimum norm outside the previous span. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private lemma exists_greedy_lattice_family (n : ℕ) (hn : n ≤ finrank ℝ E) :
    ∃ b : Fin n → E, LinearIndependent ℝ b ∧ (∀ i, b i ∈ L) ∧
      ∀ i x, x ∈ L → x ∉ span ℝ (b '' Set.Iio i) → ‖b i‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨b, hi, hb, hmin⟩ := ih (by omega)
    have hs : span ℝ (Set.range b) ≠ ⊤ := by
      intro hh
      have he := finrank_span_eq_card hi
      rw [hh, finrank_top, Fintype.card_fin] at he
      omega
    obtain ⟨x, hx, hxU, hmin'⟩ := ZLattice.exists_shortest_vector_notMem L _ hs
    refine ⟨Fin.snoc b x, hi.finSnoc hxU, ?_, ?_⟩
    · exact Fin.lastCases (by simpa using hx) (fun i => by simpa using hb i)
    · exact Fin.lastCases (by simpa [Fin.snoc_image_Iio_last] using hmin')
        (fun i => by simpa [Fin.snoc_image_Iio_castSucc] using hmin i)

/-- A real basis from the successive minima of a full lattice. -/
theorem exists_greedy_lattice_basis {n : ℕ} (hn : finrank ℝ E = n) :
    ∃ b : Basis (Fin n) ℝ E, (∀ i, b i ∈ L) ∧
      ∀ i x, x ∈ L → x ∉ span ℝ (b '' Set.Iio i) → ‖b i‖ ≤ ‖x‖ := by
  obtain ⟨v, hv, hmem, hmin⟩ := exists_greedy_lattice_family L n hn.ge
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv (by simpa using hn.symm)
  refine ⟨b, ?_⟩
  simpa [b] using And.intro hmem hmin

end
end CCDN
