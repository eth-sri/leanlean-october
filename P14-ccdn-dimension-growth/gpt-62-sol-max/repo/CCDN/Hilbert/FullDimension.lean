/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.CoordinateIndependence

/-! Full ambient Hilbert dimension forces the ideal to be zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A proper ideal whose filtered Hilbert polynomial has degree equal to the number of variables is
the zero ideal. -/
theorem ideal_eq_bot_of_full_hilbert_dimension
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤)
    (hdim : (filteredHilbertPolynomial I).natDegree = Fintype.card σ) : I = ⊥ := by
  classical
  obtain ⟨U, hU, hAI⟩ := exists_hilbert_dimension_independent_coordinates I hI
  have hcard : Fintype.card U = Fintype.card σ := by
    simp_all
  have hmem : ∀ i : σ, i ∈ U := by
    intro i
    by_contra hn
    have hh := Fintype.card_subtype_lt hn
    linarith
  let j : σ → U := fun i => ⟨i, hmem i⟩
  have hj : Function.Injective j := fun _ _ h => congrArg Subtype.val h
  have hi : AlgebraicIndependent K (fun i : σ => (Ideal.Quotient.mk I) (X i)) := by
    exact hAI.comp j hj
  have he : aeval (fun i : σ => (Ideal.Quotient.mk I) (X i)) = Ideal.Quotient.mkₐ K I := by
    ext i
    simp
  have hinj : Function.Injective (Ideal.Quotient.mkₐ K I) := by
    rw [← he]
    exact hi
  have hk := (RingHom.injective_iff_ker_eq_bot
    (Ideal.Quotient.mkₐ K I).toRingHom).mp hinj
  simp_all

end
end CCDN
