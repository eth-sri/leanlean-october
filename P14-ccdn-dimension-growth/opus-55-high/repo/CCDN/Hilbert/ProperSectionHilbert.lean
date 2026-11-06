/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.ForMathlib.Polynomial
import CCDN.Hilbert.PolynomialComparison

/-! Hilbert inequalities for a proper polynomial section of a prime
affine variety. Multiplication by the section is injective in the original
coordinate domain and is killed in the section quotient. -/

namespace CCDN
section
open MvPolynomial

variable {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) [I.IsPrime]

/-- The Hilbert polynomial of the section is bounded by the finite
difference of the original Hilbert polynomial, with the necessary shift. -/
theorem proper_section_hilbert_polynomial_difference
    (f : MvPolynomial σ K) (hf : f ∉ I) :
    ∃ M : ℕ, ∀ N ≥ M,
      ((filteredHilbertPolynomial (I ⊔ Ideal.span {f})).comp
        (Polynomial.X + Polynomial.C (f.totalDegree : ℚ))).eval (N : ℚ) ≤
      ((filteredHilbertPolynomial I).comp
        (Polynomial.X + Polynomial.C (f.totalDegree : ℚ)) -
          filteredHilbertPolynomial I).eval (N : ℚ) := by
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
  obtain ⟨L, hL⟩ := filteredHilbertPolynomial_spec (I ⊔ Ideal.span {f})
  refine ⟨max M L, fun N hN => ?_⟩
  have hMN := (le_max_left _ _).trans hN
  have hLN : L ≤ f.totalDegree + N := by grind
  simp
  rw [show (N : ℚ) + f.totalDegree = ((f.totalDegree + N : ℕ) : ℚ) by push_cast; ring,
    hM _ (by omega), hM _ hMN, hL _ hLN]
  have h : Module.finrank K (filteredCoordinateSpace (I ⊔ Ideal.span {f}) (f.totalDegree + N)) +
      Module.finrank K (filteredCoordinateSpace I N) ≤
        Module.finrank K (filteredCoordinateSpace I (f.totalDegree + N)) := by
    let J := I ⊔ Ideal.span {f}
    let A := MvPolynomial σ K ⧸ I
    let q := Ideal.Quotient.mkₐ K I
    let ψ : A →ₐ[K] MvPolynomial σ K ⧸ J :=
      Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J) (by
        intro g hg
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J from le_sup_left) hg))
    have hψ (g : MvPolynomial σ K) :
        ψ (q g) = Ideal.Quotient.mk J g := rfl
    let V := filteredCoordinateSpace I (f.totalDegree + N)
    let W := filteredCoordinateSpace I N
    let U := W.map (LinearMap.mulLeft K (q f))
    have hf0 :=
      fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hUdim :=
      (Submodule.equivMapOfInjective (LinearMap.mulLeft K (q f))
        (fun a b h => mul_left_cancel₀ hf0 h) W).finrank_eq.symm
    have hmap : V.map ψ.toLinearMap =
        filteredCoordinateSpace J (f.totalDegree + N) := by
      ext x
      constructor
      · rintro ⟨a, ⟨g, hg, rfl⟩, rfl⟩
        exact Submodule.mem_map.mpr ⟨g, hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact Submodule.mem_map.mpr ⟨q g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
    have h := finrank_map_add_kernel_subspace_le ψ.toLinearMap V U (by
      rintro x hx
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hb
      refine Submodule.mem_map.mpr ⟨f * g, ?_, by aesop⟩
      rw [mem_restrictTotalDegree] at hg ⊢
      exact (totalDegree_mul _ _).trans (Nat.add_le_add_left hg _)) (by
        rintro x hx
        obtain ⟨b, _, rfl⟩ := Submodule.mem_map.mp hx
        change ψ (q f * b) = 0
        rw [map_mul, hψ, Ideal.Quotient.eq_zero_iff_mem.mpr
          ((show Ideal.span {f} ≤ J from le_sup_right) (Ideal.subset_span (by simp))), zero_mul])
    rwa [hmap, hUdim] at h
  have hQ : (Module.finrank K
      (filteredCoordinateSpace (I ⊔ Ideal.span {f}) (f.totalDegree + N)) : ℚ) +
      Module.finrank K (filteredCoordinateSpace I N) ≤
        Module.finrank K (filteredCoordinateSpace I (f.totalDegree + N)) := by
    exact_mod_cast h
  linarith

