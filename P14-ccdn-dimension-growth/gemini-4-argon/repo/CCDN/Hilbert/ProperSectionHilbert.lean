/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.ForMathlib.Polynomial
import CCDN.Hilbert.PolynomialComparison

/-! Hilbert inequalities for a proper polynomial section of a prime
affine variety. Multiplication by the section is injective in the original
coordinate domain and is killed in the section quotient. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every proper polynomial section lowers the affine Hilbert
dimension by at least one. In the maximal remaining dimension its leading
coefficient is at most the expected intersection degree. -/
theorem proper_section_hilbert_dimension_leadingCoeff
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (m : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (f : MvPolynomial σ K) (hf : f ∉ I) (hfdeg : 0 < f.totalDegree)
    (hsection : I ⊔ Ideal.span {f} ≠ ⊤) :
    (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤ m ∧
      ((filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree = m →
        (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).leadingCoeff ≤
          (filteredHilbertPolynomial I).leadingCoeff * (m + 1) * f.totalDegree) := by
  /- The Hilbert polynomial of the section is bounded by the finite
  difference of the original Hilbert polynomial, with the necessary shift. -/
  classical
  let P := (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).comp
    (Polynomial.X + Polynomial.C (f.totalDegree : ℚ))
  let Q := (filteredHilbertPolynomial I).comp
    (Polynomial.X + Polynomial.C (f.totalDegree : ℚ)) - filteredHilbertPolynomial I
  have hPdeg : P.natDegree = (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree :=
    Polynomial.natDegree_taylor _ _
  have hPlc : P.leadingCoeff = (filteredHilbertPolynomial (I ⊔ Ideal.span {f})).leadingCoeff :=
    Polynomial.leadingCoeff_taylor _ _
  have hPpos : 0 < P.leadingCoeff :=
    hPlc ▸ filteredHilbertPolynomial_leadingCoeff_pos _ hsection
  have hs : (f.totalDegree : ℚ) ≠ 0 := mod_cast hfdeg.ne'
  have hQdeg := Polynomial.natDegree_comp_X_add_C_sub_self (filteredHilbertPolynomial I) hdim _ hs
  have hQlc := Polynomial.leadingCoeff_comp_X_add_C_sub_self (filteredHilbertPolynomial I) hdim _ hs
  have hQpos : 0 < Q.leadingCoeff := by
    rw [show Q.leadingCoeff = _ from hQlc]
    exact mul_pos (mul_pos
      (filteredHilbertPolynomial_leadingCoeff_pos I (Ideal.IsPrime.ne_top ‹I.IsPrime›))
      (by positivity)) (mod_cast hfdeg)
  have hle : ∃ M : ℕ, ∀ N ≥ M, P.eval (N : ℚ) ≤ Q.eval (N : ℚ) := by
    obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec I
    obtain ⟨L, hL⟩ := filteredHilbertPolynomial_spec (I ⊔ Ideal.span {f})
    refine ⟨max M L, fun N hN => ?_⟩
    have hMN : M ≤ N := (le_max_left _ _).trans hN
    have hLN : L ≤ f.totalDegree + N := by have := (le_max_right M L).trans hN; omega
    dsimp only [P, Q]
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_sub]
    rw [show (N : ℚ) + f.totalDegree = ((f.totalDegree + N : ℕ) : ℚ) by push_cast; ring,
      hM _ (by omega), hM _ hMN, hL _ hLN]
    let J := I ⊔ Ideal.span {f}
    let q := Ideal.Quotient.mkₐ K I
    let ψ : (MvPolynomial σ K ⧸ I) →ₐ[K] MvPolynomial σ K ⧸ J :=
      Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J) fun g hg =>
        Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J from le_sup_left) hg)
    let V := filteredCoordinateSpace I (f.totalDegree + N)
    let W := filteredCoordinateSpace I N
    let U := W.map (LinearMap.mulLeft K (q f))
    have hUV : U ≤ V := by
      rintro x hx
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hb
      refine Submodule.mem_map.mpr ⟨f * g, ?_, by simp [q]⟩
      rw [mem_restrictTotalDegree] at hg ⊢
      exact (totalDegree_mul _ _).trans (Nat.add_le_add_left hg _)
    have hUker : U ≤ ψ.toLinearMap.ker := by
      rintro x hx
      obtain ⟨b, _, rfl⟩ := Submodule.mem_map.mp hx
      apply LinearMap.mem_ker.mpr
      change ψ (q f * b) = 0
      rw [map_mul, show ψ (q f) = Ideal.Quotient.mk J f from rfl,
        Ideal.Quotient.eq_zero_iff_mem.mpr
          ((show Ideal.span {f} ≤ J from le_sup_right) (Ideal.subset_span (by simp))), zero_mul]
    have hf0 : q f ≠ 0 := fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hUdim : Module.finrank K U = Module.finrank K W :=
      (Submodule.equivMapOfInjective (LinearMap.mulLeft K (q f))
        (fun a b h => mul_left_cancel₀ hf0 h) W).finrank_eq.symm
    have hmap : V.map ψ.toLinearMap = filteredCoordinateSpace J (f.totalDegree + N) := by
      ext x; constructor
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩; exact Submodule.mem_map.mpr ⟨g, hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact Submodule.mem_map.mpr ⟨q g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
    have h := finrank_map_add_kernel_subspace_le ψ.toLinearMap V U hUV hUker
    rw [hmap, hUdim] at h
    have hQ : (Module.finrank K (filteredCoordinateSpace J (f.totalDegree + N)) : ℚ) +
        Module.finrank K W ≤ Module.finrank K V := mod_cast h
    linarith
  exact ⟨by simpa only [hPdeg, show Q.natDegree = m from hQdeg] using
      polynomial_natDegree_le_of_eventual_nat_eval_le P Q hPpos hle,
    fun hdimsection => by
      simpa only [hPlc, show Q.leadingCoeff = _ from hQlc] using
        polynomial_leadingCoeff_le_of_eventual_nat_eval_le P Q hPpos hQpos
          (by rw [hPdeg, hdimsection]; exact hQdeg.symm) hle⟩

end
end CCDN
