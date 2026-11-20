/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Filtered module generation for linear projections. A monic elimination bounds
coefficient degrees; iterating it preserves that bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The filtered piece of degree `m` is spanned by products of a fixed finite set of generators
with images of polynomials of degree at most `m`. -/
def HasFilteredGenerators {K σ τ : Type*} [Field K] (I : Ideal (MvPolynomial τ K))
    (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K ⧸ I) : Prop :=
  ∃ s : Finset (MvPolynomial τ K ⧸ I), ∀ (m : ℕ) (W : Submodule K (MvPolynomial τ K ⧸ I)),
    (∀ p, p.totalDegree ≤ m → ∀ t ∈ s, ψ p * t ∈ W) → filteredCoordinateSpace I m ≤ W

namespace HasFilteredGenerators

protected theorem quotient {K τ : Type*} [Field K] (I : Ideal (MvPolynomial τ K)) :
    HasFilteredGenerators I (Ideal.Quotient.mkₐ K I) := by
  classical
  refine ⟨{1}, ?_⟩
  intro m W h x hx
  obtain ⟨p, hp, rfl⟩ := mem_filteredCoordinateSpace.mp hx
  simpa using h p hp 1 (Finset.mem_singleton_self 1)

/-- Forgetting the degree bounds gives a finite, hence integral, projection. -/
protected theorem isIntegral {K σ τ : Type*} [Field K] {I : Ideal (MvPolynomial τ K)}
    {ψ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K ⧸ I}
    (h : HasFilteredGenerators I ψ) : ψ.IsIntegral := by
  let A := MvPolynomial τ K ⧸ I
  let R := MvPolynomial σ K
  let : Algebra R A := ψ.toRingHom.toAlgebra
  let : IsScalarTower K R A := IsScalarTower.of_algHom ψ
  obtain ⟨s, hs⟩ := h
  apply RingHom.Finite.to_isIntegral
  refine ⟨⟨s, le_antisymm le_top ?_⟩⟩
  intro x _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hs p.totalDegree ((Submodule.span R (↑s : Set A)).restrictScalars K)
    (fun q _ t ht => Submodule.smul_mem _ q (Submodule.subset_span ht))
    (mem_filteredCoordinateSpace.mpr ⟨p, le_rfl, rfl⟩)

/-- Filtered generation is transitive through the coordinate ring of the image. -/
protected theorem comp {K σ τ υ : Type*} [Field K] {I : Ideal (MvPolynomial τ K)}
    {ψ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K ⧸ I}
    {χ : MvPolynomial υ K →ₐ[K] MvPolynomial σ K ⧸ RingHom.ker ψ}
    (hψ : HasFilteredGenerators I ψ) (hχ : HasFilteredGenerators (RingHom.ker ψ) χ) :
    HasFilteredGenerators I ((Ideal.kerLiftAlg ψ).comp χ) := by
  classical
  obtain ⟨s, hs⟩ := hψ
  obtain ⟨t, ht⟩ := hχ
  let η := Ideal.kerLiftAlg ψ
  let P := (s ×ˢ t).image (fun x => η x.2 * x.1)
  refine ⟨P, fun m W hW => hs m W (fun p hp z hz => ?_)⟩
  let L := (LinearMap.mulRight K z).comp η.toLinearMap
  have hmem : Ideal.Quotient.mk (RingHom.ker ψ) p ∈ filteredCoordinateSpace (RingHom.ker ψ) m :=
    mem_filteredCoordinateSpace.mpr ⟨p, hp, rfl⟩
  have hle : filteredCoordinateSpace (RingHom.ker ψ) m ≤ W.comap L := by
    refine ht m _ (fun q hq y hy => ?_)
    change η (χ q * y) * z ∈ W
    rw [map_mul, mul_assoc]
    exact hW q hq _ (Finset.mem_image.mpr ⟨(z, y), Finset.mem_product.mpr ⟨hz, hy⟩, rfl⟩)
  exact hle hmem

/-- Including additional projection coordinates preserves filtered generation. -/
protected theorem of_comp_rename {K σ τ υ : Type*} [Field K] {I : Ideal (MvPolynomial τ K)}
    {ψ : MvPolynomial υ K →ₐ[K] MvPolynomial τ K ⧸ I} (j : σ → υ)
    (h : HasFilteredGenerators I (ψ.comp (rename j))) : HasFilteredGenerators I ψ := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun m W hW => hs m W fun p hp =>
    hW (rename j p) ((totalDegree_rename_le j p).trans hp)⟩

/-- A monic relation with the usual weighted degree bound eliminates high powers of the outer
variable without increasing the degree of the coefficients needed over the projected ring. -/
theorem of_monic_elimination {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K))
    (e : MvPolynomial τ K ≃ₐ[K] Polynomial (MvPolynomial σ K))
    (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K ⧸ I)
    (he : ∀ p, Ideal.Quotient.mk I (e.symm (Polynomial.C p)) = ψ p)
    (hcoef : ∀ f i, i ≤ (e f).natDegree → ((e f).coeff i).totalDegree + i ≤ f.totalDegree)
    (f₀ : MvPolynomial τ K) (hq : (e f₀).Monic)
    (hqdeg : f₀.totalDegree ≤ (e f₀).natDegree)
    (hqzero : f₀ ∈ I) : HasFilteredGenerators I ψ := by
  classical
  let T := (Ideal.Quotient.mkₐ K I).comp e.symm.toAlgHom
  let t := T Polynomial.X
  have hT (i : ℕ) (p : MvPolynomial σ K) : T (Polynomial.monomial i p) = ψ p * t ^ i := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact congrArg (· * t ^ i) (he p)
  let q := e f₀
  have hzero : T q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [q] using hqzero)
  let r := q.natDegree
  have hqsum : q = (∑ j ∈ Finset.range r, Polynomial.monomial j (q.coeff j)) +
      Polynomial.monomial r 1 := by
    conv_lhs => rw [q.as_sum_range]
    rw [Finset.sum_range_succ, hq.coeff_natDegree]
  refine ⟨(Finset.range r).image (fun i => t ^ i), fun m W hW => ?_⟩
  have hterm (i : ℕ) (p : MvPolynomial σ K) (hp : p.totalDegree + i ≤ m) :
      T (Polynomial.monomial i p) ∈ W := by
    induction i using Nat.strong_induction_on generalizing p with
    | h i ih =>
      by_cases hi : i < r
      · rw [hT]
        exact hW p (by omega) _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))
      · have h := congrArg (fun v => T (Polynomial.monomial (i - r) p * v)) hqsum
        change T (Polynomial.monomial (i - r) p * q) = _ at h
        have hi' : i - r + r = i := by omega
        simp only [map_mul T (Polynomial.monomial (i - r) p) q, hzero, mul_zero] at h
        rw [mul_add, Finset.mul_sum] at h
        simp only [Polynomial.monomial_mul_monomial, map_add, map_sum, mul_one, hi'] at h
        rw [eq_neg_of_add_eq_zero_right h.symm]
        refine W.neg_mem (W.sum_mem (fun j hj => ih (i - r + j) ?_ (p * q.coeff j) ?_))
        · have := Finset.mem_range.mp hj
          omega
        · have hjd := (hcoef f₀ j (Finset.mem_range.mp hj).le).trans hqdeg
          change (q.coeff j).totalDegree + j ≤ r at hjd
          have hm := totalDegree_mul p (q.coeff j)
          omega
  intro x hx
  obtain ⟨f, hf, rfl⟩ := mem_filteredCoordinateSpace.mp hx
  rw [show Ideal.Quotient.mk I f = T (e f) by simp [T], (e f).as_sum_support, map_sum]
  exact W.sum_mem (fun i hi => hterm i _ ((hcoef f i (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi))).trans hf))

end HasFilteredGenerators
end
end CCDN
