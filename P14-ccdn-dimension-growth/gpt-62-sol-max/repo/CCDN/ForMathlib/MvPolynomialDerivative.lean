/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Partial derivatives: the chain rule and vanishing derivatives

Partial derivatives commute with homomorphisms of polynomial algebras by the chain rule.
If `∂f/∂xᵢ = 0`, then each exponent of `xᵢ` occurring in `f` is zero in the coefficient ring.
Below the characteristic this means that `xᵢ` does not occur in `f`.

## Main results

* `MvPolynomial.pderiv_algHom`: the chain rule for a homomorphism of polynomial algebras.
* `CharP.natCast_ne_zero_of_lt`: a positive natural number below the characteristic is nonzero.
* `MvPolynomial.coeff_mul_natCast_eq_zero_of_pderiv_eq_zero`: the coefficient of `m` is
  annihilated by the exponent `m i`.
* `MvPolynomial.notMem_vars_of_pderiv_eq_zero`: a variable with vanishing partial derivative does
  not occur, when its exponents are nonzero in the coefficient ring.
* `MvPolynomial.exists_pderiv_ne_zero`: a nonconstant polynomial of total degree below the
  characteristic has a nonzero partial derivative.
-/

@[expose] public section

namespace CharP

/-- A positive natural number below the characteristic is nonzero. -/
theorem natCast_ne_zero_of_lt (R : Type*) [AddMonoidWithOne R] {p : ℕ} [CharP R p] {n : ℕ}
    (hn : n ≠ 0) (hnp : n < p) : (n : R) ≠ 0 := fun h =>
  Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) hnp ((cast_eq_zero_iff R p n).mp h)

end CharP

namespace MvPolynomial

/-- The multivariate chain rule for a derivation on any target algebra. -/
theorem derivation_algHom {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A] [Fintype σ]
    (D : Derivation K A A) (φ : MvPolynomial σ K →ₐ[K] A) (f : MvPolynomial σ K) :
    D (φ f) = ∑ i, φ (pderiv i f) * D (φ (X i)) := by
  classical
  let : Algebra (MvPolynomial σ K) A := φ.toRingHom.toAlgebra
  
  have hφ : algebraMap (MvPolynomial σ K) A = φ.toRingHom := rfl
  let L := Algebra.linearMap (MvPolynomial σ K) A
  have he : D.compAlgebraMap (MvPolynomial σ K) =
      ∑ i, D (φ (X i)) • L.compDer (pderiv i) := by
    apply derivation_ext
    intro j
    simp [Derivation.compAlgebraMap_apply, hφ, Derivation.coe_comp, L,
      Algebra.linearMap_apply, pderiv_X, Pi.single_apply]
  simpa [Derivation.compAlgebraMap_apply, hφ, Derivation.coe_comp, L,
    Algebra.linearMap_apply, mul_comm] using DFunLike.congr_fun he f

/-- The polynomial chain rule for a homomorphism of polynomial algebras. -/
theorem pderiv_algHom {K σ τ : Type*} [CommRing K] [Fintype σ]
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (f : MvPolynomial σ K) (k : τ) :
    pderiv k (φ f) = ∑ i, φ (pderiv i f) * pderiv k (φ (X i)) :=
  derivation_algHom (pderiv k) φ f

variable {R σ : Type*}

/-- If `∂f/∂xᵢ = 0`, then the coefficient of `f` at `m` is annihilated by the exponent `m i`. -/
theorem coeff_mul_natCast_eq_zero_of_pderiv_eq_zero [CommSemiring R] {f : MvPolynomial σ R}
    {i : σ} (h : pderiv i f = 0) (m : σ →₀ ℕ) : f.coeff m * (m i : R) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (m i) with hmi | hmi
  simp_all
  have hu : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    refine tsub_add_cancel_of_le fun j ↦ ?_
    grind
  have hc : (pderiv i f).coeff (m - Finsupp.single i 1) = 0 := by simp_all
  rw [coeff_pderiv, hu, Finsupp.tsub_apply, Finsupp.single_eq_same,
    ← Nat.cast_add_one, Nat.sub_add_cancel hmi] at hc
  exact hc

/-- A variable with vanishing partial derivative does not occur in `f`, provided the positive
natural numbers up to its degree are nonzero in `R`. -/
theorem notMem_vars_of_pderiv_eq_zero [CommSemiring R] [NoZeroDivisors R]
    {f : MvPolynomial σ R} {i : σ} (h : pderiv i f = 0)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ f.degreeOf i → (n : R) ≠ 0) : i ∉ f.vars := by
  classical
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  exact mul_ne_zero (mem_support_iff.mp hm)
    (hchar _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmi)) (monomial_le_degreeOf i hm))
    (coeff_mul_natCast_eq_zero_of_pderiv_eq_zero h m)

/-- A polynomial of positive total degree has a nonzero partial derivative, provided the
positive natural numbers up to its total degree are nonzero in `R`. -/
theorem exists_pderiv_ne_zero [CommSemiring R] [NoZeroDivisors R] {f : MvPolynomial σ R}
    (hpos : 0 < f.totalDegree)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ f.totalDegree → (n : R) ≠ 0) :
    ∃ i, pderiv i f ≠ 0 := by
  classical
  obtain ⟨m, hm, i, hi⟩ : ∃ m ∈ f.support, ∃ i, m i ≠ 0 := by
    by_contra! h
    exact LT.lt.ne' hpos ((totalDegree_eq_zero_iff σ f).mpr h)
  refine ⟨i, fun hz ↦ notMem_vars_of_pderiv_eq_zero hz
    (fun n hn hle ↦ hchar n hn (hle.trans (degreeOf_le_totalDegree f i))) ?_⟩
  exact (mem_vars_iff_mem_support i).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hi⟩

/-- A partial derivative lowers the total degree by at least one. -/
theorem pderiv_totalDegree_le {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (i : σ) : (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hd := le_totalDegree (mem_support_iff.mpr (left_ne_zero_of_mul hc))
  change (m + Finsupp.single i 1).degree ≤ _ at hd
  rw [map_add, Finsupp.degree_single] at hd
  change m.degree ≤ _
  omega

lemma pderiv_totalDegree_lt {R σ : Type*} [CommSemiring R] {f : MvPolynomial σ R}
    {i : σ} (hi : pderiv i f ≠ 0) : (pderiv i f).totalDegree < f.totalDegree := by
  have hp : f.totalDegree ≠ 0 := fun h => hi (by rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C])
  have := pderiv_totalDegree_le f i
  omega

/-- A nonzero partial derivative is not divisible by the original polynomial. -/
theorem not_dvd_pderiv_of_pderiv_ne_zero {R σ : Type*} [CommRing R] [IsDomain R]
    {f : MvPolynomial σ R} {i : σ} (hi : pderiv i f ≠ 0) : ¬f ∣ pderiv i f :=
  fun h => (pderiv_totalDegree_lt hi).not_ge (totalDegree_le_of_dvd_of_isDomain h hi)

end MvPolynomial
