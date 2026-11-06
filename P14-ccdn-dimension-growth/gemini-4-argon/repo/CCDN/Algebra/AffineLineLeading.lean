/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The coefficient of highest possible degree on an affine line depends only
on the top homogeneous component and the direction, not the base point. -/

@[expose] public section
namespace CCDN
noncomputable section

/- The affine polynomial `C a + C b * X` has degree at most `1`. -/

/-- Restriction to the affine line a+t*b. -/
def affineLinePolynomial {R σ : Type*} [CommRing R] (a b : σ → R) :
    MvPolynomial σ R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X)

/-- At any degree at least the total degree, the affine-line coefficient equals
the corresponding homogeneous component evaluated on its direction. -/
theorem affineLinePolynomial_top_coefficient {R σ : Type*} [CommRing R]
    (a b : σ → R) (f : MvPolynomial σ R) (d : ℕ) (hd : f.totalDegree ≤ d) :
    (affineLinePolynomial a b f).coeff d =
      MvPolynomial.eval b (MvPolynomial.homogeneousComponent d f) := by
  classical
  have hprod_coeff (s : Finset σ) (q : σ → Polynomial R) (e : σ → ℕ)
      (hq : ∀ i ∈ s, (q i).natDegree ≤ e i) :
      (∏ i ∈ s, q i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (q i).coeff (e i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
      have ht : (∏ j ∈ s, q j).natDegree ≤ ∑ j ∈ s, e j :=
        (Polynomial.natDegree_prod_le _ _).trans
          (Finset.sum_le_sum fun j hj => hq j (Finset.mem_insert_of_mem hj))
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
        (hq i (Finset.mem_insert_self _ _)) ht,
        ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  have hmd : m.degree ≤ d := (MvPolynomial.le_totalDegree hm).trans hd
  let q : σ → Polynomial R := fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X
  have hq (i : σ) : (q i).natDegree ≤ 1 :=
    Polynomial.natDegree_add_le_of_degree_le (by simp)
      (Polynomial.natDegree_mul_le.trans (by simpa using (Polynomial.natDegree_X_le (R := R))))
  have hp (i : σ) : ((q i) ^ m i).natDegree ≤ m i :=
    Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (m i) (hq i))
  have hprod : (m.prod (fun i e => (q i) ^ e)).natDegree ≤ m.degree :=
    (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => hp i)
  have htop : (affineLinePolynomial a b (MvPolynomial.monomial m (f.coeff m))).coeff d =
      if d = m.degree then f.coeff m * m.prod (fun i e => b i ^ e) else 0 := by
    rw [affineLinePolynomial, MvPolynomial.eval₂Hom_monomial]
    change (Polynomial.C (f.coeff m) * m.prod (fun i e => (q i) ^ e)).coeff d = _
    rw [Polynomial.coeff_C_mul]
    by_cases he : d = m.degree
    · rw [ite_eq_left he, he]
      congr 1; simp only [Finsupp.prod]
      rw [show m.degree = ∑ i ∈ m.support, m i from rfl,
        hprod_coeff m.support (fun i => q i ^ m i) m (fun i _ => hp i)]
      exact Finset.prod_congr rfl fun i _ => by
        simpa only [mul_one, q, Polynomial.coeff_add, Polynomial.coeff_C_succ,
          Polynomial.coeff_C_mul_X, zero_add, ite_true] using
          Polynomial.coeff_pow_of_natDegree_le (m := m i) (hq i)
    · rw [ite_eq_right he,
        Polynomial.coeff_eq_zero_of_natDegree_lt (hprod.trans_lt (by omega)), mul_zero]
  rw [htop, MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial _ rfl)]
  split_ifs <;> simp [MvPolynomial.eval_monomial]

end
end CCDN
