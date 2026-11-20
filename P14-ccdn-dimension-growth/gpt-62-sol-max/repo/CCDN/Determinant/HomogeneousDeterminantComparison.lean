/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
public import CCDN.Determinant.IntegerMinors
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.ForMathlib.Matrix
import CCDN.AuxiliaryPolynomial.WeightedMonomialDeterminant
import CCDN.Hilbert.HomogeneousHilbert
import CCDN.ForMathlib.Log
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! The coefficient obstruction in the determinant method, using the complementary minor of
 the evaluation matrix to a triangular minor of the polynomial multiplication map. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- Columns of the multiplication-by-`f` map on homogeneous coefficient vectors. -/
private def homogeneousMultiplication {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) (M k : ℕ) :
    Matrix (Fin ((n + M).choose M)) (Fin ((n + k).choose k)) ℤ :=
  fun i j => (f * monomial (homogeneousMonomials n k j) 1).coeff (homogeneousMonomials n M i)

private lemma homogeneousMultiplication_mulVec {n M k : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (v : Fin ((n + k).choose k) → ℤ) (i : Fin ((n + M).choose M)) :
    (homogeneousMultiplication f M k *ᵥ v) i =
      (f * polynomialOfCoefficients (homogeneousMonomials n k) v).coeff (homogeneousMonomials n M i) := by
  classical
  simp only [homogeneousMultiplication, mulVec, dotProduct, polynomialOfCoefficients, Finset.mul_sum,
    coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show monomial (homogeneousMonomials n k j) (v j) =
      v j • monomial (homogeneousMonomials n k j) (1 : ℤ) by simp [smul_monomial],
    mul_smul_comm, coeff_smul, smul_eq_mul, mul_comm]

private lemma homogeneousMultiplication_decode {n d M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : d ≤ M)
    (u : Fin ((n + (M - d)).choose (M - d)) → ℤ) :
    polynomialOfCoefficients (homogeneousMonomials n M) (homogeneousMultiplication f M (M - d) *ᵥ u) =
      f * polynomialOfCoefficients (homogeneousMonomials n (M - d)) u := by
  let q := polynomialOfCoefficients (homogeneousMonomials n (M - d)) u
  have hg : (f * q).IsHomogeneous M := by
    simpa [Nat.add_sub_of_le hd] using hf.mul (polynomialOfCoefficients_homogeneous _ _ u)
  rw [funext (homogeneousMultiplication_mulVec f u)]
  exact (homogeneous_eq_sum_coeff _ hg).symm

private lemma homogeneous_evaluation_kernel_matrix {n d M s : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : d ≤ M)
    (x : Fin s → Fin (n + 1) → ℤ) (hx : ∀ i, eval (x i) f = 0)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (x i) g = 0) → f ∣ g) (v : Fin ((n + M).choose M) → ℤ) :
    evaluationMatrix (homogeneousMonomials n M) x *ᵥ v = 0 ↔
      ∃ u, homogeneousMultiplication f M (M - d) *ᵥ u = v := by
  let g := polynomialOfCoefficients (homogeneousMonomials n M) v
  have hg : g.IsHomogeneous M := polynomialOfCoefficients_homogeneous n M v
  constructor
  · intro hv
    obtain ⟨q, he⟩ := hrel g hg (fun i => (eval_polynomialOfCoefficients _ _ _ _).trans (congrFun hv i))
    have hq := homogeneous_multiplier hf hf0 (he ▸ hg) hd
    refine ⟨fun j => q.coeff (homogeneousMonomials n (M - d) j), ?_⟩
    funext i
    rw [homogeneousMultiplication_mulVec, show polynomialOfCoefficients _ _ = q from
      (homogeneous_eq_sum_coeff q hq).symm, ← he,
      coefficient_polynomialOfCoefficients _ (homogeneousMonomials_injective _ _)]
  · rintro ⟨u, rfl⟩
    funext i
    rw [← eval_polynomialOfCoefficients, homogeneousMultiplication_decode f hf hd]
    simp [hx]

/-- The leading monomials of the multiples give a triangular minor of the multiplication map. -/
private lemma homogeneousMultiplication_leading_minor {n d M : ℕ}
    (order : MonomialOrder (Fin (n + 1))) (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : d ≤ M) :
    ∃ c : Fin ((n + (M - d)).choose (M - d)) → Fin ((n + M).choose M), Function.Injective c ∧
      ((homogeneousMultiplication f M (M - d)).submatrix c id).det =
        order.leadingCoeff f ^ ((n + (M - d)).choose (M - d)) := by
  classical
  let k := (n + (M - d)).choose (M - d)
  let m := homogeneousMonomials n (M - d)
  have hdeg (i : Fin k) : (order.degree f + m i).degree = M := by
    have h : (order.degree f).degree = d := by
      exact (hf.degree_eq_sum_deg_support ((order.degree_mem_support_iff f).mpr hf0)).symm
    simp [map_add, h, m, homogeneousMonomials_degree, Nat.add_sub_of_le hd]
  choose c hc using fun i => homogeneousMonomials_surjective n M _ (hdeg i)
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    apply homogeneousMonomials_injective n (M - d)
    exact add_left_cancel ((hc i).symm.trans ((congrArg (homogeneousMonomials n M) hij).trans (hc j)))
  let lo := LinearOrder.lift' (order.toSyn ∘ m)
    (order.toSyn.injective.comp (homogeneousMonomials_injective _ _))
  let K := (homogeneousMultiplication f M (M - d)).submatrix c id
  
  have ht : @IsUpperTriangular (Fin k) ℤ _ lo.toLT K := by
    intro i j hj
    change order.toSyn (m j) < order.toSyn (m i) at hj
    change (f * monomial (m j) 1).coeff (homogeneousMonomials n M (c i)) = 0
    rw [hc i]
    apply order.coeff_eq_zero_of_lt
    rw [order.degree_mul hf0 (by simp), order.degree_monomial, ite_eq_right one_ne_zero,
      map_add, map_add]
    exact add_lt_add_right hj _
  change K.det = _
  rw [det_of_isUpperTriangular ht]
  have hdiag (i : Fin k) : K i i = order.leadingCoeff f := by
    change (f * monomial (m i) 1).coeff (homogeneousMonomials n M (c i)) = _
    rw [hc i, coeff_mul_monomial, mul_one, MonomialOrder.leadingCoeff]
  simp [hdiag, k]

private lemma int_mulVec_eq_zero_iff {ι ν : Type*} [Fintype ν] (A : Matrix ι ν ℤ) (v : ν → ℤ) :
    A.map (Int.castRingHom ℚ) *ᵥ (Int.castRingHom ℚ ∘ v) = 0 ↔ A *ᵥ v = 0 := by
  simp_rw [funext_iff, ← RingHom.map_mulVec]
  simp

/-- A nonzero minor of the homogeneous multiplication map bounds the logarithm of the gcd of
maximal evaluation minors. The determinant method only needs this coefficient obstruction. -/
private lemma homogeneous_log_minor_bound {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : d ≤ M)
    (x : Fin t → Fin (n + 1) → ℤ) (hx : ∀ i, eval (x i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (x i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (x i) g = 0) → f ∣ g)
    (c : Fin ((n + (M - d)).choose (M - d)) → Fin ((n + M).choose M))
    (hc : Function.Injective c) (hc0 : ((homogeneousMultiplication f M (M - d)).submatrix c id).det ≠ 0) :
    let s := hypersurfaceRank n d M
    ∃ a : Fin s → Fin t,
      LinearIndependent ℚ ((evaluationMatrix (homogeneousMonomials n M) (x ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Real.log (minorGcd (evaluationMatrix (homogeneousMonomials n M) (x ∘ a)) : ℝ) +
        Real.log |(((homogeneousMultiplication f M (M - d)).submatrix c id).det : ℝ)| ≤
        Real.log (s.factorial : ℝ) + s * M * Real.log B := by
  classical
  let mon := homogeneousMonomials n M
  let Z := evaluationMatrix mon x
  let φ := Int.castRingHom ℚ
  obtain ⟨s, a, hi, hspan⟩ := exists_fin_linearIndependent_row_span_eq (Z.map φ)
  let A := evaluationMatrix mon (x ∘ a)
  have hk := ker_mulVecLin_submatrix_eq_of_span_row_eq (Z.map φ) a hspan
  change (A.map φ).mulVecLin.ker = (Z.map φ).mulVecLin.ker at hk
  have hker (v) : A *ᵥ v = 0 ↔ Z *ᵥ v = 0 := by
    rw [← int_mulVec_eq_zero_iff A, ← int_mulVec_eq_zero_iff Z]
    simpa only [LinearMap.mem_ker, mulVecLin_apply] using
      (show φ ∘ v ∈ (A.map φ).mulVecLin.ker ↔ φ ∘ v ∈ (Z.map φ).mulVecLin.ker by rw [hk])
  obtain ⟨hr, b, hb⟩ := complement_minor_bound A _ hi
    (fun v => (hker v).trans (homogeneous_evaluation_kernel_matrix f hf hf0 hd x hx hrel v)) c hc hc0
  have hs : s = hypersurfaceRank n d M := by unfold hypersurfaceRank; omega
  subst s
  refine ⟨a, hi, ?_⟩
  let C := (homogeneousMultiplication f M (M - d)).submatrix c id
  have hD : (0 : ℝ) < minorGcd A := by
    exact_mod_cast (show 0 < minorGcd A from zero_lt_one.trans_le (one_le_minorGcd hi))
  have hC : (0 : ℝ) < |(C.det : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
  have hbound : (minorGcd A : ℝ) * |(C.det : ℝ)| ≤ |((A.submatrix id b).det : ℝ)| := by
    exact_mod_cast hb
  have hA : (A.submatrix id b).det ≠ 0 := by
    intro h
    simp [h] at hbound
    exact (not_le_of_gt (mul_pos hD hC)) hbound
  have hlog := Real.log_le_log (mul_pos hD hC) hbound
  rw [Real.log_mul hD.ne' hC.ne'] at hlog
  have harch := weighted_evaluation_det_log_bound (mon ∘ b) (x ∘ a) hB (fun i => hbox (a i)) hA
  simp only [mon, Function.comp_apply, homogeneousMonomials_degree, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at harch
  exact hlog.trans harch

/-- Archimedean logarithmic bound from the leading triangular minor of the homogeneous
multiplication map. -/
theorem homogeneous_no_auxiliary_box_comparison {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 1))) (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hp : ∀ i, InBox (points i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    let s := hypersurfaceRank n d M
    ∃ a : Fin s → Fin t,
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Real.log (minorGcd (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ) ≤
        Real.log (s.factorial : ℝ) + s * M * Real.log B -
          ((n + (M - d)).choose (M - d) : ℝ) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨c, hi, hc⟩ := homogeneousMultiplication_leading_minor order f hf hf0 hdM
  have hc0 := hc.trans_ne (pow_ne_zero _ (order.leadingCoeff_ne_zero_iff.mpr hf0))
  obtain ⟨a, hli, hb⟩ := homogeneous_log_minor_bound f hf hf0 hdM points hzero hB hp hrel c hi hc0
  rw [hc, Int.cast_pow, abs_pow, Real.log_pow] at hb
  exact ⟨a, hli, le_sub_iff_add_le.mpr hb⟩

/-- At the degree of the equation the multiplication map has just one column, so it gives a
bound for every coefficient in terms of the evaluation minors. -/
theorem homogeneous_no_auxiliary_coefficient_height {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (z : Fin t → IntPoint (n + 1)) (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous d →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
        ((n + d).choose d : ℝ) * d * Real.log B := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf0)
    (fun m => (f.coeff m).natAbs)
  obtain ⟨j, hj⟩ := homogeneousMonomials_surjective n d m
    (hf.degree_eq_sum_deg_support hm).symm
  have hk : (n + (d - d)).choose (d - d) = 1 := by simp
  let c : Fin ((n + (d - d)).choose (d - d)) → Fin ((n + d).choose d) := fun _ => j
  let : Unique (Fin ((n + (d - d)).choose (d - d))) := by rw [hk]; infer_instance
  have hdet : ((homogeneousMultiplication f d (d - d)).submatrix c id).det = f.coeff m := by
    rw [det_unique]
    have h0 : homogeneousMonomials n (d - d) default = 0 := by
      apply (Finsupp.degree_eq_zero_iff _).mp
      rw [homogeneousMonomials_degree, Nat.sub_self]
    change (f * monomial _ 1).coeff (homogeneousMonomials n d j) = f.coeff m
    simp [h0, hj, ← C_apply]
  have hdet0 := hdet.trans_ne (mem_support_iff.mp hm)
  obtain ⟨a, hi, hb⟩ := homogeneous_log_minor_bound f hf hf0 le_rfl z hz hB hbox hrel c
    (fun _ _ _ => Subsingleton.elim _ _) hdet0
  have hD : (1 : ℝ) ≤ minorGcd (evaluationMatrix (homogeneousMonomials n d) (z ∘ a)) := by
    exact_mod_cast one_le_minorGcd hi
  let s := hypersurfaceRank n d d
  have hs : s ≤ (n + d).choose d := Nat.sub_le ..
  have hfac := Real.log_factorial_le_mul_log hs
  have hN : (1 : ℝ) ≤ (n + d).choose d := by exact_mod_cast Nat.choose_pos (by omega : d ≤ n + d)
  simp only [integerCoefficientHeight, he, Nat.cast_natAbs, Int.cast_abs]
  rw [hdet] at hb
  calc
    _ ≤ (s : ℝ) * Real.log ((n + d).choose d) + s * d * Real.log B := by
      linarith [Real.log_nonneg hD]
    _ ≤ _ := by
      have hℓ := Real.log_nonneg hN
      have hℓB := Real.log_nonneg hB
      gcongr

end
end CCDN
