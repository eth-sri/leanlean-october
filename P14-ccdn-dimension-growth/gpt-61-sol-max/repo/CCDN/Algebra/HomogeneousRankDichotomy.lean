/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.HomogeneousRank
public import CCDN.Hilbert.HomogeneousHilbert
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.ForMathlib.MvPolynomial

/-! Exact evaluation rank when all homogeneous vanishing relations are multiples
of the defining equation, and the resulting auxiliary-polynomial dichotomy. -/

public section
namespace CCDN
open MvPolynomial Matrix

private lemma homogeneousCoefficientMap_injective {K : Type*} [Field K] (n M : ℕ) :
    Function.Injective ((homogeneousCoefficientMap K n M).domRestrict
      (homogeneousSubmodule (Fin (n + 1)) K M)) := by
  intro u v huv
  apply Subtype.ext
  have he : ∀ j, u.val.coeff (homogeneousMonomials n M j) =
      v.val.coeff (homogeneousMonomials n M j) := fun j => congrFun huv j
  rw [homogeneous_eq_sum_coeff u.val u.property, homogeneous_eq_sum_coeff v.val v.property]
  simp only [he]

private lemma homogeneousCoefficientMap_surjective {K : Type*} [Field K] (n M : ℕ) :
    Function.Surjective ((homogeneousCoefficientMap K n M).domRestrict
      (homogeneousSubmodule (Fin (n + 1)) K M)) := by
  classical
  intro v
  let f : MvPolynomial (Fin (n + 1)) K := ∑ j, monomial (homogeneousMonomials n M j) (v j)
  have hf : f.IsHomogeneous M := by
    solve_by_elim [IsHomogeneous.sum, isHomogeneous_monomial, homogeneousMonomials_degree]
  refine ⟨⟨f, hf⟩, ?_⟩
  ext j
  simp [homogeneousCoefficientMap, f, coeff_monomial,
    (homogeneousMonomials_injective n M).eq_iff]

variable {K : Type*} [Field K] {n d M t : ℕ} (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M) (points : Fin t → Fin (n + 1) → K) (hzero : ∀ i, eval (points i) f = 0) (hrel : ∀ g : MvPolynomial (Fin (n + 1)) K, g.IsHomogeneous M → (∀ i, eval (points i) g = 0) → f ∣ g)

include hf hf0 hdM hzero hrel in
/-- When all degree-M relations are multiples of f, the evaluation
kernel is exactly the image of the degree-allowed multiples. -/
private theorem homogeneous_evaluation_kernel_eq_multiples  :
    (homogeneousEvaluationMatrix K n M points).mulVecLin.ker =
      (homogeneousMultiples f d M).map (homogeneousCoefficientMap K n M) := by
  ext v
  constructor
  · intro hv
    obtain ⟨g, hg⟩ := homogeneousCoefficientMap_surjective n M v
    have hvan : ∀ i, eval (points i) g.val = 0 := by
      intro i
      rw [← homogeneous_evaluation_mulVec g.val g.property]
      have he := congrFun (LinearMap.mem_ker.mp hv) i
      simpa only [← hg, LinearMap.domRestrict_apply, Matrix.mulVecLin_apply, Pi.zero_apply] using he
    obtain ⟨u, hu⟩ := hrel g.val g.property hvan
    have hhom :=
      homogeneous_multiplier hf hf0 (hu ▸ g.property) hdM
    refine ⟨g.val, ?_, hg⟩
    exact Submodule.mem_map.mpr ⟨u, hhom, hu.symm⟩
  · intro hv
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
    have hhom := by
      simpa only [Nat.add_sub_of_le hdM] using hf.mul hu
    ext i
    rw [Matrix.mulVecLin_apply, LinearMap.mulLeft_apply, homogeneous_evaluation_mulVec _ hhom]
    simp only [eval_mul, hzero i, zero_mul, Pi.zero_apply]

include hf hf0 hdM hzero hrel in
/-- The exact Hilbert rank in the absence of an auxiliary polynomial. -/
private theorem homogeneous_evaluation_rank_eq  :
    (homogeneousEvaluationMatrix K n M points).rank +
      (n + (M - d)).choose (M - d) = (n + M).choose M := by
  let U := homogeneousMultiples f d M
  let φ := homogeneousCoefficientMap K n M
  have hhom : ∀ u ∈ U, u.IsHomogeneous M := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hu
    simpa only [Nat.add_sub_of_le hdM, LinearMap.mulLeft_apply] using hf.mul hw
  have hinj : Function.Injective (φ.domRestrict U) := by
    intro u v huv
    have h := homogeneousCoefficientMap_injective  n M
      (a₁ := ⟨u.val, hhom _ u.property⟩) (a₂ := ⟨v.val, hhom _ v.property⟩) huv
    exact Subtype.ext (Subtype.mk.inj h)
  have hdim := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_domRestrict, homogeneousMultiples_finrank f hf0,
    finrank_homogeneousSubmodule_fin] at hdim
  have h := (homogeneousEvaluationMatrix K n M points).mulVecLin.finrank_range_add_finrank_ker
  rw [homogeneous_evaluation_kernel_eq_multiples f hf hf0 hdM points hzero hrel, hdim] at h
  simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, mul_one,
    Fintype.card_fin] using h


/-- The no-auxiliary hypothesis over the integers forces the exact rational
rank of the integer evaluation matrix. -/
theorem integer_homogeneous_evaluation_rank_eq {n d M t : ℕ}
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d)
    (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → CCDN.IntPoint (n + 1)) (hzero : ∀ i, eval (points i) f = 0)
    (hrel : ∀ g : CCDN.IntegerPolynomial (n + 1), g.IsHomogeneous M →
      (∀ i, eval (points i) g = 0) → f ∣ g) :
    ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)).rank +
      (n + (M - d)).choose (M - d) = (n + M).choose M := by
  have hfQ : CCDN.rationalPolynomial f ≠ 0 := by
    intro h
    apply hf0
    exact (map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using h)
  have hzQ : ∀ i, eval (fun j => (points i j : ℚ)) (CCDN.rationalPolynomial f) = 0 := by
    intro i
    have h := congrArg (Int.castRingHom ℚ) (hzero i)
    rw [map_eval, map_zero] at h
    exact h
  have hr := homogeneous_evaluation_rank_eq (CCDN.rationalPolynomial f) (hf.map _)
    hfQ hdM (fun i j => (points i j : ℚ)) hzQ
    ((by
       intro g hg hzero
       obtain ⟨b, u, hb, hu, he⟩ := (show ∃ b u, b ≠ (0 : ℤ) ∧ IsHomogeneous u M ∧ rationalPolynomial u = C ↑b * g from (by
                                      classical
                                      obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
                                        (nonZeroDivisors ℤ) (fun j => g.coeff (homogeneousMonomials n M j))
                                      choose v hv using hb
                                      refine ⟨b.val, polynomialOfCoefficients (homogeneousMonomials n M) v,
                                        nonZeroDivisors.coe_ne_zero b, polynomialOfCoefficients_homogeneous n M v, ?_⟩
                                      rw [homogeneous_eq_sum_coeff g hg, Finset.mul_sum]
                                      simp only [polynomialOfCoefficients, map_sum, map_monomial, C_mul_monomial]
                                      congr 1
                                      funext j
                                      congr 1
                                      simpa [Algebra.smul_def] using hv j))
       have huv : ∀ i, eval (points i) u = 0 := by
         intro i
         apply Int.cast_injective (α := ℚ)
         have hh := congrArg (eval (fun j => (points i j : ℚ))) he
         rw [eval_mul, hzero i, mul_zero] at hh
         change (Int.castRingHom ℚ) (eval (points i) u) = 0
         rw [map_eval]
         exact hh
       obtain ⟨v, hv⟩ := hrel u hu huv
       have hm : C (b : ℚ) * g = CCDN.rationalPolynomial f * CCDN.rationalPolynomial v := by
         rw [← he, hv, map_mul]
       refine ⟨C ((b : ℚ)⁻¹) * CCDN.rationalPolynomial v, ?_⟩
       have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
       calc
         g = C ((b : ℚ)⁻¹) * (C ↑b * g) := by
           rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hbq, C_1, one_mul]
         _ = _ := by rw [hm]; ring))
  rw [homogeneousEvaluationMatrix_intCast] at hr
  exact hr

/-- Twice the dimension of ternary forms, without natural-number division. -/
lemma ternary_homogeneous_dimension (M : ℕ) :
    2 * (2 + M).choose M = (M + 2) * (M + 1) := by
  grind [Nat.add_one_mul_choose_eq]

variable {s d M : ℕ}

/-- Closed form of the exact rank for plane projective curves. -/
lemma plane_homogeneous_rank_identity  (hdM : d ≤ M)
    (hr : s + (2 + (M - d)).choose (M - d) = (2 + M).choose M) :
    2 * s + d ^ 2 = d * (2 * M + 3) := by
  grind [ternary_homogeneous_dimension, Nat.sub_add_cancel]

/-- Elementary rank bounds sufficient to compare the plane rank with d*M. -/
lemma plane_homogeneous_rank_bounds  (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (2 + (M - d)).choose (M - d) = (2 + M).choose M) :
    0 < s ∧ d * M ≤ 2 * s ∧ s ≤ d * (M + 1) := by
  have he := plane_homogeneous_rank_identity hdM hr
  constructor
  · nlinarith
  constructor <;> nlinarith

end CCDN
