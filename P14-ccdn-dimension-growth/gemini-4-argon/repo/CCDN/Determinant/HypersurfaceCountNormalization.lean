/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Determinant.HypersurfaceMultiplicityEstimate

/-! Numerical normalization of a finite-field hypersurface count, as in
CCDN Lemma 2.8. The input count bound is an explicit hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The global single-prime determinant bound in denominator form, assuming
the displayed bound for the total residue multiplicity. -/
theorem projective_hypersurface_minorGcd_of_count_bound {n s N p d M : ℕ}
    [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : MvPolynomial.map (Int.castRingHom (ZMod p)) f ≠ 0)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0) {H : ℝ} (hH : 0 ≤ H)
    (hcount : (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤
      (p : ℝ) ^ (n + 1) + H * (p : ℝ) ^ n) :
    ∃ e : ℕ,
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (p + H) *
        (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) -
        (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd
        (Matrix.of fun i j => MvPolynomial.eval (z i) (F j)) := by
  /- A point-count error of H times P^(m-1) increases the mth root by at most H.
  There is no degree or multiplicity loss in this normalization. -/
  /- An upper bound on the multiplicity root gives the usual denominator form
  of the sharp determinant exponent. -/
  by_cases hs : 0 < s
  · obtain ⟨hpos, e, hcut, he, hd⟩ :=
      projective_hypersurface_reduction_minorGcd hs f hf hf0 F hF z hprim hz
    let μ := projectiveHypersurfaceTotalMultiplicity f hf hf0
    have hμR : (0 : ℝ) < μ := mod_cast hpos
    have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hmajor : (p : ℝ) ^ (n + 1) + H * (p : ℝ) ^ n ≤ ((p : ℝ) + H) ^ (n + 1) := by
      rw [pow_succ ((p : ℝ) + H)]
      have hpow := pow_le_pow_left₀ hP (by linarith : (p : ℝ) ≤ p + H) n
      have h := mul_le_mul_of_nonneg_right hpow (add_nonneg hP hH)
      rw [pow_succ]; nlinarith
    have hroot : (μ : ℝ) ^ (1 / (n + 1 : ℝ)) ≤ p + H := by
      have hr := Real.rpow_le_rpow hμR.le (hcount.trans hmajor)
        (by positivity : (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ))
      rw [one_div, Real.pow_rpow_inv_natCast (add_nonneg hP hH) (Nat.succ_ne_zero n),
        ← one_div, Nat.cast_add, Nat.cast_one] at hr
      exact hr
    have hcoef : ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (p + H) ≤
        (((n + 1).factorial : ℝ) / μ) ^ (1 / (n + 1 : ℝ)) := by
      rw [Real.div_rpow (by positivity) hμR.le]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hroot
    have h := mul_le_mul_of_nonneg_right hcoef
      (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)))
    have heq (a : ℝ) : a * ((n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ))) =
        a * (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) := by ring
    simp only [heq] at h
    exact ⟨e, by linarith, hd⟩
  · have hs0 : s = 0 := by omega
    refine ⟨0, ?_, by simp⟩
    simp only [hs0, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0), mul_zero, sub_zero, le_refl]

end
end CCDN
