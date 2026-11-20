/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Determinant.HypersurfaceMultiplicityEstimate

/-! Numerical normalization of a finite-field hypersurface count, as in
CCDN Lemma 2.8. The input count bound is an explicit hypothesis. -/

@[expose] public section
namespace CCDN
noncomputable section

section

variable (m s e : ℕ) (hm : 0 < m)

include hm in
/-- A point-count error of H times P^(m-1) increases the mth root by at most H.
There is no degree or multiplicity loss in this normalization. -/
theorem hypersurface_count_root_bound
    {P H T : ℝ} (hP : 0 ≤ P) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hcount : T ≤ P ^ m + H * P ^ (m - 1)) :
    T ^ (1 / (m : ℝ)) ≤ P + H := by
  have hmajor : P ^ m + H * P ^ (m - 1) ≤ (P + H) ^ m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    simp only [Nat.succ_sub_one, pow_succ]
    have hpow := pow_le_pow_left₀ hP (show P ≤ P + H by linarith) n
    nlinarith
  calc
    _ ≤ ((P + H) ^ m) ^ (1 / (m : ℝ)) :=
      Real.rpow_le_rpow hT (hcount.trans hmajor) (by positivity)
    _ = P + H := by
      grind [one_div, Real.pow_rpow_inv_natCast, add_nonneg, Nat.ne_of_gt]

include hm in
/-- An upper bound on the multiplicity root gives the usual denominator form
of the sharp determinant exponent. -/
theorem local_exponent_separated_lower_bound_of_root_bound
    {μ : ℕ} (hμ : 0 < μ) {Q : ℝ}
    (hroot : (μ : ℝ) ^ (1 / (m : ℝ)) ≤ Q)
    (hcutoff : ∀ K : ℕ, s * K ≤ e + μ * (m + K).choose (m + 1)) :
    (m.factorial : ℝ) ^ (1 / (m : ℝ)) / Q * m / (m + 1) *
      (s : ℝ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * s ≤ e := by
  have hμR : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hcoef : (m.factorial : ℝ) ^ (1 / (m : ℝ)) / Q ≤
      ((m.factorial : ℝ) / μ) ^ (1 / (m : ℝ)) := by
    rw [Real.div_rpow (by positivity) hμR.le]
    bound
  have hscale : (0 : ℝ) ≤ (m : ℝ) / (m + 1) * (s : ℝ) ^ (1 + 1 / (m : ℝ)) := by positivity
  have h := mul_le_mul_of_nonneg_right hcoef hscale
  have he := local_exponent_separated_lower_bound m s e hm hμ hcutoff
  grind

end

/-- The global single-prime determinant bound in denominator form, assuming
the displayed bound for the total residue multiplicity. -/
theorem projective_hypersurface_minorGcd_of_count_bound {n s N p d M : ℕ}
    [Fact p.Prime] (f : IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d)
    (hf0 : residueEquation p f ≠ 0)
    (F : Fin N → IntegerPolynomial (n + 3)) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0) {H : ℝ} (hH : 0 ≤ H)
    (hcount : (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤
      (p : ℝ) ^ (n + 1) + H * (p : ℝ) ^ n) :
    ∃ e : ℕ,
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (p + H) *
        (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) -
        (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd
        (valueMatrix z F) := by
  by_cases hs : 0 < s
  · obtain ⟨hpos, e, hcut, _, hd⟩ :=
      projective_hypersurface_reduction_minorGcd hs f hf hf0 F hF z hprim hz
    have hroot := hypersurface_count_root_bound (n + 1) (by omega)
      (Nat.cast_nonneg p) hH (Nat.cast_nonneg _)
      (by assumption)
    refine ⟨e, ?_, hd⟩
    exact_mod_cast local_exponent_separated_lower_bound_of_root_bound _ s e (by omega) hpos hroot hcut
  · have hs0 : s = 0 := by omega
    refine ⟨0, ?_, by simp⟩
    simp_rw [hs0, Nat.cast_zero, Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0), mul_zero, sub_zero, le_refl]

end
end CCDN
