module

public import OAI.NumberTheory.DirichletL.Moments.Cancellation

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentCounting

theorem norm_tsum_ideal_ball (f : Ideal ActualEisensteinCubic.O → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal ActualEisensteinCubic.O, f I‖ ≤ 128 * M * H := by
  classical
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := ActualEisensteinCubic.O) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal ActualEisensteinCubic.O) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal ActualEisensteinCubic.O, f I) = ∑ I ∈ S, f I :=
    tsum_eq_sum (by grind)
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact by grind
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := by grind
    have hcount := DescentFiberCost.finite_ideal_count_real S H hH1
      (by grind)
      (by grind)
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (by grind)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (128 * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity

theorem norm_linear_coefficient_le (S : ℝ → ℂ) (v : ℂ) (C E : ℝ) (hE : 0 ≤ E)
    (herror : ∀ X : ℝ, 0 < X → ‖S X - (X : ℂ) * v‖ ≤ E)
    (habsolute : ∀ X : ℝ, 0 < X → ‖S X‖ ≤ C * X) : ‖v‖ ≤ C := by
  by_contra hn
  have hδ : 0 < ‖v‖ - C := by linarith
  let X := (E + 1) / (‖v‖ - C)
  have hX : 0 < X := by positivity
  have heq : X * (‖v‖ - C) = E + 1 := by grind
  have h := norm_le_norm_sub_add ((X : ℂ) * v) (S X)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX.le, norm_sub_rev] at h
  grind

end SevenEighths.CenteredMomentCounting
end

end OAI
