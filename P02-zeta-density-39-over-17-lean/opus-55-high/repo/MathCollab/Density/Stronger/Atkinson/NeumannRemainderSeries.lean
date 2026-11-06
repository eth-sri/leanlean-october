module
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from ZetaNeumannSeries.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_SOURCE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaNeumannRemainder
public import MathCollab.Density.Stronger.Fourth.SquareDivisorSeries
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaAtkinsonY0Term (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaAtkinsonY0Integrand T G L n x

def zetaAtkinsonTwoTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaAtkinsonTwoTermIntegrand T G L n x

def zetaNeumannRemainderTerm (T G L : ℝ) (n : ℕ) : ℂ :=
  divisorWeight n * (-(2 * Real.pi) : ℂ) * ∫ x : ℝ in Ioi 0, zetaNeumannRemainderIntegrand T G L n x

theorem norm_divisorDirichletTerm_real (s : ℝ) (n : ℕ) :
    ‖divisorDirichletTerm (s : ℂ) n‖ = ‖divisorWeight n‖ * (n : ℝ) ^ (-s) := by
  by_cases hn : n = 0
  · simp [hn, divisorDirichletTerm, LSeries.term, divisorWeight]
  simp only [divisorDirichletTerm, LSeries.norm_term_eq, hn, ite_false, divisorWeight,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem exists_norm_zetaNeumannRemainderTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ∀ n : ℕ,
        ‖zetaNeumannRemainderTerm T G L n‖ ≤ C * G * ‖divisorDirichletTerm (5 / 4) n‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_integral_zetaNeumannRemainder_le
  refine ⟨2 * Real.pi * C, by positivity, ?_⟩
  pm_377 zetaNeumannRemainderTerm
  have hpi : ‖(-(2 * Real.pi) : ℂ)‖ = 2 * Real.pi := by
    simp_all
  pm_4377
  rw [zetaNeumannRemainderTerm, norm_mul, norm_mul, hpi, hd]
  calc
    _ ≤ ‖divisorWeight n‖ * (2 * Real.pi) * (C * G * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound T G L hT hG hGT hL hwidth n (Nat.pos_of_ne_zero hn))
        (by positivity)
    _ = _ := by ring

section
variable {T G L : ℝ} (hT : 16 ≤ T) (hG : 0 < G)
include T G L hT hG
theorem summable_zetaNeumannRemainderTerm (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (zetaNeumannRemainderTerm T G L) := by pm_4378 exists_norm_zetaNeumannRemainderTerm_le

theorem zetaAtkinsonTwoTerm_eq_sub (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n =
      zetaAtkinsonY0Term T G L n - zetaNeumannRemainderTerm T G L n := by
  by_cases hn : n = 0
  · simp [hn, zetaAtkinsonTwoTerm, zetaAtkinsonY0Term, zetaNeumannRemainderTerm, divisorWeight]
  unfold zetaAtkinsonTwoTerm zetaAtkinsonY0Term zetaNeumannRemainderTerm
  simp_rw [zetaAtkinsonTwoTermIntegrand_eq_sub]
  rw [integral_sub
    (integrable_zetaAtkinsonY0Integrand hT hG hL hwidth (Nat.pos_of_ne_zero hn)).integrableOn
    (integrable_zetaNeumannRemainderIntegrand hT hG hL hwidth (Nat.pos_of_ne_zero hn)).integrableOn]
  ring
end

theorem exists_norm_tsum_zetaNeumannRemainderTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G →
        ‖∑' n : ℕ, zetaNeumannRemainderTerm T G L n‖ ≤ C * G := by pm_4379 exists_norm_zetaNeumannRemainderTerm_le summable_zetaNeumannRemainderTerm zetaNeumannRemainderTerm

end MathCollab.Density.Stronger.Atkinson
