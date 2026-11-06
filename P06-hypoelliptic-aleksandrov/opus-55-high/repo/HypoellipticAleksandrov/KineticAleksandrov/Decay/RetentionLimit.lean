module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionMatrix
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceComparison
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The coefficient-uniform retention rate bound

This elementary closing bound preserves the source's ellipticity signs and
literal radius dependence.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

/-- The explicit retention rate has the stated structural upper bound. -/
theorem retention_rate_uniform {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam ρ H : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hρ : 0 < ρ) (hc : 0 < barrierC d N lam Lam) :
    barrierRate d N lam Lam ρ H ≤
      (2 * N * d * Lam + (N : ℝ) ^ 2 / barrierC d N lam Lam) * (ρ⁻¹ ^ 2 + H ^ 2) := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hlamLam).le
  have hA : 0 ≤ 2 * N * d * Lam := by positivity
  have hB : 0 ≤ N ^ 2 / barrierC d N lam Lam := by positivity
  have h1 : 0 ≤ (2 * N * d * Lam) * H ^ 2 := mul_nonneg hA (sq_nonneg H)
  have h2 : 0 ≤ (N ^ 2 / barrierC d N lam Lam) * ρ⁻¹ ^ 2 :=
    mul_nonneg hB (sq_nonneg _)
  unfold barrierRate
  simp only [div_eq_mul_inv, inv_pow] at h1 h2 ⊢
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Decay
