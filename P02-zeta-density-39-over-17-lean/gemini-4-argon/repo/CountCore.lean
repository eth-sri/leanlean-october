module

public import MathCollab.Density.ZetaCounting
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

@[expose] public section

namespace LewkoDensityPalomar

noncomputable def zeroWeight (σ T : ℝ) (ρ : ℂ) : ℝ≥0∞ := by
  classical
  exact if riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T
    then (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) else 0

noncomputable def zeroCount (σ T : ℝ) : ℝ≥0∞ := ∑' ρ : ℂ, zeroWeight σ T ρ

theorem zeroCount_eq_zetaDensityCount (σ T : ℝ) :
    zeroCount σ T = (MathCollab.Density.zetaDensityCount σ T : ℝ≥0∞) := by
  classical
  have hF : ∀ ρ : ℂ, ρ ∈ MathCollab.Density.zetaZeroFinset σ (-T) T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    intro ρ
    rw [MathCollab.Density.mem_zetaDensityFinset]
    simp only [MathCollab.Density.IsNontrivialZetaZero, and_assoc]
  calc
    zeroCount σ T = ∑ ρ ∈ MathCollab.Density.zetaZeroFinset σ (-T) T, zeroWeight σ T ρ :=
      tsum_eq_sum (fun ρ hρ => by simp only [zeroWeight, ite_eq_right (mt (hF ρ).mpr hρ)])
    _ = ∑ ρ ∈ MathCollab.Density.zetaZeroFinset σ (-T) T, (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun ρ hρ => by simp only [zeroWeight, ite_eq_left ((hF ρ).mp hρ)])
    _ = _ := by simp [MathCollab.Density.zetaDensityCount, MathCollab.Density.zetaSlabCount, MathCollab.Density.zetaMultiplicity]

theorem bound_of_weaken {σ p q ε : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (MathCollab.Density.zetaDensityCount σ T : ℝ) ≤ C * T ^ (p + ε))
    (hpq : p ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (q + ε)) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun T hT => ?_⟩
  rw [zeroCount_eq_zetaDensityCount, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal ((hb T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hC.le))

theorem bound_of_div_weaken {σ c d c' d' ε : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (MathCollab.Density.zetaDensityCount σ T : ℝ) ≤ C * T ^ (c * (1 - σ) / d + ε))
    (hd : 0 < d) (hd' : 0 < d') (h1 : σ ≤ 1) (hc : c * d' ≤ c' * d) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((c' / d') * (1 - σ) + ε)) := by
  apply bound_of_weaken h
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hd hd']
  nlinarith

