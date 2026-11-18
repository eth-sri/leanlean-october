module

public import MathCollab.Density.ZetaCounting
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

theorem zeroCount_le_of_nat {σ x : ℝ} (T : ℝ)
    (h : (MathCollab.Density.zetaDensityCount σ T : ℝ) ≤ x) :
    zeroCount σ T ≤ ENNReal.ofReal x := by
  classical
  have hF : ∀ ρ : ℂ, ρ ∈ MathCollab.Density.zetaZeroFinset σ (-T) T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := fun ρ => by
    rw [MathCollab.Density.mem_zetaZeroFinset, ← abs_le]
    simp [MathCollab.Density.IsNontrivialZetaZero, and_assoc]
  have heq : zeroCount σ T = (MathCollab.Density.zetaDensityCount σ T : ℝ≥0∞) := by
    calc
      zeroCount σ T = ∑ ρ ∈ MathCollab.Density.zetaZeroFinset σ (-T) T, zeroWeight σ T ρ :=
        tsum_eq_sum fun ρ hρ => by simp [zeroWeight, mt (hF ρ).mpr hρ]
      _ = ∑ ρ ∈ MathCollab.Density.zetaZeroFinset σ (-T) T,
            (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) :=
        Finset.sum_congr rfl fun ρ hρ => by simp [zeroWeight, (hF ρ).mp hρ]
      _ = _ := by
        simp [MathCollab.Density.zetaDensityCount, MathCollab.Density.zetaSlabCount,
          MathCollab.Density.zetaMultiplicity]
  rw [heq, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h

theorem of_db {σ p ε : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (MathCollab.Density.zetaDensityCount σ T : ℝ) ≤ C * T ^ (p + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (p + ε)) :=
  let ⟨C, hC, hb⟩ := h
  ⟨C, hC, fun T hT => zeroCount_le_of_nat T (hb T hT)⟩

end LewkoDensityPalomar
