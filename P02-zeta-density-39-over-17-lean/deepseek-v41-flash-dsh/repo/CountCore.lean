module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal

@[expose] public section

namespace LewkoDensityPalomar

/-- Analytic multiplicity of an actual global zeta zero in the closed height window.
The critical strip is open; the density and height cutoffs are closed. -/
noncomputable def zeroWeight (σ T : ℝ) (ρ : ℂ) : ℝ≥0∞ := by
  classical
  exact if riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T
    then (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) else 0

/-- The full count of actual zeta zeros with analytic multiplicity and both signs
of the ordinate. This is a genuine nonnegative extended-real sum. -/
noncomputable def zeroCount (σ T : ℝ) : ℝ≥0∞ := ∑' ρ : ℂ, zeroWeight σ T ρ

/-- An exact enumeration gives exactly the same multiplicity count. -/
theorem zeroCount_eq_finset (σ T : ℝ) (F : Finset ℂ)
    (hF : ∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T) :
    zeroCount σ T = ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞) := by
  classical
  calc
    zeroCount σ T = ∑ ρ ∈ F, zeroWeight σ T ρ := by
      apply tsum_eq_sum
      intro ρ hρ
      simp only [zeroWeight, ite_eq_right (mt (hF ρ).mpr hρ)]
    _ = ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp only [zeroWeight, ite_eq_left ((hF ρ).mp hρ)]
    _ = ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ≥0∞) := by simp

/-- Such an enumeration exists without any analytic or finiteness hypothesis. -/
theorem exact_zero_set_exists (σ T : ℝ) : ∃ F : Finset ℂ,
    ∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  classical
  have hfin : {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      σ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite := by
    apply ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset
    intro ρ hρ
    refine ⟨?_, hρ.1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + |T| := by
        rw [abs_of_pos hρ.2.1]
        linarith [hρ.2.2.1, hρ.2.2.2.2, le_abs_self T]
  exact ⟨hfin.toFinset, fun ρ => Set.Finite.mem_toFinset hfin⟩

/-- Transfer a real-valued full enumeration bound without changing any
quantifier or discarding any possible infinite count. -/
theorem bound_of_literal {σ p ε : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ F : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        σ ≤ ρ.re ∧ |ρ.im| ≤ T) →
      ((∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤ C * T ^ (p + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (p + ε)) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨F, hF⟩ := exact_zero_set_exists σ T
  rw [zeroCount_eq_finset σ T F hF, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hb T hT F hF)

end LewkoDensityPalomar
