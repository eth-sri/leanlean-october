module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks

/-! # Frequency decay uniformly over interval location and length -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The frequency decay constants depend only on the structural source bounds. -/
theorem interval_frequency_decay
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (E : IntervalEvolution lam Lam m Lb),
      ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
      (v : E.domain),
      TV (intervalFourierKernel E.kernel σ τ hστ ξ v) ≤
        C * Real.exp (-k * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ := interval_frequency_blocks
    lam Lam m Lb hlam hlamLam hm hmLb
  have hq : 0 < 1 - δ := sub_pos.mpr hδ1
  obtain ⟨hC, hk⟩ := decay_constants hδ hδ1 hL
  refine ⟨(1 - δ)⁻¹, -Real.log (1 - δ) / L, zero_lt_one.trans_le hC, hk, ?_⟩
  intro E σ τ hστ ξ v
  by_cases hξ : ξ = 0
  · subst ξ
    have htv := intervalFourierKernel_totalVariation_le_one E.kernel σ τ hστ 0 v
    have hreal := ENNReal.toReal_mono ENNReal.one_ne_top htv
    simp only [ENNReal.toReal_one] at hreal
    simpa only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, Real.sqrt_zero,
      Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero,
      Real.exp_zero, mul_one] using hreal.trans hC
  · have hN := frequency_norm_pos hξ
    let N := PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
    have hNp : 0 < N := Real.rpow_pos_of_pos hN _
    let T := L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))
    have hTdef : T = L / N := by
      dsimp [T, N]
      rw [Real.rpow_neg hN.le]
      rfl
    have hT : 0 < T := by rw [hTdef]; exact div_pos hL hNp
    have hc := (E.clauses).2.2
    have hb := interval_exponential_of_blocks E.kernel E.measurableSet E.realizes.2.2.2 hc hT hq
      (by linarith only [hδ] : 1 - δ ≤ 1) ξ
      (fun s w => hsteps E ξ hξ s w
        (le_add_of_nonneg_right hT.le)) σ τ hστ v
    have he : -(-Real.log (1 - δ) / T) * (τ - σ) =
        -(-Real.log (1 - δ) / L) * (τ - σ) * N := by
      rw [hTdef]
      field_simp
    rw [he] at hb
    exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Interval
