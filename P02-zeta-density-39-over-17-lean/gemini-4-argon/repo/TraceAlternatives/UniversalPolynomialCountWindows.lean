module
public import TraceAlternatives.UniversalPolynomialCount

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Filter Finset GuthMaynard.Improvement GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

structure UniversalCountWindow (σ a : ℝ) : Prop where
  sigma_low : 4/5 ≤ σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  budgets : ∀ x : ℝ, a ≤ x → ∀ j : Fin 3, ∀ i : Fin 5,
    0 ≤ universalTraceEnergyMargin σ a x j i
  low_budget : ∀ x : ℝ, a ≤ x → 1/100 ≤ universalLowMargin σ a x

theorem universalCountWindow_of_fraction {σ P D : ℝ}
    (hσ : 4/5 ≤ σ) (hσ1 : σ < 1) (hd : 0 < D)
    (hal : D ≤ 2*P) (hah : 3*P < 2*D)
    (hlow : 51*D ≤ 100*P*(7*σ/2-2))
    (hm : ∀ j : Fin 3, ∀ i : Fin 5,
      0 ≤ (2-universalTraceB j-universalTraceG j-universalTraceD j*gmEnergyR i)*3*P*(1-σ)-
        (universalTraceA j+universalTraceD j*gmEnergyV i)*D+
        ((4-2*universalTraceB j-universalTraceD j*gmEnergyW i)*σ-3+universalTraceB j-
          universalTraceD j*gmEnergyU i)*P) :
    UniversalCountWindow σ (P/D) := by
  refine ⟨hσ, hσ1, (le_div_iff₀ hd).mpr (by linarith), (div_lt_iff₀ hd).mpr (by linarith), ?_, ?_⟩
  · intro x hxa j i
    have h0 : 0 ≤ universalTraceEnergyMargin σ (P/D) (P/D) j i := by
      have := hd.ne'
      refine (div_nonneg (hm j i) hd.le).trans_eq ?_
      unfold universalTraceEnergyMargin
      field_simp
      ring
    exact h0.trans (universalTraceEnergyMargin_mono_length hσ hxa j i)
  · intro x hxa
    have hBase : 51/100 ≤ (P/D)*(7*σ/2-2) := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hd).mpr (by linarith)
    have hMono := mul_le_mul_of_nonneg_left hxa (show 0 ≤ 5*σ-7/2 by linarith)
    unfold universalLowMargin
    nlinarith only [hBase, hMono]

theorem universal_polynomial_count_window_loss {σ a δ : ℝ}
    (hw : UniversalCountWindow σ a) (hδ : 0 < δ) (hδsmall : δ ≤ 1/1800) (hδa : δ ≤ (1-3*a/2)/2) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ T t₀ N : ℝ, T₀ ≤ T → T^a ≤ N → N ≤ T^(3*a/2+δ) →
      ∀ b : ℕ → ℂ, (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
      (W.card:ℝ) ≤ C*T^(3*a*(1-σ)+144*δ) :=
  universal_polynomial_count_loss hw.sigma_low hw.sigma_high hw.a_low hw.a_high hδ hδsmall hδa hw.budgets hw.low_budget

