/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.TailMargins
public import DOZZ.GMC.SharpMoments.SeibergUniform

/-! The uniform higher moments needed for the unequal-charge residue branch (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md). -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)

/-- After removing the critical root, the remaining finite root and infinity charge both
have strict positive-moment slack, throughout the full unequal-charge domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem residue_unequal_competitor_coulomb_moment
    (γ α2 α3 : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα2 : 0 < α2) (hα23 : α2 < α3) (hα3 : γ / 2 < α3) (hα3Q : α3 < Q γ) :
    ∃ d₀ ρ : ℝ, 0 < d₀ ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d₀ →
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α2] ![7] (α3 - α2 + ε))
          (reflectionExponent γ α3 + ρ) ∂P ≤ K := by
  let p := reflectionExponent γ α3
  let τ := min (2 * (α3 - γ / 2) / γ)
    (min (2 * α2 / γ) (2 * (α3 - α2) / γ))
  have hτ := residue_unequal_threshold_gap γ α2 α3 hγ hα2 hα23 hα3
  have hτb : τ ≤ 2 * (α3 - γ / 2) / γ := min_le_left ..
  have hτi : τ ≤ 2 * (α3 - α2) / γ := by grind
  have hτinf : τ ≤ 2 * α2 / γ := by grind
  let d₀ := min (α2 / 2) (γ * τ / 8)
  have hd₀ : 0 < d₀ := by positivity
  obtain ⟨K, hK, hKb⟩ := coulombMass_moment_uniform_pos P X hX γ hγ hγ2 M hM
    1 (δ := 1 / 8) (by norm_num) (by norm_num) (Rr := 14) (by norm_num)
    (Zs := 7) (A := α3 + 1) (g := τ / 8) (by norm_num) (by positivity)
  refine ⟨d₀, τ / 8, hd₀, by positivity, K, hK, ?_⟩
  intro ε hε hεd
  have hεloss : 2 * ε / γ < τ / 4 := by
    apply (div_lt_iff₀ hγ).mpr
    nlinarith only [(hεd.trans_le (min_le_right ..))]
  have hp := (residue_critical_order_bounds γ α3 hγ hα3 hα3Q).1
  have hbulk : 4 / γ ^ 2 - p = 2 * (α3 - γ / 2) / γ := by
    dsimp only [p]
    unfold reflectionExponent Q
    field_simp [hγ.ne']
    ring
  have hi : 2 / γ * (Q γ - α2) - p = 2 * (α3 - α2) / γ := by
    dsimp only [p]
    unfold reflectionExponent
    ring
  have hinf : 2 / γ * (Q γ - (α3 - α2 + ε)) - p = 2 * α2 / γ - 2 * ε / γ := by
    dsimp only [p]
    unfold reflectionExponent
    ring
  apply hKb ![7] ![α2] (α3 - α2 + ε) _
  · simp
  · norm_num
  · norm_num
  · intro j; fin_cases j
    change |α2| ≤ α3 + 1
    grind
  · grind
  · positivity
  · linarith
  · intro k; fin_cases k
    change p + τ / 8 + τ / 8 ≤ 2 / γ * (Q γ - α2)
    linarith
  · linarith

/-- On the equal-charge branch both critical roots are removed. The remaining charge at
infinity tends to zero and its Coulomb mass has a uniform moment strictly above the pole. -/
theorem residue_equal_background_coulomb_moment
    (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : γ / 2 < α) (hαQ : α < Q γ) :
    ∃ d₀ ρ : ℝ, 0 < d₀ ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d₀ →
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![] ![] ε)
          (reflectionExponent γ α + ρ) ∂P ≤ K := by
  let p := reflectionExponent γ α
  let τ := min (2 * (α - γ / 2) / γ) (2 * α / γ)
  have hα0 := lt_trans (by positivity) hα
  have hτ : 0 < τ := by positivity
  have hτb : τ ≤ 2 * (α - γ / 2) / γ := min_le_left ..
  have hτinf : τ ≤ 2 * α / γ := min_le_right ..
  let d₀ := min (α / 2) (γ * τ / 8)
  have hd₀ : 0 < d₀ := by positivity
  obtain ⟨K, hK, hKb⟩ := coulombMass_moment_uniform_pos P X hX γ hγ hγ2 M hM
    0 (δ := 1 / 8) (by norm_num) (by norm_num) (Rr := 1) (by norm_num)
    (Zs := 0) (A := α + 1) (g := τ / 8) (by norm_num) (by positivity)
  refine ⟨d₀, τ / 8, hd₀, by positivity, K, hK, ?_⟩
  intro ε hε hεd
  have hεloss : 2 * ε / γ < τ / 4 := by
    apply (div_lt_iff₀ hγ).mpr
    nlinarith only [(hεd.trans_le (min_le_right ..))]
  have hp := (residue_critical_order_bounds γ α hγ hα hαQ).1
  have hbulk : 4 / γ ^ 2 - p = 2 * (α - γ / 2) / γ := by
    dsimp only [p]
    unfold reflectionExponent Q
    field_simp [hγ.ne']
    ring
  have hinf : 2 / γ * (Q γ - ε) - p = 2 * α / γ - 2 * ε / γ := by
    dsimp only [p]
    unfold reflectionExponent
    ring
  apply hKb ![] ![] ε _
  · simp
  · simp
  · simp
  · simp
  · grind
  · positivity
  · linarith
  · simp
  · linarith

end

end DOZZ.Proofs
