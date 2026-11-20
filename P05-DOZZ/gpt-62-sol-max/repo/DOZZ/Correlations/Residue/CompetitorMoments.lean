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

private theorem residue_reflectionExponent_slack (γ a b : ℝ) (hγ : 0 < γ) (h : b < a) :
    0 < 2 / γ * (Q γ - b) - reflectionExponent γ a := by
  calc
    _ = 2 / γ * (a - b) := by unfold reflectionExponent; ring
    _ > 0 := by positivity


section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
include Ω

/-- Positive moment slack persists under a small increase of the charge at infinity,
with zero or one finite competitor. -/
private theorem residue_background_moment {N : ℕ} [Subsingleton (Fin N)]
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (a : Fin N → ℝ) (β p τ : ℝ) (hp : 0 < p) (hτ : 0 < τ)
    (hbulk : p + τ ≤ 4 / γ ^ 2) (hroot : ∀ j, p + τ ≤ 2 / γ * (Q γ - a j))
    (hinf : p + τ ≤ 2 / γ * (Q γ - β)) :
    ∃ d ρ : ℝ, 0 < d ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d →
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) a z (β + ε)) (p + ρ) ∂P ≤ K := by
  classical
  let Z := ∑ j, ‖z j‖
  let A := ∑ j, |a j|
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hz j : ‖z j‖ ≤ Z := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have ha j : |a j| ≤ A := Finset.single_le_sum (f := fun j => |a j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  obtain ⟨K, hK, hKb⟩ := coulombMass_moment_uniform_pos P X hX γ hγ hγ2 M hM
    N (δ := 1 / 8) (by norm_num) (by norm_num) (Rr := 1 + 2 * Z) (by linarith)
    (Zs := Z) (A := A + |β| + 1) (g := τ / 4) hZ (by positivity)
  refine ⟨min 1 (γ * τ / 4), τ / 4, by positivity, by positivity, K, hK, fun ε hε hd => ?_⟩
  have hε1 : ε < 1 := hd.trans_le (min_le_left ..)
  have hετ : 2 * ε / γ < τ / 2 := (div_lt_iff₀ hγ).2 (by
    have h := hd.trans_le (min_le_right (1 : ℝ) (γ * τ / 4))
    linarith)
  refine hKb z a (β + ε) (p + τ / 4) (fun j k h => (h (Subsingleton.elim j k)).elim)
    le_rfl (fun j => by linarith [hz j]) (fun j => by linarith [ha j, abs_nonneg β]) ?_
    (by positivity) (by linarith) (fun j => by linarith [hroot j]) ?_
  · linarith [abs_add_le β ε, abs_of_pos hε]
  · calc
      _ ≤ 2 / γ * (Q γ - β) - 2 * ε / γ := by linarith
      _ = _ := by ring

/-- After removing the critical root, the remaining finite root and infinity charge both
have strict positive-moment slack, throughout the full unequal-charge domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem residue_unequal_competitor_coulomb_moment (γ α2 α3 : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα2 : 0 < α2) (hα23 : α2 < α3) (hα3 : γ / 2 < α3) (hα3Q : α3 < Q γ) :
    ∃ d₀ ρ : ℝ, 0 < d₀ ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d₀ →
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α2] ![7] (α3 - α2 + ε))
          (reflectionExponent γ α3 + ρ) ∂P ≤ K := by
  let p := reflectionExponent γ α3
  obtain ⟨hp, hp4⟩ := residue_critical_order_bounds γ α3 hγ hα3 hα3Q
  let τ := min (4 / γ ^ 2 - p) (min (2 / γ * (Q γ - α2) - p)
    (2 / γ * (Q γ - (α3 - α2)) - p))
  have hτ : 0 < τ := lt_min (sub_pos.mpr hp4) (lt_min
    (residue_reflectionExponent_slack γ α3 α2 hγ hα23)
    (residue_reflectionExponent_slack γ α3 _ hγ (by linarith)))
  apply residue_background_moment P X M γ hγ hγ2 hX hM ![7] ![α2] (α3 - α2) p τ hp hτ
  · exact (le_sub_iff_add_le').mp (min_le_left ..)
  · intro j; fin_cases j
    change p + τ ≤ 2 / γ * (Q γ - α2)
    exact (le_sub_iff_add_le').mp ((min_le_right ..).trans (min_le_left ..))
  · exact (le_sub_iff_add_le').mp ((min_le_right ..).trans (min_le_right ..))

/-- On the equal-charge branch both critical roots are removed. The remaining charge at
infinity tends to zero and its Coulomb mass has a uniform moment strictly above the pole. -/
theorem residue_equal_background_coulomb_moment (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : γ / 2 < α) (hαQ : α < Q γ) :
    ∃ d₀ ρ : ℝ, 0 < d₀ ∧ 0 < ρ ∧ ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ε < d₀ →
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![] ![] ε)
          (reflectionExponent γ α + ρ) ∂P ≤ K := by
  let p := reflectionExponent γ α
  obtain ⟨hp, hp4⟩ := residue_critical_order_bounds γ α hγ hα hαQ
  let τ := min (4 / γ ^ 2 - p) (2 / γ * (Q γ - 0) - p)
  have hτ : 0 < τ := lt_min (sub_pos.mpr hp4)
    (residue_reflectionExponent_slack γ α 0 hγ ((by positivity : 0 < γ / 2).trans hα))
  simpa only [zero_add] using
    residue_background_moment P X M γ hγ hγ2 hX hM ![] ![] 0 p τ hp hτ
      ((le_sub_iff_add_le').mp (min_le_left ..)) (fun j => Fin.elim0 j)
      ((le_sub_iff_add_le').mp (min_le_right ..))

end
end DOZZ.Proofs
