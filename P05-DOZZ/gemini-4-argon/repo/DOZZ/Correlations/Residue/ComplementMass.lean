/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ChartMass
public import DOZZ.Correlations.Residue.CompetitorMoments
import DOZZ.ShiftEquations.Mobius.InversionMoment

/-! Domination of the actual GMC mass outside the critical insertion balls. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs


/-- The extended insertion factor has the same deterministic bound. -/
theorem residue_coulomb_factor_le (γ α : ℝ) (hγα : 0 ≤ γ * α) z x
    (hx : x ∉ Metric.ball z 1) :
    ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z‖)) (γ * α) ≤
      ENNReal.ofReal ((‖z‖ + 2) ^ (γ * α)) := by
  have residue_normPlus_div_le : normPlus x / ‖x - z‖ ≤ ‖z‖ + 2 := by
    have hd : 1 ≤ ‖x - z‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx
    have hnp : normPlus x ≤ ‖x - z‖ + ‖z‖ + 1 := max_le (by linarith only [hd, norm_nonneg z]) (by linarith only [(by simpa only [sub_add_cancel] using norm_add_le (x - z) z)])
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
    nlinarith only [hnp, hd, norm_nonneg z]
  have hd : 0 < ‖x - z‖ := by
    linarith only [(by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx)]
  rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos (div_pos (normPlus_pos' x) hd)]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (div_pos (normPlus_pos' x) hd).le
    (residue_normPlus_div_le) hγα)

/-- Factor the critical root off the two-root Coulomb weight. -/
theorem residue_coulombWeight_two_split γ a b c z w x :
    coulombWeight γ ![a, b] ![z, w] c x =
      ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z‖)) (γ * a) *
        coulombWeight γ ![b] ![w] c x := by
  unfold coulombWeight
  simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact mul_assoc _ _ _


/-- Quantitative moment domination of the critical-ball complement. -/
theorem residue_complement_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ a b c t : ℝ) (hγα : 0 ≤ γ * a) (ht : 0 ≤ t) z w :
    (∫⁻ ω, ENNReal.rpow
      (∫⁻ x, if x ∉ Metric.ball z 1 then coulombWeight γ ![a, b] ![z, w] c x else 0 ∂M ω) t ∂P) ≤
      (ENNReal.ofReal ((‖z‖ + 2) ^ (γ * a))) ^ t *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![b] ![w] c) t ∂P := by
  have residue_complement_mass_le (μ : Measure ℂ) : (∫⁻ x, if x ∉ Metric.ball z 1 then coulombWeight γ ![a, b] ![z, w] c x else 0 ∂μ) ≤ ENNReal.ofReal ((‖z‖ + 2) ^ (γ * a)) * coulombMass γ μ ![b] ![w] c := by
    rw [coulombMass_eq_lintegral_coulombWeight, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hx : x ∈ Metric.ball z 1
    · simp [hx]
    · rw [ite_eq_left hx, residue_coulombWeight_two_split]
      exact mul_le_mul_left (residue_coulomb_factor_le γ a hγα z x hx) _
  rw [← lintegral_const_mul' _ _ ((ENNReal.rpow_lt_top_of_nonneg ht ENNReal.ofReal_ne_top).ne)]
  apply lintegral_mono
  intro ω
  calc _ ≤ (ENNReal.ofReal ((‖z‖ + 2) ^ (γ * a)) * coulombMass γ (M ω) ![b] ![w] c) ^ t :=
      ENNReal.rpow_le_rpow (residue_complement_mass_le (M ω)) ht
    _ = _ := by
      rw [inversionMoment_mul_rpow (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)).ne' ENNReal.ofReal_ne_top]
      rfl


/-- Moment version of the all-critical-ball complement domination. -/
theorem residue_all_complement_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    {N} (γ c t : ℝ) (α : Fin N → ℝ) (hα : ∀ k, 0 ≤ γ * α k)
    (z : Fin N → ℂ) (ht : 0 ≤ t) :
    (∫⁻ ω, ENNReal.rpow
      (∫⁻ x, if ∀ k, x ∉ Metric.ball (z k) 1 then coulombWeight γ α z c x else 0 ∂M ω) t ∂P) ≤
      (∏ k, ENNReal.ofReal ((‖z k‖ + 2) ^ (γ * α k))) ^ t *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![] ![] c) t ∂P := by
  have residue_all_complement_mass_le (μ : Measure ℂ) : (∫⁻ x, if ∀ k, x ∉ Metric.ball (z k) 1 then coulombWeight γ α z c x else 0 ∂μ) ≤ (∏ k, ENNReal.ofReal ((‖z k‖ + 2) ^ (γ * α k))) * coulombMass γ μ ![] ![] c := by
    rw [coulombMass_eq_lintegral_coulombWeight, ← lintegral_const_mul' _ _ ((ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)).ne)]
    apply lintegral_mono
    intro x
    change (if ∀ k, x ∉ Metric.ball (z k) 1 then coulombWeight γ α z c x else 0) ≤ _
    by_cases hx : ∀ k, x ∉ Metric.ball (z k) 1
    · rw [ite_eq_left hx]
      unfold coulombWeight
      simp only [Fin.prod_univ_zero, one_mul]
      exact mul_le_mul_left (Finset.prod_le_prod fun k _ => residue_coulomb_factor_le γ (α k) (hα k) (z k) x (hx k)) _
    · rw [ite_eq_right hx]
      exact zero_le
  let A := ∏ k, ENNReal.ofReal ((‖z k‖ + 2) ^ (γ * α k))
  have hAtop : A ≠ ⊤ := (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)).ne
  rw [← lintegral_const_mul' _ _ ((ENNReal.rpow_lt_top_of_nonneg ht hAtop).ne)]
  apply lintegral_mono
  intro ω
  calc _ ≤ (A * coulombMass γ (M ω) ![] ![] c) ^ t :=
      ENNReal.rpow_le_rpow (residue_all_complement_mass_le (M ω)) ht
    _ = _ := by rw [inversionMoment_mul_rpow (Finset.prod_ne_zero_iff.mpr fun k _ => (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)).ne') hAtop]; rfl

end DOZZ.Proofs
