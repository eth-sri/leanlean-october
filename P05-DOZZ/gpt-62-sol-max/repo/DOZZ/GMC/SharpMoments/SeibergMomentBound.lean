/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.MeasureTheory.PowerSums

/-! # Explicit moment bounds for the Coulomb mass

Positive moments of the Coulomb mass are bounded by an explicit combination of the weighted local
moments at the roots, the moment of the mass of a bounded disk, and the weighted local moment of
the inverted measure at the origin, with constants depending only on the root separation, the
exterior radius, the root sizes and the charges. Nonpositive moments are bounded through a fixed
exterior disk. These are the inputs for uniformity over compact parameter sets. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Nonpositive moments of the Coulomb mass, uniformly over exterior radii, charges and orders in
compact ranges. -/
theorem coulombMass_moment_uniform_nonpos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : ℕ) (Rr : ℝ) (hRr1 : 1 ≤ Rr) (A tmin : ℝ) (htmin : tmin ≤ 0) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (z : Fin N → ℂ) (α : Fin N → ℝ) (αinf t : ℝ),
      (∀ j, 2 * ‖z j‖ ≤ Rr) → (∀ j, |α j| ≤ A) → |αinf| ≤ A → tmin ≤ t → t ≤ 0 →
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P ≤ K := by
  let _  := hX.1
  set cmin : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
    ENNReal.ofReal ((Rr + 2) ^ (-(γ * A))) with hcmin
  set B : Set ℂ := Metric.ball (((Rr + 1 : ℝ)) : ℂ) (1 / 8) with hB
  have hBm  :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B Metric.isOpen_ball.measurableSet
  have hc0 : cmin ≠ 0 := mul_ne_zero
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hctop : cmin ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨cmin ^ tmin * (1 + gmcMassMoment P M B tmin),
    ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc0 hctop).lt_top
      (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
        gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM _ (1 / 8) (by norm_num) le_rfl
          tmin (lt_of_le_of_lt htmin (by positivity))⟩), ?_⟩
  intro z α αinf t hzRr hαA hαinfA htt ht0
  -- the uniform lower constant
  by_cases hNA : 0 ≤ A
  · have hsum : ∑ j, |γ * α j| ≤ N * (γ * A) := by
      calc ∑ j, |γ * α j| ≤ ∑ _j : Fin N, γ * A := Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_pos hγ]
            exact mul_le_mul_of_nonneg_left (hαA j) hγ.le
        _ = N * (γ * A) := by simp
    have hinf : |γ * αinf| ≤ γ * A := by
      rw [abs_mul, abs_of_pos hγ]
      exact mul_le_mul_of_nonneg_left hαinfA hγ.le
    have hcle : cmin ≤ ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((Rr + 2) ^ (-|γ * αinf|)) := by
      rw [hcmin]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
      · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hc1 : cmin ≤ 1 := by
      rw [hcmin, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      refine ENNReal.ofReal_le_one.mpr ?_
      have h1 : (2 : ℝ) ^ (-(N * (γ * A))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg N) (mul_nonneg hγ.le hNA)))
      have h2 : (Rr + 2) ^ (-(γ * A)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
          (neg_nonpos.mpr (mul_nonneg hγ.le hNA))
      calc (2 : ℝ) ^ (-(N * (γ * A))) * (Rr + 2) ^ (-(γ * A)) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) zero_le_one
        _ = 1 := one_mul 1
    have hlow  := fun ω =>
      (mul_le_mul' hcle le_rfl).trans (coulombMass_ge_exterior_ball (M ω) γ α z αinf hRr1 hzRr)
    calc ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P
        ≤ ∫⁻ ω, cmin ^ tmin * (1 + M ω B ^ tmin) ∂P := by
          apply lintegral_mono
          intro ω
          calc ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ≤ (cmin * M ω B) ^ t :=
                ennreal_rpow_antitone_of_nonpos (hlow ω) ht0
            _ = cmin ^ t * M ω B ^ t := ennreal_mul_rpow_of_ne_zero_ne_top _ _ hc0 hctop t
            _ ≤ cmin ^ tmin * (1 + M ω B ^ tmin) := by
                refine mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hc1 htt) ?_
                rcases le_total 1 (M ω B) with h1 | h1
                · exact ((ennreal_rpow_antitone_of_nonpos h1 ht0).trans_eq
                    (ENNReal.one_rpow t)).trans le_self_add
                · exact (ENNReal.rpow_le_rpow_of_exponent_ge h1 htt).trans le_add_self
      _ = cmin ^ tmin * (1 + gmcMassMoment P M B tmin) := by
          have h1m : AEMeasurable (fun ω => 1 + M ω B ^ tmin) P :=
            aemeasurable_const.add (hBm.pow_const tmin)
          have hone : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P := aemeasurable_const
          rw [lintegral_const_mul'' _ h1m, lintegral_add_left' hone, lintegral_const,
            measure_univ, mul_one]
          rfl
  · -- a negative charge bound admits no parameters
    exact absurd ((abs_nonneg _).trans hαinfA) hNA

end DOZZ.Proofs
