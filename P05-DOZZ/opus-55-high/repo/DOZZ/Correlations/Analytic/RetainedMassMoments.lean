/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.GMC.SharpMoments.MomentRange

/-! Real moment envelopes for the charge-independent mass in finite-radius vertex observables. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (O : Set ℂ) (ho : IsOpen O) (hb : Bornology.IsBounded O) (hn : O.Nonempty)
include hX hγ hγ2 hM ho hb hn

/-- On bounded nonempty open sets, the unweighted chaos mass is positive and finite almost surely. -/
theorem open_mass_pos_finite_ae
    :
    ∀ᵐ ω ∂P, M ω O ≠ 0 ∧ M ω O ≠ ⊤ := by
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM O ho.measurableSet
  have hp : 1 < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith
  have hi' := (equatorGFF_GMC_moment_range P X hX γ hγ hγ2 M hM O ho hb hn (-1)).mpr
    (show (-1) < 4 / γ ^ 2 by linarith)
  filter_upwards [ae_lt_top' (hm.pow_const (1 : ℝ)) ((equatorGFF_GMC_moment_range P X hX γ hγ hγ2 M hM O ho hb hn 1).mpr hp).ne,
    ae_lt_top' (hm.pow_const (-1 : ℝ)) hi'.ne] with ω h1 h2
  aesop

/-- Every real power below the bulk threshold is integrable for the real retained mass. -/
theorem open_mass_real_power_integrable
    (p : ℝ) (hp : p < 4 / γ ^ 2) :
    Integrable (fun ω => (M ω O).toReal ^ p) P := by
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM O ho.measurableSet
  have hmeas : AEMeasurable (fun ω => (M ω O).toReal ^ p) P := by
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  change (∫⁻ ω, ‖(M ω O).toReal ^ p‖ₑ ∂P) < ⊤
  calc
    _ = ∫⁻ ω, M ω O ^ p ∂P := by
      apply lintegral_congr_ae
      filter_upwards [(open_mass_pos_finite_ae P X hX γ hγ hγ2 M hM O ho hb hn)] with ω hω
      rw [Real.enorm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _),
        ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hω.1 hω.2), ENNReal.ofReal_toReal hω.2]
    _ < ⊤ := ((equatorGFF_GMC_moment_range P X hX γ hγ hγ2 M hM O ho hb hn p).mpr hp)

end

end

end DOZZ.Proofs
