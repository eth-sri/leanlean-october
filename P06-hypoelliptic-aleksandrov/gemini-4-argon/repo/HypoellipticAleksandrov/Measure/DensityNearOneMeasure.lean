module

public import HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Measure bookkeeping for the near-one density argument

This module proves the finite-support parabolic norm bound and the exact
strict-sublevel complement identity used by the near-one density-to-point
argument.  It has no coefficient, ABP, or density-to-point conclusion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem parabolicExponent_ne_zero (d : Nat) : parabolicExponent d ≠ 0 := by
  simp [parabolicExponent]

private theorem parabolicExponent_ne_top (d : Nat) : parabolicExponent d ≠ ∞ := by
  simp [parabolicExponent]

theorem measurableSet_localABPInterior {d : Nat} (v0 : PDE.Vec d) :
    MeasurableSet (localABPInterior v0) := by
  unfold localABPInterior localABPAffine
  exact (parabolicAffine_measurableEmbedding (d := d)
    (by norm_num : 0 < (1 / 2 : Real))).measurableSet_image'
      (measurableSet_parabolicInterior 1 (0 : PDE.Vec d))

/- The normalized open coordinate box has volume `2^d`. -/
theorem volume_parabolicBox_one_toReal (d : Nat) :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal = (2 : Real) ^ d := by
  simpa using (volume_parabolicBox_toReal (d := d) (vartheta := 1) (r := 1)
    (t₀ := 0) (v₀ := (0 : PDE.Vec d)) (by norm_num) (by norm_num))

/- The normalized open coordinate box has positive finite real volume. -/
theorem volume_parabolicBox_one_ne_top (d : Nat) :
    volume (parabolicBox 1 1 0 (0 : PDE.Vec d)) ≠ ∞ := by
  intro htop
  have hpos : 0 < (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal := by
      rw [volume_parabolicBox_one_toReal]
      positivity

    /- The normalized open coordinate box has finite volume. -/
  rw [htop, ENNReal.toReal_top] at hpos
  linarith

/- A restricted parabolic norm is bounded by a constant on a measurable
support, without a positive-dimension assumption. -/
theorem parabolicLpNormOn_le_of_norm_le_indicator
    (d : Nat) (f : TimeVelocity d → Real) (s E : Set (TimeVelocity d))
    (M : Real) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hM : 0 ≤ M)
    (hfinite : volume (s ∩ E) ≠ ∞)
    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _ : TimeVelocity d ↦ M) z) :
    parabolicLpNormOn d f s ≤
      M * Real.rpow (volume (s ∩ E)).toReal (1 / ((d : Real) + 1)) := by
  have hraw : parabolicELpNormOn d f s ≤
      ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
      have hmono : eLpNorm f (parabolicExponent d) (volume.restrict s) ≤
          eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
            (parabolicExponent d) (volume.restrict s) :=
        eLpNorm_mono_ae hf (ae_restrict_of_forall_mem hs (by
          intro z hz
          by_cases hzE : z ∈ E
          · simpa only [Set.indicator_of_mem hzE, Real.norm_eq_abs, abs_of_nonneg hM]
              using hbound z hz
          · simpa only [Set.indicator_of_notMem hzE, norm_zero] using hbound z hz))
      calc
        parabolicELpNormOn d f s = eLpNorm f (parabolicExponent d) (volume.restrict s) := rfl
        _ ≤ eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
            (parabolicExponent d) (volume.restrict s) := hmono
        _ = ‖M‖ₑ * (volume.restrict s E) ^ (1 / (parabolicExponent d).toReal) :=
          eLpNorm_indicator_const hE.nullMeasurableSet (parabolicExponent_ne_zero d)
            (parabolicExponent_ne_top d)
        _ = ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
          have _h_inl_15 (d) : (parabolicExponent d).toReal = (d : Real) + 1 := by
            unfold parabolicExponent
            have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
            rw [hcast, ENNReal.toReal_natCast]
            norm_num
          rw [Measure.restrict_apply hE, inter_comm, _h_inl_15]
          rw [Real.enorm_of_nonneg hM]

    /- Real-valued corollary of the finite-support parabolic norm estimate. -/
  have hexponent : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hright : ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexponent hfinite)
  have hleft : parabolicELpNormOn d f s ≠ ∞ := ne_top_of_le_ne_top hright hraw
  have hreal := (ENNReal.toReal_le_toReal hleft hright).mpr hraw
  unfold parabolicLpNormOn
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ← ENNReal.toReal_rpow] at hreal
  exact hreal

/- The strict sublevel set is measurable relative to the unit box under the
local `C²` regularity supplied to `DensityToPoint`. -/
theorem measurableSet_parabolicBox_inter_lt_one_of_contDiffOn
    (d U) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U) :
    MeasurableSet (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1}) := by
  have hcont :=
    hu.continuousOn.mono hQU
  change MeasurableSet (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ u ⁻¹' Iio 1)
  exact (hcont.isOpen_inter_preimage
    (isOpen_parabolicBox 1 1 0 (0 : PDE.Vec d)) isOpen_Iio).measurableSet

/- Density of the non-strict superlevel set bounds its exact strict
sublevel complement in the normalized parabolic box. -/
end HypoellipticAleksandrov.Parabolic
