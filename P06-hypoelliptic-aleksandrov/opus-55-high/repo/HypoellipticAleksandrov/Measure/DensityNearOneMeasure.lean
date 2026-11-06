module

public import HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct

/-!
# Measure bookkeeping for the near-one density argument

This module proves the finite-support parabolic norm bound and the exact
strict-sublevel complement identity used by the near-one density-to-point
argument.  It has no coefficient, ABP, or density-to-point conclusion.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable (d : Nat) (rho : Real) (f : TimeVelocity d → Real) (s E : Set (TimeVelocity d)) (M : Real)



theorem parabolicExponent_toReal  :
    (parabolicExponent d).toReal = (d : Real) + 1 := by
  aesop

/-- The local open ABP cylinder is measurable. -/
theorem measurableSet_localABPInterior {d : Nat} (v0 : PDE.Vec d) :
    MeasurableSet (localABPInterior v0) := (parabolicAffine_measurableEmbedding (d := d)
    (by norm_num)).measurableSet_image'
      (measurableSet_parabolicInterior 1 _)

/-- The normalized open coordinate box has volume `2^d`. -/
theorem volume_parabolicBox_one_toReal  :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal = (2 : Real) ^ d := by
  simpa using (volume_parabolicBox_toReal (d := d) (vartheta := 1) (r := 1)
    (t₀ := 0) (v₀ := (0)) (by norm_num) (by norm_num))

/-- The normalized open coordinate box has positive finite real volume. -/
theorem volume_parabolicBox_one_toReal_pos  :
    0 < (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal := by
  rw [volume_parabolicBox_one_toReal]
  positivity

/-- The normalized open coordinate box has finite volume. -/
theorem volume_parabolicBox_one_ne_top  :
    volume (parabolicBox 1 1 0 (0 : PDE.Vec d)) ≠ ∞ := by
  intro htop
  have hpos := volume_parabolicBox_one_toReal_pos d
  simp_all

/-- A restricted parabolic norm is bounded by a constant on a measurable
support, without a positive-dimension assumption. -/
theorem parabolicELpNormOn_le_of_norm_le_indicator
     (hf : AEStronglyMeasurable f (volume.restrict s))
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _ : TimeVelocity d ↦ M) z) :
    parabolicELpNormOn d f s ≤
      ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
  have hmono : eLpNorm f _ _ ≤
      eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M)
        (parabolicExponent d) (volume.restrict s) :=
    eLpNorm_mono_ae hf (ae_restrict_of_forall_mem hs (by
      intro z hz
      by_cases hzE : z ∈ E
      · simpa only [Set.indicator_of_mem hzE, Real.norm_eq_abs, abs_of_nonneg hM]
          using hbound z hz
      · simpa only [Set.indicator_of_notMem hzE, norm_zero] using hbound z hz))
  calc
    parabolicELpNormOn d f s = eLpNorm f _ _ := rfl
    _ ≤ eLpNorm _
        _ _ := hmono
    _ = ‖M‖ₑ * (volume.restrict s E) ^ (1 / (parabolicExponent d).toReal) :=
      eLpNorm_indicator_const hE.nullMeasurableSet (parabolicExponent_ne_zero d)
        (parabolicExponent_ne_top d)
    _ = ENNReal.ofReal M * volume _ ^ (1 / ((d : Real) + 1)) := by
      rw [Measure.restrict_apply hE, inter_comm, parabolicExponent_toReal, Real.enorm_of_nonneg hM]

/-- Real-valued corollary of the finite-support parabolic norm estimate. -/
theorem parabolicLpNormOn_le_of_norm_le_indicator
     (hf : AEStronglyMeasurable f (volume.restrict s))
    (hs : MeasurableSet s) (hE : MeasurableSet E) (hM : 0 ≤ M)
    (hfinite : volume (s ∩ E) ≠ ∞)
    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _ : TimeVelocity d ↦ M) z) :
    parabolicLpNormOn d f s ≤
      M * Real.rpow (volume (s ∩ E)).toReal (1 / ((d : Real) + 1)) := by
  have hraw := parabolicELpNormOn_le_of_norm_le_indicator d f s E M hf hs hE hM hbound
  have hexponent : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hright : ENNReal.ofReal M * volume _ ^ (1 / ((d : Real) + 1)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexponent hfinite)
  have hleft : parabolicELpNormOn d f s ≠ ∞ := ne_top_of_le_ne_top hright hraw
  have hreal := (ENNReal.toReal_le_toReal hleft hright).mpr hraw
  rw [ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow] at hreal
  aesop

/-- The strict sublevel set is measurable relative to the unit box under the
local `C²` regularity supplied to `DensityToPoint`. -/
theorem measurableSet_parabolicBox_inter_lt_one_of_contDiffOn
     (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U) :
    MeasurableSet (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1}) := by
  have hcont : ContinuousOn u _ :=
    hu.continuousOn.mono hQU
  exact (hcont.isOpen_inter_preimage
    (isOpen_parabolicBox 1 1 0 _) isOpen_Iio).measurableSet

/-- Density of the non-strict superlevel set bounds its exact strict
sublevel complement in the normalized parabolic box. -/
theorem volume_parabolicBox_inter_lt_one_toReal_le_one_sub_mul
     (beta : Real) (U : Set (TimeVelocity d))
    (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hdensity : beta *
        (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal ≤
      (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | 1 ≤ u z})).toReal) :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal ≤
      (1 - beta) * (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal := by
  let Q : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  let L  := Q ∩ {z | u z < 1}
  let H  := Q ∩ {z | 1 ≤ u z}
  have hL : MeasurableSet L := measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu
  have hLsubset : L ⊆ Q := fun _ hz => hz.1
  have hinter  := inter_eq_right.mpr hLsubset
  have hdiff : Q \ L = H := by
    aesop
  have hdecomp : (volume L).toReal + (volume H).toReal = (volume Q).toReal := by
    simpa only [Measure.real, hinter, hdiff] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hL
        (volume_parabolicBox_one_ne_top d))
  linarith

private theorem weightedSource_nonneg {d : Nat} (rho : Real) (u : TimeVelocity d → Real)
    (z : TimeVelocity d) (hrho : 0 ≤ rho) :
    0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0) := by
  positivity

/-- The local weighted positive source is controlled by the strict low-set
volume, with no coefficient or ABP premise. -/
theorem parabolicLpNormOn_localABP_weighted_one_sub_le
     (hrho : 0 ≤ rho)
    (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hu_nonneg : IsNonnegativeOn u (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (v0 : PDE.Vec d) (hv0 : v0 ∈ velocityClosedCube 0 (1 / 2 : Real)) :
    parabolicLpNormOn d
        (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
        (localABPInterior v0) ≤
      rho * Real.exp (rho / 4) *
        Real.rpow (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal
          (1 / ((d : Real) + 1)) := by
  let Q : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  let E  := Q ∩ {z | u z < 1}
  let f  := fun z ↦
    Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0)
  have hM : 0 ≤ rho * Real.exp (rho / 4) := mul_nonneg hrho (Real.exp_pos _).le
  have hE : MeasurableSet E := measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu
  have hfinite : volume (localABPInterior v0 ∩ E) ≠ ∞ := by
    apply measure_ne_top_of_subset (show localABPInterior v0 ∩ E ⊆ Q by
      grind)
    exact volume_parabolicBox_one_ne_top d
  have hEfinite : volume E ≠ ∞ := by
    apply measure_ne_top_of_subset (show E ⊆ Q by
      grind)
    exact volume_parabolicBox_one_ne_top d
  have hbound : ∀ z ∈ localABPInterior v0, ‖f z‖ ≤
      E.indicator (fun _ : TimeVelocity d ↦ rho * Real.exp (rho / 4)) z := by
    rintro z ⟨w, hw, rfl⟩
    have hzQ : localABPAffine v0 w ∈ Q :=
      localABPInterior_subset_parabolicBox_one hv0 ⟨w, hw, rfl⟩
    by_cases hlow : u (localABPAffine v0 w) < 1
    · have hzE : localABPAffine v0 w ∈ E := ⟨hzQ, hlow⟩
      rw [Set.indicator_of_mem hzE]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (weightedSource_nonneg rho u (localABPAffine v0 w) hrho)]
      have hmax : max (1 - u (localABPAffine v0 w)) 0 ≤ 1 := by
        aesop
      rcases mem_parabolicInterior_iff.mp hw with ⟨hw0, hw1, hwv⟩
      have htimeMul : rho * w.1 ≤ rho * 1 :=
        mul_le_mul_of_nonneg_left hw1.le hrho
      have htime : rho * ((localABPAffine v0 w).1 - 3 / 4) ≤ rho / 4 := by
        dsimp only [localABPAffine, parabolicAffine]
        linarith
      calc
        Real.exp _ *
            (rho * max _ 0) ≤
            Real.exp _ * (rho * 1) := by
          gcongr
        _ ≤ Real.exp (rho / 4) * (rho * 1) := by
          gcongr
        _ = rho * Real.exp _ := by ring
    aesop
  have hnorm := parabolicLpNormOn_le_of_norm_le_indicator d f
    _ E _
    (show AEStronglyMeasurable f _ from
      (show ContinuousOn f _ from
        (by fun_prop : Continuous _).continuousOn.mul
          (continuousOn_const.mul
            ((continuousOn_const.sub (hu.continuousOn.mono
              ((localABPInterior_subset_parabolicBox_one hv0).trans hQU))).sup
                continuousOn_const))).aestronglyMeasurable
                  (measurableSet_localABPInterior v0))
    (measurableSet_localABPInterior v0) hE hM hfinite hbound
  calc
    parabolicLpNormOn d f _ ≤
        rho * Real.exp _ *
          Real.rpow _
            _ := hnorm
    _ ≤ rho * Real.exp _ *
          Real.rpow _ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow ENNReal.toReal_nonneg
        · exact ENNReal.toReal_mono hEfinite
            (measure_mono inter_subset_right)
        positivity
      omega
    _ = _ := rfl

/-- The exponential factor in the local ABP conclusion cancels exactly with
the weighted-source estimate. -/
theorem exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_one_sub_le
     (hrho : 0 ≤ rho)
    (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hu_nonneg : IsNonnegativeOn u (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (v0 : PDE.Vec d) (hv0 : v0 ∈ velocityClosedCube 0 (1 / 2 : Real)) :
    Real.exp (-rho / 4) *
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
      rho * Real.rpow (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal
        (1 / ((d : Real) + 1)) := by
  have h := parabolicLpNormOn_localABP_weighted_one_sub_le d rho hrho U u hQU hu
    hu_nonneg v0 hv0
  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    calc
      Real.exp _ * Real.exp _ =
          Real.exp _ := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by
        ring
      _ = 1 := Real.exp_zero
  calc
    Real.exp _ * parabolicLpNormOn d
        _
        _ ≤
        Real.exp _ *
          (rho * Real.exp _ *
            Real.rpow _
              _) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = rho * Real.rpow
        _
          _ := by
      grind

end HypoellipticAleksandrov.Parabolic
