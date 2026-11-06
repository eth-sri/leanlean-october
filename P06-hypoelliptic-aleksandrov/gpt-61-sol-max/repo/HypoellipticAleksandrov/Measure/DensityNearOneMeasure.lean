module

public import HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import all HypoellipticAleksandrov.Parabolic.ScalingMeasure

open private HypoellipticAleksandrov.Parabolic.parabolicExponent_toReal from HypoellipticAleksandrov.Parabolic.ScalingMeasure


/-!
# Measure bookkeeping for the near-one density argument

This module proves the finite-support parabolic norm bound and the exact
strict-sublevel complement identity used by the near-one density-to-point
argument.  It has no coefficient, ABP, or density-to-point conclusion.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

variable (d : Nat)

private theorem parabolicExponent_ne_zero  : parabolicExponent d ≠ 0 := by
  simp [parabolicExponent]

private theorem parabolicExponent_ne_top  : parabolicExponent d ≠ ∞ := by
  simp [parabolicExponent]




/-- The local open ABP cylinder is measurable. -/
theorem measurableSet_localABPInterior {d : Nat} (v0 : PDE.Vec d) :
    MeasurableSet (localABPInterior v0) := by
  unfold localABPInterior localABPAffine
  exact (parabolicAffine_measurableEmbedding (d := d)
    (by norm_num : 0 < (1 / 2 : Real))).measurableSet_image'
      (measurableSet_parabolicInterior 1 (0 : PDE.Vec d))

variable (d : Nat)

/-- The normalized open coordinate box has volume `2^d`. -/
theorem volume_parabolicBox_one_toReal  :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal = (2 : Real) ^ d := by
  simpa using (volume_parabolicBox_toReal (d := d) (vartheta := 1) (r := 1)
    (t₀ := 0) (v₀ := (0 )) (by norm_num) (by norm_num))

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
  rw [htop, ENNReal.toReal_top] at hpos
  linarith

section
variable (f : TimeVelocity d → Real) (s E : HypoellipticAleksandrov.Parabolic.Region d) (M : Real) (hf : AEStronglyMeasurable f (volume.restrict s)) (hs : MeasurableSet s) (hE : MeasurableSet E) (hM : 0 ≤ M)

include hf hs hE hM
/-- A restricted parabolic norm is bounded by a constant on a measurable
support, without a positive-dimension assumption. -/
theorem parabolicELpNormOn_le_of_norm_le_indicator

    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _  ↦ M) z) :
    parabolicELpNormOn d f s ≤
      ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
  let sharedTerm_a05fe46c4b := (eLpNorm (E.indicator fun _ : TimeVelocity d ↦ M) (parabolicExponent d) (volume.restrict s))
  have hmono : eLpNorm f (parabolicExponent d) (volume.restrict s) ≤
      sharedTerm_a05fe46c4b :=
    eLpNorm_mono_ae hf (ae_restrict_of_forall_mem hs (by
      intro z hz
      by_cases hzE : z ∈ E
      · simpa only [Set.indicator_of_mem hzE, Real.norm_eq_abs, abs_of_nonneg hM]
          using hbound z hz
      · simpa only [Set.indicator_of_notMem hzE, norm_zero] using hbound z hz))
  calc
    parabolicELpNormOn d f s = eLpNorm f (parabolicExponent d) (volume.restrict s) := rfl
    _ ≤ sharedTerm_a05fe46c4b := hmono
    _ = ‖M‖ₑ * (volume.restrict s E) ^ (1 / (parabolicExponent d).toReal) :=
      eLpNorm_indicator_const hE.nullMeasurableSet (parabolicExponent_ne_zero d)
        (parabolicExponent_ne_top d)
    _ = ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) := by
      rw [Measure.restrict_apply hE, inter_comm, _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_toReal]
      rw [Real.enorm_of_nonneg hM]

/-- Real-valued corollary of the finite-support parabolic norm estimate. -/
theorem parabolicLpNormOn_le_of_norm_le_indicator

    (hfinite : volume (s ∩ E) ≠ ∞)
    (hbound : ∀ z ∈ s, ‖f z‖ ≤ E.indicator (fun _  ↦ M) z) :
    parabolicLpNormOn d f s ≤
      M * Real.rpow (volume (s ∩ E)).toReal (1 / ((d : Real) + 1)) := by
  have hraw := parabolicELpNormOn_le_of_norm_le_indicator d f s E M hf hs hE hM hbound

  have hright : ENNReal.ofReal M * volume (s ∩ E) ^ (1 / ((d : Real) + 1)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfinite)

  have hreal := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hright hraw) hright).mpr hraw
  unfold parabolicLpNormOn
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ← ENNReal.toReal_rpow] at hreal
  exact hreal
end


/-- The strict sublevel set is measurable relative to the unit box under the
local `C²` regularity supplied to `DensityToPoint`. -/
theorem measurableSet_parabolicBox_inter_lt_one_of_contDiffOn
     (U : HypoellipticAleksandrov.Parabolic.Region d) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U) :
    MeasurableSet (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1}) := (id
  (IsOpen.measurableSet
    (ContinuousOn.isOpen_inter_preimage (ContinuousOn.mono (ContDiffOn.continuousOn hu) hQU)
      (isOpen_parabolicBox 1 1 0 0) isOpen_Iio)))

/-- Density of the non-strict superlevel set bounds its exact strict
sublevel complement in the normalized parabolic box. -/
theorem volume_parabolicBox_inter_lt_one_toReal_le_one_sub_mul
     (beta : Real) (U : HypoellipticAleksandrov.Parabolic.Region d)
    (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hdensity : beta *
        (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal ≤
      (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | 1 ≤ u z})).toReal) :
    (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal ≤
      (1 - beta) * (volume (parabolicBox 1 1 0 (0 : PDE.Vec d))).toReal := by
  let Q : HypoellipticAleksandrov.Parabolic.Region d := parabolicBox 1 1 0 0
  let L  := Q ∩ {z | u z < 1}
  let H  := Q ∩ {z | 1 ≤ u z}
  have hL : MeasurableSet L := measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu
  have hLsubset : L ⊆ Q := fun _ hz => hz.1

  have hdiff : Q \ L = H := by
    ext z
    simp only [L, H, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · simp_all
    · simp_all
  have hdecomp : (volume L).toReal + (volume H).toReal = (volume Q).toReal := by
    simpa only [Measure.real, (inter_eq_right.mpr hLsubset), hdiff] using
      (measureReal_inter_add_diff (μ := volume) (s := Q) hL
        (volume_parabolicBox_one_ne_top d))
  linarith

private theorem weightedSource_nonneg {d : Nat} (rho : Real) (u : TimeVelocity d → Real)
    (z : TimeVelocity d) (hrho : 0 ≤ rho) :
    0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0) := by
  positivity

variable (d : Nat) (rho : Real) (hrho : 0 ≤ rho) (U : HypoellipticAleksandrov.Parabolic.Region d) (u : TimeVelocity d → Real) (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U) (hu : ContDiffOn Real 2 u U) (hu_nonneg : IsNonnegativeOn u (parabolicBox 1 1 0 (0 ))) (v0 : PDE.Vec d) (hv0 : v0 ∈ velocityClosedCube 0 (1 / 2 : Real))

include hrho hQU hu hu_nonneg hv0
/-- The local weighted positive source is controlled by the strict low-set
volume, with no coefficient or ABP premise. -/
theorem parabolicLpNormOn_localABP_weighted_one_sub_le
     :
    parabolicLpNormOn d
        (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
        (localABPInterior v0) ≤
      rho * Real.exp (rho / 4) *
        Real.rpow (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal
          (1 / ((d : Real) + 1)) := by
  let sharedTerm_5beec76251 := ((rho * Real.exp (rho / 4)))
  let sharedTerm_039be6c8d6 := ((1 / ((d : Real) + 1)))
  let Q : HypoellipticAleksandrov.Parabolic.Region d := parabolicBox 1 1 0 0
  let E  := Q ∩ {z | u z < 1}
  let f  := fun z ↦
    Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0)
  have hM : 0 ≤ sharedTerm_5beec76251 := mul_nonneg hrho (Real.exp_pos _).le


  have hEfinite : volume E ≠ ∞ := by
    apply measure_ne_top_of_subset (show E ⊆ Q by
      intro z hz
      exact hz.1)
    exact volume_parabolicBox_one_ne_top d

  have hnorm := parabolicLpNormOn_le_of_norm_le_indicator d f
    (localABPInterior v0) E sharedTerm_5beec76251
    (show AEStronglyMeasurable f (volume.restrict (localABPInterior v0)) from
      (show ContinuousOn f (localABPInterior v0) from
        (by fun_prop : Continuous (fun z : TimeVelocity d =>
          Real.exp (rho * (z.1 - 3 / 4)))).continuousOn.mul
          (continuousOn_const.mul
            ((continuousOn_const.sub (hu.continuousOn.mono
              ((localABPInterior_subset_parabolicBox_one hv0).trans hQU))).sup
                continuousOn_const))).aestronglyMeasurable
                  (measurableSet_localABPInterior v0))
    (measurableSet_localABPInterior v0) (measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu) hM (by
        apply measure_ne_top_of_subset (show localABPInterior v0 ∩ E ⊆ Q by
          intro z hz
          exact hz.2.1)
        exact volume_parabolicBox_one_ne_top d) (by
        rintro z ⟨w, hw, rfl⟩
        have hzQ : localABPAffine v0 w ∈ Q :=
          localABPInterior_subset_parabolicBox_one hv0 ⟨w, hw, rfl⟩
        by_cases hlow : u (localABPAffine v0 w) < 1
        ·
          rw [Set.indicator_of_mem (show localABPAffine v0 w ∈ E from ⟨hzQ, hlow⟩)]
          rw [Real.norm_eq_abs,
            abs_of_nonneg (weightedSource_nonneg rho u (localABPAffine v0 w) hrho)]
          have hmax : max (1 - u (localABPAffine v0 w)) 0 ≤ 1 := by
            apply max_le
            · linarith [hu_nonneg _ hzQ]
            · norm_num
          rcases mem_parabolicInterior_iff.mp hw with ⟨hw0, hw1, hwv⟩


          have hexp := Real.exp_le_exp.mpr (show rho * ((localABPAffine v0 w).1 - 3 / 4) ≤ rho / 4 by
              dsimp only [localABPAffine, parabolicAffine]
              nlinarith [(mul_le_mul_of_nonneg_left hw1.le hrho)])
          calc
            Real.exp (rho * ((localABPAffine v0 w).1 - 3 / 4)) *
                (rho * max (1 - u (localABPAffine v0 w)) 0) ≤
                Real.exp (rho * ((localABPAffine v0 w).1 - 3 / 4)) * (rho * 1) := by
              gcongr
            _ ≤ Real.exp (rho / 4) * (rho * 1) := by
              gcongr
            _ = sharedTerm_5beec76251 := by ring
        · rw [Set.indicator_of_notMem]
          · have hfzero : f (localABPAffine v0 w) = 0 := by
              dsimp only [f]
              rw [max_eq_right]
              · ring
              · exact sub_nonpos.mpr (le_of_not_gt hlow)
            rw [hfzero, norm_zero]
          · rintro ⟨_, hzlow⟩
            exact hlow hzlow)
  change parabolicLpNormOn d f (localABPInterior v0) ≤ _
  calc
    parabolicLpNormOn d f (localABPInterior v0) ≤
        sharedTerm_5beec76251 *
          Real.rpow (volume (localABPInterior v0 ∩ E)).toReal
            sharedTerm_039be6c8d6 := hnorm
    _ ≤ sharedTerm_5beec76251 *
          Real.rpow (volume E).toReal sharedTerm_039be6c8d6 := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow ENNReal.toReal_nonneg
        · gcongr <;> first | positivity | assumption | norm_num
        · positivity
      · exact hM
    _ = _ := rfl

/-- The exponential factor in the local ABP conclusion cancels exactly with
the weighted-source estimate. -/
theorem exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_one_sub_le
     :
    Real.exp (-rho / 4) *
        parabolicLpNormOn d
          (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
          (localABPInterior v0) ≤
      rho * Real.rpow (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal
        (1 / ((d : Real) + 1)) := by
  let sharedTerm_5ff77c29e6 := (Real.rpow (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal (1 / ((d : Real) + 1)))
  let sharedTerm_de9044b150 := (Real.exp (-rho / 4) * Real.exp (rho / 4))
  have h := parabolicLpNormOn_localABP_weighted_one_sub_le d rho hrho U u hQU hu
    hu_nonneg v0 hv0
  have hcancel : sharedTerm_de9044b150 = 1 := by
    calc
      sharedTerm_de9044b150 =
          Real.exp ((-rho / 4) + rho / 4) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := by
        congr 1
        ring
      _ = 1 := Real.exp_zero
  calc
    Real.exp (-rho / 4) * parabolicLpNormOn d
        (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
        (localABPInterior v0) ≤
        Real.exp (-rho / 4) *
          (rho * Real.exp (rho / 4) *
            sharedTerm_5ff77c29e6) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = rho * sharedTerm_5ff77c29e6 := by
      have hrearrange : Real.exp (-rho / 4) * (rho * Real.exp (rho / 4) *
          sharedTerm_5ff77c29e6) =
          rho * (sharedTerm_de9044b150) *
          sharedTerm_5ff77c29e6 := by
        ring
      rw [hrearrange]
      rw [hcancel]
      ring

end HypoellipticAleksandrov.Parabolic
