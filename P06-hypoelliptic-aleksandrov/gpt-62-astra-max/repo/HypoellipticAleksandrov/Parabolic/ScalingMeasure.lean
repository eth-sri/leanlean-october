module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure scaling for parabolic affine maps

This module proves the determinant, Haar-measure, and restricted `L^(d + 1)`
change-of-variables formulas for the affine map which multiplies time by
`r^2` and every velocity coordinate by `r`.  The results are stated for the
literal product Lebesgue measure on `TimeVelocity d`; no density-to-point or
higher-level parabolic estimate is imported here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

section
variable (d : ℕ) (r : ℝ)

private theorem parabolicLinear_eq_prodMap :
    (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d) =
      LinearMap.prodMap ((r ^ 2) • LinearMap.id) (r • LinearMap.id) := by
  rfl

/-- The determinant of the parabolic linear scaling is `r^(d + 2)`. -/
theorem parabolicLinear_det :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ]
      TimeVelocity d) = r ^ (d + 2) := by
  rw [parabolicLinear_eq_prodMap, LinearMap.det_prodMap]
  simp_all <;> grind

end

section
variable {d : ℕ} {t₀ r : ℝ} {v₀ : PDE.Vec d} (hr : r ≠ 0)

include hr in
/-- A nonzero-radius parabolic affine map is injective. -/
theorem parabolicAffine_injective_of_ne_zero : Function.Injective (parabolicAffine t₀ v₀ r) := by
  intro z w hzw
  apply Prod.ext
  · have htime := congrArg Prod.fst hzw
    change t₀ + r ^ 2 * z.1 = t₀ + r ^ 2 * w.1 at htime
    grind
  · ext i
    have hvelocity := congrFun (congrArg Prod.snd hzw) i
    change v₀ i + r * z.2 i = v₀ i + r * w.2 i at hvelocity
    apply mul_left_cancel₀ hr
    linarith

include hr in
/-- A nonzero-radius parabolic affine map is a measurable embedding. -/
theorem parabolicAffine_measurableEmbedding_of_ne_zero :
    MeasurableEmbedding (parabolicAffine t₀ v₀ r) :=
  (contDiff_infty_parabolicAffine t₀ v₀ r).continuous.measurableEmbedding
    (parabolicAffine_injective_of_ne_zero hr)

/-- A positive-radius parabolic affine map is a measurable embedding. -/
theorem parabolicAffine_measurableEmbedding
    (hr : 0 < r) :
    MeasurableEmbedding (parabolicAffine t₀ v₀ r) :=
  parabolicAffine_measurableEmbedding_of_ne_zero hr.ne'

end

section
variable {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) {r : ℝ} (hr : 0 < r) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d))

include hr in
private theorem parabolicLinear_det_ne_zero :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ]
      TimeVelocity d) ≠ 0 := by
  rw [parabolicLinear_det]
  positivity

include hr in
/-- The pushforward of product Lebesgue volume by a positive-radius parabolic
affine map has the inverse determinant factor. -/
theorem map_volume_parabolicAffine :
    Measure.map (parabolicAffine t₀ v₀ r) (volume : Measure (TimeVelocity d)) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) • volume := by
  have hL_measurable : Measurable (parabolicLinear (d := d) r) :=
    (parabolicLinear (d := d) r).continuous_of_finiteDimensional.measurable
  have htranslation_measurable : Measurable (fun z : TimeVelocity d ↦ (t₀, v₀) + z) :=
    (continuous_const.add continuous_id).measurable
  let c := ENNReal.ofReal ((r ^ (d + 2))⁻¹)
  have hlinear :
      Measure.map (parabolicLinear (d := d) r) volume =
        c • volume := by
    change Measure.map
        ((parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d)) volume = c • volume
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (parabolicLinear_det_ne_zero hr)]
    rw [parabolicLinear_det, abs_inv, abs_of_pos (pow_pos hr _)]
  calc
    Measure.map (parabolicAffine t₀ v₀ r) volume =
        Measure.map (fun z : TimeVelocity d ↦ (t₀, v₀) + z)
          (Measure.map (parabolicLinear r) volume) := by
      rw [Measure.map_map htranslation_measurable hL_measurable]
      rfl
    _ = Measure.map (fun z : TimeVelocity d ↦ (t₀, v₀) + z) (c • volume) := by
      rw [hlinear]
    _ = c • Measure.map (fun z : TimeVelocity d ↦ (t₀, v₀) + z) volume := by
      rw [Measure.map_smul _ htranslation_measurable.aemeasurable]
    _ = c • volume := by
      aesop
    _ = ENNReal.ofReal ((r ^ (d + 2))⁻¹) • volume := rfl

include hr in
private theorem map_restrict_parabolicAffine :
    Measure.map (parabolicAffine t₀ v₀ r) ((volume : Measure (TimeVelocity d)).restrict s) =
      (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' s) := by
  calc
    Measure.map (parabolicAffine t₀ v₀ r) (volume.restrict s) =
        Measure.map (parabolicAffine t₀ v₀ r)
          (volume.restrict (parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' s))) := by
      rw [(preimage_image_eq _ (parabolicAffine_injective hr))]
    _ = (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' s) :=
      ((parabolicAffine_measurableEmbedding hr).restrict_map volume
        (parabolicAffine t₀ v₀ r '' s)).symm

include hr in
/-- The ENNReal restricted-norm pullback formula before its elementary real
power simplification.  It has no measurability or finiteness premise. -/
theorem parabolicELpNormOn_pullback_raw :
    parabolicELpNormOn d
        (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z)) s =
      ‖r ^ 2‖ₑ *
        (ENNReal.ofReal ((r ^ (d + 2))⁻¹) ^
          (1 / parabolicExponent d).toReal) *
        parabolicELpNormOn d f (parabolicAffine t₀ v₀ r '' s) := by
  let a := parabolicAffine t₀ v₀ r
  let p := parabolicExponent d
  let c := ENNReal.ofReal ((r ^ (d + 2))⁻¹)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (pow_pos hr _))
  have hembedding : MeasurableEmbedding a := parabolicAffine_measurableEmbedding hr
  change eLpNorm (r ^ 2 • (f ∘ a)) p (volume.restrict s) =
    ‖r ^ 2‖ₑ * (c ^ (1 / p).toReal) *
      eLpNorm f p (volume.restrict (a '' s))
  rw [eLpNorm_const_smul, ← hembedding.eLpNorm_map_measure,
    map_restrict_parabolicAffine t₀ v₀ hr s, map_volume_parabolicAffine t₀ v₀ hr,
    Measure.restrict_smul, eLpNorm_smul_measure_of_ne_zero hc]
  simp_all <;> grind

end

private theorem parabolicExponent_toReal (d : ℕ) :
    (parabolicExponent d).toReal = (d : ℝ) + 1 := by
  rfl

private theorem parabolic_norm_scaling_factor (d : ℕ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * ((r ^ (d + 2))⁻¹) ^ (1 / ((d : ℝ) + 1)) =
      r ^ ((d : ℝ) / ((d : ℝ) + 1)) := by
  have hp : d + 1 ≠ 0 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_neg hr.le]
  rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  congr 1
  push_cast
  field_simp [hp]
  ring

/-- Exact restricted `L^(d + 1)` scaling under positive-radius parabolic affine
pullback.  The `toReal` norm encoding makes the statement valid also when the
underlying extended norm is infinite. -/
theorem parabolicLpNormOn_pullback {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) {r : ℝ}
    (hr : 0 < r) (f : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) :
    parabolicLpNormOn d
        (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z)) s =
      r ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d f (parabolicAffine t₀ v₀ r '' s) := by
  have hraw := parabolicELpNormOn_pullback_raw t₀ v₀ hr f s
  unfold parabolicLpNormOn
  calc
    (parabolicELpNormOn d
        (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z)) s).toReal =
        ‖r ^ 2‖ₑ.toReal *
          (ENNReal.ofReal ((r ^ (d + 2))⁻¹)).toReal ^
            (1 / parabolicExponent d).toReal *
          (parabolicELpNormOn d f (parabolicAffine t₀ v₀ r '' s)).toReal := by
      rw [(congrArg ENNReal.toReal hraw), ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    _ = r ^ (d / ((d : ℝ) + 1)) *
          (parabolicELpNormOn d f (parabolicAffine t₀ v₀ r '' s)).toReal := by
      rw [Real.enorm_of_nonneg (sq_nonneg r), ENNReal.toReal_ofReal (sq_nonneg r),
        ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hr _).le),
        ENNReal.toReal_div, ENNReal.toReal_one,
        parabolicExponent_toReal, parabolic_norm_scaling_factor d hr]

end HypoellipticAleksandrov.Parabolic
