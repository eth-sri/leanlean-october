module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ScalingMeasure

open private HypoellipticAleksandrov.Parabolic.parabolicExponent_toReal from HypoellipticAleksandrov.Parabolic.ScalingMeasure


/-!
# Restriction for normalized parabolic Morrey mean norms

This module proves the normalized restriction factor for arbitrary positive
finite time--velocity sets and specializes it to literal forward physical
parabolic boxes.  The real-valued statement remains guarded by the normalized
`MemLp` certificates required by the proof-indexed mean norm.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal




variable {d : Nat}

private theorem parabolicMorreyBox_volume_ratio_rpow_toReal

    (tᵦ : Real) (vᵦ : PDE.Vec d) {rᵦ : Real} (hrᵦ : 0 < rᵦ)
    (tₛ : Real) (vₛ : PDE.Vec d) {rₛ : Real} (hrₛ : 0 < rₛ) :
    ((volume (parabolicBox 1 rᵦ tᵦ vᵦ) /
        volume (parabolicBox 1 rₛ tₛ vₛ)) ^
      (1 / parabolicExponent d).toReal).toReal =
      (rᵦ / rₛ) ^ (((d : Real) + 2) / ((d : Real) + 1)) := by
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_div,
    volume_parabolicMorreyBox_toReal tᵦ vᵦ hrᵦ,
    volume_parabolicMorreyBox_toReal tₛ vₛ hrₛ]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_toReal]

  have hratio :
      ((2 : Real) ^ d * rᵦ ^ (d + 2)) /
          ((2 : Real) ^ d * rₛ ^ (d + 2)) =
        (rᵦ / rₛ) ^ (d + 2) := by
    rw [mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num)), (div_pow _ _ _).symm]
  rw [hratio, ← Real.rpow_natCast,
    ← Real.rpow_mul (div_nonneg hrᵦ.le hrₛ.le)]
  congr 1
  have hp : (d : Real) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hp]

/-- Restricting to a smaller positive finite set costs the normalized-volume
ratio to the power `1 / (d + 1)`. -/
theorem parabolicELpMeanNormOn_mono_set
     {Qₛ Qᵦ : HypoellipticAleksandrov.Parabolic.Region d}
    (_hₛpos : 0 < volume Qₛ) (hₛtop : volume Qₛ < ∞)
    (hᵦpos : 0 < volume Qᵦ) (hᵦtop : volume Qᵦ < ∞)
    (hsub : Qₛ ⊆ Qᵦ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    parabolicELpMeanNormOn d f Qₛ ≤
      (volume Qᵦ / volume Qₛ) ^ (1 / parabolicExponent d).toReal *
        parabolicELpMeanNormOn d f Qᵦ := by

  calc
    parabolicELpMeanNormOn d f Qₛ =
        (volume Qₛ)⁻¹ ^ (1 / parabolicExponent d).toReal *
          parabolicELpNormOn d f Qₛ :=
      parabolicELpMeanNormOn_eq_volume_inv_rpow_mul_parabolicELpNormOn hₛtop f
    _ ≤ (volume Qₛ)⁻¹ ^ (1 / parabolicExponent d).toReal *
          parabolicELpNormOn d f Qᵦ :=
      mul_le_mul_right (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hsub)) _
    _ = (volume Qᵦ / volume Qₛ) ^ (1 / parabolicExponent d).toReal *
          parabolicELpMeanNormOn d f Qᵦ := by
      rw [parabolicELpNormOn_eq_volume_rpow_mul_parabolicELpMeanNormOn
        hᵦpos hᵦtop f, ENNReal.inv_rpow,
        ENNReal.div_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
      simp only [div_eq_mul_inv]
      ac_rfl

variable (tᵦ : Real) (vᵦ : PDE.Vec d) {rᵦ : Real} (hrᵦ : 0 < rᵦ) (tₛ : Real) (vₛ : PDE.Vec d) {rₛ : Real} (hrₛ : 0 < rₛ) (hsub : parabolicBox 1 rₛ tₛ vₛ ⊆ parabolicBox 1 rᵦ tᵦ vᵦ)

include hrᵦ hrₛ hsub
/-- Normalized `MemLp` on a larger literal forward physical box restricts to
a contained smaller such box. -/
theorem memLp_parabolicNormalizedVolumeOn_mono_parabolicBox


    {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hᵦ : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 rᵦ tᵦ vᵦ))) :
    MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 rₛ tₛ vₛ)) := (memLp_parabolicNormalizedVolumeOn_of_memLp (volume_parabolicMorreyBox_pos tₛ vₛ hrₛ)
  (MemLp.mono_measure (Measure.restrict_mono_set volume hsub)
    (memLp_restrict_of_memLp_parabolicNormalizedVolumeOn (volume_parabolicMorreyBox_pos tᵦ vᵦ hrᵦ)
      (volume_parabolicMorreyBox_lt_top tᵦ vᵦ hrᵦ) hᵦ)))

/-- The guarded real normalized mean norm on a smaller contained forward box
is bounded by that on the larger box with the exact parabolic radius factor. -/
theorem parabolicLpMeanNormOn_mono_parabolicBox


    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hₛ : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 rₛ tₛ vₛ)))
    (hᵦ : MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 rᵦ tᵦ vᵦ))) :
    parabolicLpMeanNormOn d f _ hₛ ≤
      (rᵦ / rₛ) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d f _ hᵦ := (id
  (Eq.mp
    (congrArg (LE.le (parabolicELpMeanNormOn d f (parabolicBox 1 rₛ tₛ vₛ)).toReal)
      (Eq.trans ENNReal.toReal_mul
        (congrFun' (congrArg HMul.hMul (parabolicMorreyBox_volume_ratio_rpow_toReal tᵦ vᵦ hrᵦ tₛ vₛ hrₛ))
          (parabolicELpMeanNormOn d f (parabolicBox 1 rᵦ tᵦ vᵦ)).toReal)))
    (ENNReal.toReal_mono
      (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
          (ENNReal.div_ne_top (volume_parabolicMorreyBox_ne_top tᵦ vᵦ hrᵦ)
            (LT.lt.ne' (volume_parabolicMorreyBox_pos tₛ vₛ hrₛ))))
        (ne_of_lt (memLp_iff.mp hᵦ)))
      (parabolicELpMeanNormOn_mono_set (volume_parabolicMorreyBox_pos tₛ vₛ hrₛ)
        (volume_parabolicMorreyBox_lt_top tₛ vₛ hrₛ) (volume_parabolicMorreyBox_pos tᵦ vᵦ hrᵦ)
        (volume_parabolicMorreyBox_lt_top tᵦ vᵦ hrᵦ) hsub f))))

end HypoellipticAleksandrov.Parabolic
