module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Normalized norms on parabolic Morrey boxes

This file defines the normalized restricted `L^(d + 1)` norm on
`TimeVelocity d`.  It also records its elementary conversion to the raw
restricted norm and the positive finite volume of the literal forward boxes
used by the parabolic Morrey program.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

/-- Restricted volume, divided by the volume of the set. -/
def parabolicNormalizedVolumeOn {d : Nat}
    (Q : HypoellipticAleksandrov.Parabolic.Region d) : Measure (TimeVelocity d) :=
  (volume Q)⁻¹ • volume.restrict Q

variable (d : Nat) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (Q : HypoellipticAleksandrov.Parabolic.Region d)

/-- The authoritative normalized restricted `L^(d + 1)` norm in `ENNReal`. -/
def parabolicELpMeanNormOn  : ENNReal :=
  eLpNorm f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)

/-- The finite real presentation of the normalized restricted `L^(d + 1)` norm. -/
def parabolicLpMeanNormOn
    (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)) : Real :=
  let finiteNorm : {a : ENNReal // a ≠ ⊤} :=
    ⟨parabolicELpMeanNormOn d f Q, ne_of_lt <| (memLp_iff.mp hf)⟩
  finiteNorm.1.toReal

variable {d : Nat}

/-- The proof-indexed real mean norm is definitionally the finite `ENNReal` norm. -/
theorem parabolicLpMeanNormOn_eq_toReal
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (Q : HypoellipticAleksandrov.Parabolic.Region d)
    (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)) :
    parabolicLpMeanNormOn d f Q hf =
      (parabolicELpMeanNormOn d f Q).toReal := rfl

variable {Q : HypoellipticAleksandrov.Parabolic.Region d}

private theorem volume_smul_parabolicNormalizedVolumeOn_eq_restrict

    (hQpos : 0 < volume Q) (hQtop : volume Q < ∞) :
    volume Q • parabolicNormalizedVolumeOn Q = volume.restrict Q := by
  rw [parabolicNormalizedVolumeOn, smul_smul,
    ENNReal.mul_inv_cancel hQpos.ne' hQtop.ne, one_smul]

section
variable {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hQpos : 0 < volume Q)

include hQpos
/-- Raw restricted `L^(d + 1)` membership passes to normalized restricted volume. -/
theorem memLp_parabolicNormalizedVolumeOn_of_memLp

    (hf : MemLp f (parabolicExponent d) (volume.restrict Q)) :
    MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q) := by
  rw [parabolicNormalizedVolumeOn]
  exact hf.smul_measure (ENNReal.inv_ne_top.mpr hQpos.ne')

/-- Normalized restricted `L^(d + 1)` membership recovers raw restricted volume. -/
theorem memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
       (hQtop : volume Q < ∞)
    (hf : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)) :
    MemLp f (parabolicExponent d) (volume.restrict Q) := by
  rw [← volume_smul_parabolicNormalizedVolumeOn_eq_restrict hQpos hQtop]
  exact hf.smul_measure hQtop.ne
end


/-- The normalized extended norm is the inverse-volume power times the raw norm. -/
theorem parabolicELpMeanNormOn_eq_volume_inv_rpow_mul_parabolicELpNormOn
      (hQtop : volume Q < ∞)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    parabolicELpMeanNormOn d f Q =
      (volume Q)⁻¹ ^ (1 / parabolicExponent d).toReal *
        parabolicELpNormOn d f Q := by

  rw [parabolicELpMeanNormOn, parabolicNormalizedVolumeOn,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hQtop.ne)]
  rfl

section
variable (hQpos : 0 < volume Q) (hQtop : volume Q < ∞) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)

include hQpos hQtop
/-- The raw extended norm is the volume power times the normalized norm. -/
theorem parabolicELpNormOn_eq_volume_rpow_mul_parabolicELpMeanNormOn

     :
    parabolicELpNormOn d f Q =
      volume Q ^ (1 / parabolicExponent d).toReal *
        parabolicELpMeanNormOn d f Q := by
  calc
    parabolicELpNormOn d f Q =
        eLpNorm f (parabolicExponent d)
          (volume Q • parabolicNormalizedVolumeOn Q) := by
      rw [volume_smul_parabolicNormalizedVolumeOn_eq_restrict hQpos hQtop]
      rfl
    _ = volume Q ^ (1 / parabolicExponent d).toReal *
          parabolicELpMeanNormOn d f Q := by
      rw [eLpNorm_smul_measure_of_ne_zero hQpos.ne']
      rfl

/-- The guarded real mean norm is the inverse-volume power times the raw real norm. -/
theorem parabolicLpMeanNormOn_eq_volume_toReal_inv_rpow_mul_parabolicLpNormOn


    (hraw : MemLp f (parabolicExponent d) (volume.restrict Q))
    (hmean : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q)) :
    parabolicLpMeanNormOn d f Q hmean =
      ((volume Q).toReal)⁻¹ ^ (1 / parabolicExponent d).toReal *
        parabolicLpNormOn d f Q := by

  have hhmean : hmean = (memLp_parabolicNormalizedVolumeOn_of_memLp hQpos hraw) := Subsingleton.elim _ _
  subst hmean
  have hnorm := congrArg ENNReal.toReal
    (parabolicELpMeanNormOn_eq_volume_inv_rpow_mul_parabolicELpNormOn hQtop f)
  simpa only [parabolicLpMeanNormOn_eq_toReal, parabolicLpNormOn,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv] using hnorm
end


variable (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)

include hr
private theorem volume_parabolicMorreyBox_toReal_pos
      :
    0 < (volume (parabolicBox 1 r t₀ v₀)).toReal := by
  rw [volume_parabolicBox_toReal_eq_parabolicScaling (d := d)
    (vartheta := 1) (r := r) (t₀ := t₀) (v₀ := v₀) (by norm_num) hr.le]
  simp_all

/-- The literal forward physical box has volume `2^d r^(d + 2)`. -/
theorem volume_parabolicMorreyBox_toReal
      :
    (volume (parabolicBox 1 r t₀ v₀)).toReal =
      (2 : Real) ^ d * r ^ (d + 2) := by
  simpa only [one_mul] using
    (volume_parabolicBox_toReal_eq_parabolicScaling (d := d)
      (vartheta := 1) (r := r) (t₀ := t₀) (v₀ := v₀) (by norm_num) hr.le)

/-- Literal forward physical boxes have positive volume at positive radius. -/
theorem volume_parabolicMorreyBox_pos
      :
    0 < volume (parabolicBox 1 r t₀ v₀) :=
  (ENNReal.toReal_pos_iff.mp
    (volume_parabolicMorreyBox_toReal_pos t₀ v₀ hr)).1

/-- Literal forward physical boxes have finite volume at positive radius. -/
theorem volume_parabolicMorreyBox_lt_top
      :
    volume (parabolicBox 1 r t₀ v₀) < ∞ :=
  (ENNReal.toReal_pos_iff.mp
    (volume_parabolicMorreyBox_toReal_pos t₀ v₀ hr)).2

/-- Literal forward physical boxes have non-infinite volume at positive radius. -/
theorem volume_parabolicMorreyBox_ne_top
      :
    volume (parabolicBox 1 r t₀ v₀) ≠ ∞ :=
  ne_of_lt (volume_parabolicMorreyBox_lt_top t₀ v₀ hr)

end HypoellipticAleksandrov.Parabolic
