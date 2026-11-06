module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import HypoellipticAleksandrov.Measure.TimeVelocity
import HypoellipticAleksandrov.Parabolic.HarnackGeometry

/-!
# Restriction for normalized parabolic Morrey mean norms

This module proves the normalized restriction factor for arbitrary positive
finite time--velocity sets and specializes it to literal forward physical
parabolic boxes.  The real-valued statement remains guarded by the normalized
`MemLp` certificates required by the proof-indexed mean norm.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

theorem parabolicELpMeanNormOn_mono_set
    {d : Nat} {Qₛ Qᵦ : Set (TimeVelocity d)}
    (_hₛpos : 0 < volume Qₛ) (hₛtop : volume Qₛ < ∞)
    (hᵦpos : 0 < volume Qᵦ) (hᵦtop : volume Qᵦ < ∞)
    (hsub : Qₛ ⊆ Qᵦ) (f : TimeVelocity d -> Real) :
    parabolicELpMeanNormOn d f Qₛ ≤
      (volume Qᵦ / volume Qₛ) ^ (1 / parabolicExponent d).toReal *
        parabolicELpMeanNormOn d f Qᵦ := by
  have hraw : parabolicELpNormOn d f Qₛ ≤ parabolicELpNormOn d f Qᵦ := by
    exact eLpNorm_mono_measure f (Measure.restrict_mono_set volume hsub)
  calc
    parabolicELpMeanNormOn d f Qₛ =
        (volume Qₛ)⁻¹ ^ (1 / parabolicExponent d).toReal *
          parabolicELpNormOn d f Qₛ :=
      parabolicELpMeanNormOn_eq_volume_inv_rpow_mul_parabolicELpNormOn hₛtop f
    _ ≤ (volume Qₛ)⁻¹ ^ (1 / parabolicExponent d).toReal *
          parabolicELpNormOn d f Qᵦ :=
      mul_le_mul_right hraw _
    _ = (volume Qᵦ / volume Qₛ) ^ (1 / parabolicExponent d).toReal *
          parabolicELpMeanNormOn d f Qᵦ := by
      rw [parabolicELpNormOn_eq_volume_rpow_mul_parabolicELpMeanNormOn
        hᵦpos hᵦtop f, ENNReal.inv_rpow,
        ENNReal.div_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
      simp only [div_eq_mul_inv]
      ac_rfl

/- Normalized `MemLp` on a larger literal forward physical box restricts to
a contained smaller such box. -/
end HypoellipticAleksandrov.Parabolic
