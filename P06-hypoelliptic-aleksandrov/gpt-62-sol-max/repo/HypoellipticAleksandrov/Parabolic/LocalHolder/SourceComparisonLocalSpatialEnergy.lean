module

import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff

public import HypoellipticAleksandrov.Parabolic.LocalCompactSupportIntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.Parabolic.SpatialPrincipalIntegrationByParts

/-! # Local spatial value-energy testing

The compact cutoff permits testing a C2 spatial slice by its own value. This is the
integration by parts used to control gradients independently of boundary derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set

/-- A single coefficient entry obeys the exact cutoff value-energy identity. -/
theorem integral_local_spatial_value_energy_entry {d : ℕ}
    (O : Set (PDE.Vec d)) (hO : IsOpen O) (i j : Fin d)
    (a q η : PDE.Vec d → ℝ) (ha : ContDiffOn ℝ 1 a O)
    (hq : ContDiffOn ℝ 2 q O) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hsub : tsupport η ⊆ O) :
    (∫ y in O, a y * spatialPartial j q y *
      (η y ^ 2 * spatialPartial i q y + 2 * η y * spatialPartial i η y * q y)) =
    -(∫ y in O, (spatialPartial i a y * spatialPartial j q y +
      a y * spatialPartial i (spatialPartial j q) y) * (q y * η y ^ 2)) := by
  have hq1 : ContDiffOn ℝ 1 q O := hq.of_le (by norm_num)
  have hη1 : ContDiffOn ℝ 1 η O := hη.contDiffOn.of_le (by simp)
  have hgrad : ContDiffOn ℝ 1 (spatialPartial j q) O :=
    ContDiffOn.spatialPartial hq hO j
  have hcut : ContDiffOn ℝ 1 (fun y => q y * η y ^ 2) O := hq1.mul (hη1.pow 2)
  obtain ⟨hpowc, hpows⟩ := cutoff_square_support hc
  have hcutc : HasCompactSupport (fun y => q y * η y ^ 2) := hpowc.mul_left
  have hcuts : tsupport (fun y => q y * η y ^ 2) ⊆ O :=
    tsupport_mul_subset_right.trans (hpows.trans hsub)
  have hibp := setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
    O hO i (fun y => a y * spatialPartial j q y) (fun y => q y * η y ^ 2)
    (ha.mul hgrad) hcut hcutc hcuts
  have hder (y : PDE.Vec d) (hy : y ∈ O) :
      spatialPartial i (fun x => q x * η x ^ 2) y =
        η y ^ 2 * spatialPartial i q y + 2 * η y * spatialPartial i η y * q y := by
    rw [_root_.HypoellipticAleksandrov.Parabolic.spatialPartial_mul hO i hq1 (hη1.pow 2) hy]
    have hpow : spatialPartial i (fun x => η x ^ 2) y =
        2 * η y * spatialPartial i η y := by
      change fderiv ℝ (fun x => η x ^ 2) y (PDE.basisVec i) = _
      rw [fderiv_fun_pow 2 ((hη1.contDiffAt (hO.mem_nhds hy)).differentiableAt
        (by norm_num))]
      simp only [Nat.reduceSub, pow_one, smul_apply, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat, spatialPartial]
    rw [hpow]
    ring
  calc
    _ = ∫ y in O, (a y * spatialPartial j q y) *
        spatialPartial i (fun x => q x * η x ^ 2) y := by
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      dsimp only
      rw [hder y hy]
    _ = _ := hibp.trans (by
      congr 1
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      dsimp only
      rw [_root_.HypoellipticAleksandrov.Parabolic.spatialPartial_mul hO i ha hgrad hy])

end HypoellipticAleksandrov.Parabolic.LocalHolder
