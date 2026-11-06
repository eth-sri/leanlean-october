module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffine
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffineIncrement
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffineIncrement

open private HypoellipticAleksandrov.Parabolic.parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm from HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffineIncrement


/-!
# Reference-carrier parabolic Morrey Holder estimate

This module combines the affine-modulo nearby decay with the full-norm
anchoring of the common affine projection on the exact dyadic reference
carrier.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators




/-- Compactly supported smooth data satisfy the local parabolic Holder estimate
on the exact dyadic reference carrier. -/
theorem exists_parabolicMorreyReferenceHolderFullNormConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (_hz : z ∈ parabolicDyadicReferenceCell d)
        (w : TimeVelocity d)
        (_hw : w ∈ parabolicDyadicReferenceCell d),
        parabolicCoordinateDist z w <= 1 ->
        ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff Real 2 u ->
          HasCompactSupport u ->
          |u z - u w| <=
            C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
              parabolicSmoothJetLpNorm d u := by
  obtain ⟨C4, hC4_pos, hmodulo⟩ :=
    exists_parabolicMorreyDyadicNearbyAffineModuloDecayConst d hd
  obtain ⟨CI, hCI_pos, hincrement⟩ :=
    exists_parabolicMorreyDyadicNearbyAffineIncrementFullNormConst d hd
  refine ⟨C4 + CI, add_pos hC4_pos hCI_pos, ?_⟩
  intro z hz w hw hrho_one u hu huc
  by_cases hzw : z = w
  · subst w
    have hjet_nonneg : 0 <= parabolicSmoothJetLpNorm d u := ENNReal.toReal_nonneg
    have hpow_nonneg : 0 <=
        (parabolicCoordinateDist z z) ^ parabolicMorreyExponent d :=
      Real.rpow_nonneg (parabolicCoordinateDist_nonneg z z) _
    simpa only [sub_self, abs_zero] using
      mul_nonneg (mul_nonneg (add_pos hC4_pos hCI_pos).le hpow_nonneg) hjet_nonneg
  · obtain ⟨n, hn_lower, hn_upper⟩ :=
      exists_parabolicDyadicGeneration_radius_le_coordinateDist_lt_two_mul_radius
        d z hz w hw hzw
    let rho : Real := parabolicCoordinateDist z w
    let alpha : Real := parabolicMorreyExponent d
    let D : Real := parabolicMorreyDerivativeLpNorm d u
    let J : Real := parabolicSmoothJetLpNorm d u
    let P  := fun x =>
      parabolicMorreyBoxAffineProjection
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) (3 * parabolicCoordinateDist z w) u x
    have hmodulo_bound :
        |(u z - P z) - (u w - P w)| <= C4 * rho ^ alpha * D := by
      simpa only [P, rho, alpha, D] using
        hmodulo z hz w hw n hn_lower hn_upper u hu huc
    have hincrement_bound : |P z - P w| <= CI * rho ^ alpha * J := by
      exact hincrement z hz w hw n hn_lower hn_upper hrho_one u hu huc
    have hujet  :=
      parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
    have hderivative_le_jet : D <= J := by
      exact _root_.HypoellipticAleksandrov.Parabolic.parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm hujet
    have hrho_nonneg : 0 <= rho := by
      dsimp only [rho]
      exact parabolicCoordinateDist_nonneg z w
    have hC4rho_nonneg  :=
      mul_nonneg hC4_pos.le (Real.rpow_nonneg hrho_nonneg alpha)
    calc
      |u z - u w| = |((u z - P z) - (u w - P w)) + (P z - P w)| := by
        congr 1
        ring
      _ <= |(u z - P z) - (u w - P w)| + |P z - P w| := abs_add_le _ _
      _ <= C4 * rho ^ alpha * D + CI * rho ^ alpha * J :=
        add_le_add hmodulo_bound hincrement_bound
      _ <= C4 * rho ^ alpha * J + CI * rho ^ alpha * J :=
        add_le_add (mul_le_mul_of_nonneg_left hderivative_le_jet hC4rho_nonneg) le_rfl
      _ = (C4 + CI) * rho ^ alpha * J := by ring
      _ = _ := by rfl

end HypoellipticAleksandrov.Parabolic
