module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointDecay
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyGeometry
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjectionClosed
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxResidualMean
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedTail

/-!
# Affine-modulo nearby-pair parabolic Morrey decay

This module combines the dyadic pointwise tail with a literal common nearby
forward box.  It does not assert a common dyadic address or a raw Holder bound.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

variable (d : Nat)


/-- At the dyadic scale comparable to two reference points, the smooth value
minus the canonical common forward-box affine projection has Morrey decay. -/
theorem exists_parabolicMorreyDyadicNearbyAffineModuloDecayConst
     (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (hz : z ∈ parabolicDyadicReferenceCell d)
        (w : TimeVelocity d)
        (hw : w ∈ parabolicDyadicReferenceCell d)
        (n : Nat),
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).radius ≤
            parabolicCoordinateDist z w →
        parabolicCoordinateDist z w <
          2 * (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).radius →
        ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
          HasCompactSupport u ->
          |(u z - parabolicMorreyBoxAffineProjection
              (min
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz n).2).baseTime
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d w hw n).2).baseTime)
              ((z.2 + w.2) / 2)
              (3 * parabolicCoordinateDist z w) u z) -
            (u w - parabolicMorreyBoxAffineProjection
              (min
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz n).2).baseTime
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d w hw n).2).baseTime)
              ((z.2 + w.2) / 2)
              (3 * parabolicCoordinateDist z w) u w)| ≤
            C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
              parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C_tail, hC_tail_pos, htail⟩ :=
    exists_parabolicMorreyDyadicContainingProjectionValueDecayConst d hd
  obtain ⟨C_P, hC_P_pos, hresidual⟩ :=
    exists_parabolicMorreyBoxAffineResidualMeanConst d hd
  let alpha  := parabolicMorreyExponent d
  let beta  := (d + 2) / ((d : Real) + 1)
  let geom  := (1 - (2 : Real) ^ (-alpha))⁻¹
  let K  := (1 + 3 * d) * 6 ^ beta * C_P *
    (2) ^ (-d / ((d : Real) + 1)) * 3 ^ alpha
  let C  := 2 * (C_tail * geom + K)
  have halpha_pos : 0 < alpha := by
    dsimp only [alpha, parabolicMorreyExponent]
    positivity
  have htwopow_lt_one : (2 : Real) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr halpha_pos)
  refine ⟨C, ?_, ?_⟩
  · positivity
  intro z hz w hw n hscale hscale_upper u hu huc
  let rho : Real := parabolicCoordinateDist z w
  let qz := parabolicDyadicSourceBox
    (parabolicDyadicAddressContaining d z hz n).2
  let qw := parabolicDyadicSourceBox
    (parabolicDyadicAddressContaining d w hw n).2
  let tMin : Real := min qz.baseTime qw.baseTime
  let vMid : PDE.Vec d := (z.2 + w.2) / 2
  have hqz_pos : 0 < qz.radius := parabolicDyadicSourceBox_radius_pos _
  have hrho_pos : 0 < rho := lt_of_lt_of_le hqz_pos hscale
  have hqw_radius : qz.radius = qw.radius := by
    rfl
  have hqw_pos : 0 < qw.radius := by simpa only [hqw_radius] using hqz_pos
  have hscale_w : qw.radius ≤ rho := by simpa only [qz, qw, rho] using! hscale
  have hscale_upper_w : rho < 2 * qw.radius := by
    simpa only [qz, qw, rho] using! hscale_upper
  have hbig_pos : 0 < 3 * rho := mul_pos (by norm_num) hrho_pos
  obtain ⟨hsub_z, hsub_w, -, -⟩ :=
    parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox d z hz w hw n hscale
  have hz_closed : z ∈ parabolicClosedBox 1 qz.radius qz.baseTime qz.center := parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n
  have hw_closed : w ∈ parabolicClosedBox 1 qw.radius qw.baseTime qw.center := parabolicDyadicAddressContaining_mem_closedForwardBox d w hw n
  obtain ⟨hres, hmean⟩ := hresidual tMin vMid (3 * rho) hbig_pos u hu huc
  have hratio_z : 3 * rho / qz.radius ≤ 6 := by
    apply (div_le_iff₀ hqz_pos).mpr
    nlinarith [hscale_upper]
  have hratio_w : 3 * rho / qw.radius ≤ 6 := by
    apply (div_le_iff₀ hqw_pos).mpr
    nlinarith [hscale_upper_w]
  have hD_nonneg : 0 ≤ parabolicMorreyDerivativeLpNorm d u :=
    parabolicMorreyDerivativeLpNorm_nonneg d u
  have hbig_rpow : (3 * rho) ^ alpha = 3 ^ alpha * rho ^ alpha := by
    rw [Real.mul_rpow (by norm_num) hrho_pos.le]
  have htail_z := htail z hz u hu huc n
  have htail_w := htail w hw u hu huc n
  have htail_z_bound :
      |u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z| ≤
        C_tail * geom * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
    calc
      |u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z| ≤
          C_tail * qz.radius ^ alpha * geom * parabolicMorreyDerivativeLpNorm d u := by
            simpa only [qz, alpha, geom] using htail_z
      _ ≤ C_tail * rho ^ alpha * geom * parabolicMorreyDerivativeLpNorm d u := by
            gcongr
      _ = C_tail * geom * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by ring
  have htail_w_bound :
      |u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w| ≤
        C_tail * geom * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
    calc
      |u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w| ≤
          C_tail * qw.radius ^ alpha * geom * parabolicMorreyDerivativeLpNorm d u := by
            simpa only [qw, alpha, geom] using htail_w
      _ ≤ C_tail * rho ^ alpha * geom * parabolicMorreyDerivativeLpNorm d u := by
            gcongr
      _ = C_tail * geom * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by ring
  have hcompare_z := parabolicMorreyNestedProjection_abs_sub_le_largeResidual_closed
    tMin vMid hbig_pos qz.baseTime qz.center hqz_pos hsub_z u z hz_closed hres
  have hcompare_w := parabolicMorreyNestedProjection_abs_sub_le_largeResidual_closed
    tMin vMid hbig_pos qw.baseTime qw.center hqw_pos hsub_w u w hw_closed hres
  have hmean_nonneg : 0 ≤ parabolicLpMeanNormOn d
      (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
      (parabolicBox 1 (3 * rho) tMin vMid) hres := ENNReal.toReal_nonneg
  have hnear_z :
      |parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
          parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z| ≤
        K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
    calc
      |parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
          parabolicMorreyBoxAffineProjection tMin vMid _ u z| ≤
          (1 + 3 * d) * (3 * rho / qz.radius) ^ beta *
            parabolicLpMeanNormOn d
              _
              _ hres := by
            simpa only [beta] using hcompare_z
      _ ≤ (1 + 3 * d) * 6 ^ beta *
            (C_P * (2) ^ (-d / ((d : Real) + 1)) *
              (3 * rho) ^ alpha * parabolicMorreyDerivativeLpNorm d u) := by
            gcongr
      _ = K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
            rw [hbig_rpow]
            ring
  have hnear_w :
      |parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
          parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w| ≤
        K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
    calc
      |parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
          parabolicMorreyBoxAffineProjection tMin vMid _ u w| ≤
          (1 + 3 * d) * (3 * rho / qw.radius) ^ beta *
            parabolicLpMeanNormOn d
              _
              _ hres := by
            simpa only [beta] using hcompare_w
      _ ≤ (1 + 3 * d) * 6 ^ beta *
            (C_P * (2) ^ (-d / ((d : Real) + 1)) *
              (3 * rho) ^ alpha * parabolicMorreyDerivativeLpNorm d u) := by
            gcongr
      _ = K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
            rw [hbig_rpow]
            ring
  calc
    |(u z - parabolicMorreyBoxAffineProjection tMin vMid _ u z) -
        (u w - parabolicMorreyBoxAffineProjection tMin vMid _ u w)| =
        |(u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z) +
          (parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
            parabolicMorreyBoxAffineProjection tMin vMid _ u z) -
          ((u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w) +
            (parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
              parabolicMorreyBoxAffineProjection tMin vMid _ u w))| := by
                congr 1
                ring
    _ ≤ |u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z| +
          |parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
            parabolicMorreyBoxAffineProjection tMin vMid _ u z| +
          (|u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w| +
            |parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
              parabolicMorreyBoxAffineProjection tMin vMid _ u w|) := by
        calc
          _ ≤ |(u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z) +
              (parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
                parabolicMorreyBoxAffineProjection tMin vMid _ u z)| +
              |(u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w) +
                (parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
                  parabolicMorreyBoxAffineProjection tMin vMid _ u w)| := by
                    simpa only [sub_zero, zero_sub, abs_neg] using
                      abs_sub_le
                        _
                        0
                        ((u w - parabolicMorreyBoxAffineProjection
                            qw.baseTime qw.center qw.radius u w) +
                          (parabolicMorreyBoxAffineProjection
                            qw.baseTime qw.center qw.radius u w -
                            parabolicMorreyBoxAffineProjection
                              tMin vMid _ u w))
          _ ≤ _ := add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ ≤ (C_tail * geom * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u) +
          (K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u) +
          ((C_tail * geom * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u) +
            (K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u)) :=
        add_le_add (add_le_add htail_z_bound hnear_z)
          (add_le_add htail_w_bound hnear_w)
    _ = 2 * (C_tail * geom + K) * rho ^ alpha *
          parabolicMorreyDerivativeLpNorm d u := by ring
    _ = C * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
        rfl
    _ = _ := by
        simp only [rho, alpha]

end HypoellipticAleksandrov.Parabolic
