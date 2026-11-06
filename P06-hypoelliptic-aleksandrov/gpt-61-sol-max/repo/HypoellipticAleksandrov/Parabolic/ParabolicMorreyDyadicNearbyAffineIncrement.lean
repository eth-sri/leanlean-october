module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyGeometry
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjection
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxResidualMean
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicWeightedSlopeAnchor
import Mathlib.Tactic.NormNum



/-!
# Full-norm bound of a nearby affine increment

This module bounds the affine increment of the common nearby box by
the full compactly supported smooth-jet norm.  It uses a residual comparison,
the finite radius-weighted slope tail, and the root coefficient bound.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

private theorem parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicMorreyDerivativeLpNorm d u <= parabolicSmoothJetLpNorm d u := by
  let sharedTerm_7d5346f6d5 := (∑ i : Fin d, ∑ j : Fin d, (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal)
  let sharedTerm_45878e91f4 := ((parabolicELpNorm d (timeDerivative u)).toReal)
  let E  := parabolicELpNorm d (timeDerivative u) +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => velocityHessian u z i j)

  have hreal  :=
    ENNReal.toReal_mono (parabolicSmoothJetELpNorm_ne_top hu) (by
        dsimp only [E, parabolicSmoothJetELpNorm]
        calc
          parabolicELpNorm d (timeDerivative u) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicELpNorm d (fun z => velocityHessian u z i j) <=
              (parabolicELpNorm d u + parabolicELpNorm d (timeDerivative u) +
                ∑ i : Fin d, parabolicELpNorm d (fun z => velocityGradient u z i)) +
                  ∑ i : Fin d, ∑ j : Fin d,
                    parabolicELpNorm d (fun z => velocityHessian u z i j) := by
                  apply add_le_add_left
                  exact (self_le_add_left _ _).trans (self_le_add_right _ _)
          _ = _ := by ac_rfl)

  have htosum : (∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
      sharedTerm_7d5346f6d5 := by
    calc
      (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
          ∑ i : Fin d, (∑ j : Fin d,
            parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
              apply ENNReal.toReal_sum
              intro i _
              apply ENNReal.sum_ne_top.mpr
              intro j _
              exact (hu.2.2.2 i j).eLpNorm_ne_top
      _ = sharedTerm_7d5346f6d5 := by
            apply Finset.sum_congr rfl
            intro i _
            apply ENNReal.toReal_sum
            intro j _
            exact (hu.2.2.2 i j).eLpNorm_ne_top

  calc
    parabolicMorreyDerivativeLpNorm d u = E.toReal := (show E.toReal = parabolicMorreyDerivativeLpNorm d u by
        calc
          E.toReal = sharedTerm_45878e91f4 +
              (∑ i : Fin d, ∑ j : Fin d,
                parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := (by
                    apply ENNReal.toReal_add
                    · exact hu.2.1.eLpNorm_ne_top
                    · apply ENNReal.sum_ne_top.mpr
                      intro i _
                      apply ENNReal.sum_ne_top.mpr
                      intro j _
                      exact (hu.2.2.2 i j).eLpNorm_ne_top)
          _ = sharedTerm_45878e91f4 +
              sharedTerm_7d5346f6d5 := by rw [htosum]
          _ = parabolicMorreyDerivativeLpNorm d u := rfl).symm
    _ <= parabolicSmoothJetLpNorm d u := hreal

/-- The common nearby forward-box affine projection has an increment bounded by the full norm
 at reference-carrier scales at most one. -/
theorem exists_parabolicMorreyDyadicNearbyAffineIncrementFullNormConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (hz : z ∈ parabolicDyadicReferenceCell d)
        (w : TimeVelocity d)
        (hw : w ∈ parabolicDyadicReferenceCell d)
        (n : Nat),
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).radius <=
            parabolicCoordinateDist z w ->
        parabolicCoordinateDist z w <
          2 * (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).radius ->
        parabolicCoordinateDist z w <= 1 ->
        ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff Real 2 u ->
          HasCompactSupport u ->
          |parabolicMorreyBoxAffineProjection
              (min
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz n).2).baseTime
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d w hw n).2).baseTime)
              ((z.2 + w.2) / 2)
              (3 * parabolicCoordinateDist z w) u z -
            parabolicMorreyBoxAffineProjection
              (min
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz n).2).baseTime
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d w hw n).2).baseTime)
              ((z.2 + w.2) / 2)
              (3 * parabolicCoordinateDist z w) u w| <=
            C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
              parabolicSmoothJetLpNorm d u := by
  let sharedTerm_a27367f57e := (1 + 3 * (d : Real))
  let sharedTerm_e1c17b58a8 := ((2 : Real) ^ (-(d : Real) / ((d : Real) + 1)))
  obtain ⟨C_tail, hC_tail_pos, htail⟩ :=
    exists_parabolicMorreyDyadicContainingRadiusWeightedSlopeTailConst d hd
  obtain ⟨C_P, hC_P_pos, hresidual⟩ :=
    exists_parabolicMorreyBoxAffineResidualMeanConst d hd
  let alpha : Real := parabolicMorreyExponent d
  let beta : Real := ((d : Real) + 2) / ((d : Real) + 1)
  let q : Real := (2 : Real) ^ (-(1 - alpha))
  let geom : Real := (1 - q)⁻¹
  let K_compare : Real := 2 * (sharedTerm_a27367f57e) * 6 ^ beta * C_P *
    sharedTerm_e1c17b58a8 * 3 ^ alpha
  let K_tail : Real := 2 * C_tail * geom
  let K_root : Real := sharedTerm_a27367f57e
  let C : Real := K_compare + K_tail + K_root

  have halpha_le_one : alpha <= 1 := by
    dsimp only [alpha, parabolicMorreyExponent]

    apply (div_le_iff₀ (by positivity)).mpr
    linarith

  have hq_pos : 0 < q := by
    dsimp only [q]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hq_lt_one : q < 1 := by
    dsimp only [q]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have halpha_lt_one : alpha < 1 := by
      dsimp only [alpha, parabolicMorreyExponent]

      apply (div_lt_iff₀ (by positivity)).mpr
      have hlt : (d : Real) < (d : Real) + 1 := by
        linarith
      simpa only [one_mul] using hlt
    linarith




  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro z hz w hw n hscale hscale_upper hrho_one u hu huc
  let rho : Real := parabolicCoordinateDist z w
  let qz := parabolicDyadicSourceBox
    (parabolicDyadicAddressContaining d z hz n).2
  let qw := parabolicDyadicSourceBox
    (parabolicDyadicAddressContaining d w hw n).2
  let tMin : Real := min qz.baseTime qw.baseTime
  let vMid  := (z.2 + w.2) / 2
  let D : Real := parabolicMorreyDerivativeLpNorm d u
  let J : Real := parabolicSmoothJetLpNorm d u
  have hqz_pos : 0 < qz.radius := by
    dsimp only [qz]
    exact parabolicDyadicSourceBox_radius_pos _
  have hrho_pos : 0 < rho := by
    dsimp only [rho]
    exact lt_of_lt_of_le hqz_pos hscale

  have hrho_lt_two_qz : rho < 2 * qz.radius := by
    exact hscale_upper
  have hbig_pos : 0 < 3 * rho := mul_pos (by norm_num) hrho_pos


  have hratio_rpow  :=
    Real.rpow_le_rpow ((div_pos (mul_pos (by norm_num) hrho_pos) hqz_pos).le) (show 3 * rho / qz.radius <= 6 by
        apply (div_le_iff₀ hqz_pos).mpr
        nlinarith [hrho_lt_two_qz]) (show 0 < beta by
        dsimp only [beta]
        positivity).le
  have hD_nonneg : 0 <= D := by
    dsimp only [D, parabolicMorreyDerivativeLpNorm, parabolicLpNorm,
      parabolicELpNorm]
    exact add_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

  have hbig_rpow : (3 * rho) ^ alpha = 3 ^ alpha * rho ^ alpha := by
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 3) hrho_pos.le]
  obtain ⟨hsub_z, -, -, -⟩ :=
    parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox d z hz w hw n hscale
  obtain ⟨hres, hmean⟩ := hresidual tMin vMid (3 * rho) hbig_pos u hu huc
  have hmean_nonneg : 0 <= parabolicLpMeanNormOn d
      (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
      _ hres := by
    rw [parabolicLpMeanNormOn_eq_toReal]
    exact ENNReal.toReal_nonneg
  have hdisc := parabolicMorreyNestedProjection_discrepancy_le_largeResidual
    tMin vMid hbig_pos qz.baseTime qz.center hqz_pos hsub_z u hres
  have hslope_disc : qz.radius * ∑ i : Fin d,
      |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
        parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| <=
      (sharedTerm_a27367f57e) * (3 * rho / qz.radius) ^ beta *
        parabolicLpMeanNormOn d
          (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
          _ hres := by
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans hdisc


  have htail_raw := htail z hz u hu huc n

  have hroot_box_radius :
      (parabolicDyadicSourceBox
        (parabolicDyadicAddressContaining d z hz 0).2).radius = 1 := by
    change ((2 : Real) ^ 0)⁻¹ = 1
    norm_num
  have hroot_box_time :
      (parabolicDyadicSourceBox
        (parabolicDyadicAddressContaining d z hz 0).2).baseTime = 0 := by
    change (parabolicDyadicTimeCode 0
      (parabolicDyadicAddressContaining d z hz 0).2 : Real) / (4 : Real) ^ 0 = 0
    simp only [parabolicDyadicTimeCode, Nat.cast_zero, zero_div, pow_zero]
  have hroot_box_center :
      (parabolicDyadicSourceBox
        (parabolicDyadicAddressContaining d z hz 0).2).center = 0 := by
    funext i
    change -1 + 2 *
      (parabolicDyadicVelocityCode 0
        (parabolicDyadicAddressContaining d z hz 0).2 i : Real) / (2 : Real) ^ 0 +
        ((2 : Real) ^ 0)⁻¹ = 0
    norm_num [parabolicDyadicVelocityCode]







  have hD_le_J : D <= J := by
    dsimp only [D, J]
    exact parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm (parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc)
  calc
    |parabolicMorreyBoxAffineProjection
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) (3 * parabolicCoordinateDist z w) u z -
      parabolicMorreyBoxAffineProjection
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) (3 * parabolicCoordinateDist z w) u w| <=
        rho * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| := (by
            have hvelocity (i : Fin d) : |z.2 i - w.2 i| <= rho := by

              have hcoordinate := (pi_norm_le_iff_of_nonneg hrho_pos.le).mp (by
                  dsimp only [rho, parabolicCoordinateDist]
                  exact le_max_right _ _) i
              exact hcoordinate
            rw [parabolicMorreyBoxAffineProjection, parabolicMorreyBoxAffineProjection]
            calc
              |(parabolicMorreyBoxAverage tMin vMid (3 * rho) u +
                  ∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                    (z.2 i - vMid i)) -
                  (parabolicMorreyBoxAverage tMin vMid (3 * rho) u +
                    ∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                      (w.2 i - vMid i))| =
                  |∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                    (z.2 i - w.2 i)| := by
                      let sharedTerm_3e2e2c7962 := (∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i * (z.2 i - vMid i))
                      let sharedTerm_c7cda5ecb0 := (∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i * (w.2 i - vMid i))
                      congr 1
                      calc
                        parabolicMorreyBoxAverage tMin vMid (3 * rho) u +
                            sharedTerm_3e2e2c7962 -
                            (parabolicMorreyBoxAverage tMin vMid (3 * rho) u +
                              sharedTerm_c7cda5ecb0) =
                            (sharedTerm_3e2e2c7962) -
                            sharedTerm_c7cda5ecb0 := by ring
                        _ = ∑ i : Fin d,
                            (parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                              (z.2 i - vMid i) -
                            parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                              (w.2 i - vMid i)) := by
                              rw [← Finset.sum_sub_distrib]
                        _ = _ := by
                              apply Finset.sum_congr rfl
                              intro i _
                              ring
              _ <= ∑ i : Fin d,
                  |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                    (z.2 i - w.2 i)| := Finset.abs_sum_le_sum_abs _ Finset.univ
              _ = ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| *
                  |z.2 i - w.2 i| := by
                    norm_num
              _ <= ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| * rho :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (hvelocity i) (abs_nonneg _)
              _ = rho * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| := by
                rw [Finset.mul_sum]
                ring_nf)
    _ <= (K_compare + K_tail) * rho ^ alpha * D + K_root * rho ^ alpha * J := (by
        let sharedTerm_7b4b7ad98e := ((parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2))

        calc
          rho * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| <=
              rho * (∑ i : Fin d,
                |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i -
                  parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i| +
                ∑ i : Fin d,
                  |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
                    parabolicMorreyBoxVelocitySlope
                      (parabolicDyadicSourceBox
                        (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                      (parabolicDyadicSourceBox
                        (parabolicDyadicAddressContaining d z hz 0).2).center
                      (parabolicDyadicSourceBox
                        (parabolicDyadicAddressContaining d z hz 0).2).radius u i| +
                ∑ i : Fin d,
                  |parabolicMorreyBoxVelocitySlope
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).center
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).radius u i|) :=
            mul_le_mul_of_nonneg_left (by
                rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                refine Finset.sum_le_sum fun i _ => ?_
                let a := parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i -
                  parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i
                let b := parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
                  parabolicMorreyBoxVelocitySlope
                    sharedTerm_7b4b7ad98e.baseTime
                    sharedTerm_7b4b7ad98e.center
                    sharedTerm_7b4b7ad98e.radius u i
                let c := parabolicMorreyBoxVelocitySlope
                  sharedTerm_7b4b7ad98e.baseTime
                  sharedTerm_7b4b7ad98e.center
                  sharedTerm_7b4b7ad98e.radius u i

                calc
                  |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| = |a + b + c| :=
                    congrArg abs (show a + b + c =
                    parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i by
                        dsimp only [a, b, c]
                        ring).symm
                  _ <= |a + b| + |c| := abs_add_le _ _
                  _ <= (|a| + |b|) + |c| := add_le_add_left (abs_add_le _ _) _
                  _ = |a| + |b| + |c| := by ring
                  _ = _ := rfl) hrho_pos.le
          _ = (rho * ∑ i : Fin d,
              |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i -
                parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i|) +
              (rho * ∑ i : Fin d,
                |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
                  parabolicMorreyBoxVelocitySlope
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).center
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).radius u i|) +
                rho * ∑ i : Fin d,
                  |parabolicMorreyBoxVelocitySlope
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).center
                    (parabolicDyadicSourceBox
                      (parabolicDyadicAddressContaining d z hz 0).2).radius u i| := by ring
          _ <= K_compare * rho ^ alpha * D + K_tail * rho ^ alpha * D +
              K_root * rho ^ alpha * J :=
            add_le_add (add_le_add (by
                calc
                  rho * ∑ i : Fin d,
                      |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i -
                        parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i| =
                      (rho / qz.radius) *
                        (qz.radius * ∑ i : Fin d,
                          |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
                            parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i|) := by
                          simp_rw [abs_sub_comm]
                          field_simp [hqz_pos.ne']
                  _ <= 2 * ((sharedTerm_a27367f57e) * (3 * rho / qz.radius) ^ beta *
                      parabolicLpMeanNormOn d
                        (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
                        _ hres) := by
                          gcongr
                          · apply (div_le_iff₀ hqz_pos).mpr
                            linarith
                  _ <= 2 * ((sharedTerm_a27367f57e) * 6 ^ beta *
                      (C_P * sharedTerm_e1c17b58a8 *
                        (3 * rho) ^ alpha * D)) := by
                          gcongr
                  _ = K_compare * rho ^ alpha * D := by
                    rw [hbig_rpow]
                    dsimp only [K_compare]
                    ring) (by
                have hrpow  :=
                  Real.rpow_le_rpow hqz_pos.le (by exact hscale) (show 0 < alpha by
                      dsimp only [alpha, parabolicMorreyExponent]

                      positivity).le
                calc
                  rho * ∑ i : Fin d,
                      |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
                        parabolicMorreyBoxVelocitySlope
                          (parabolicDyadicSourceBox
                            (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                          (parabolicDyadicSourceBox
                            (parabolicDyadicAddressContaining d z hz 0).2).center
                          (parabolicDyadicSourceBox
                            (parabolicDyadicAddressContaining d z hz 0).2).radius u i| =
                      (rho / qz.radius) *
                        (qz.radius * ∑ i : Fin d,
                          |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
                            parabolicMorreyBoxVelocitySlope
                              (parabolicDyadicSourceBox
                                (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                              (parabolicDyadicSourceBox
                                (parabolicDyadicAddressContaining d z hz 0).2).center
                              (parabolicDyadicSourceBox
                                (parabolicDyadicAddressContaining d z hz 0).2).radius u i|) := by
                          field_simp [hqz_pos.ne']
                  _ <= 2 * (C_tail * qz.radius ^ alpha *
                      (∑ k ∈ Finset.range n, q ^ k) * D) := by
                        gcongr
                        apply (div_le_iff₀ hqz_pos).mpr
                        linarith
                  _ <= 2 * (C_tail * rho ^ alpha * geom * D) := by
                        gcongr
                        exact (show ∀ N : Nat, (∑ k ∈ Finset.range N, q ^ k) <= geom by
                            intro N
                            have hclear : (∑ k ∈ Finset.range N, q ^ k) * (1 - q) = 1 - q ^ N := by
                              calc
                                (∑ k ∈ Finset.range N, q ^ k) * (1 - q) =
                                    -((∑ k ∈ Finset.range N, q ^ k) * (q - 1)) := by ring
                                _ = -(q ^ N - 1) := by rw [geom_sum_mul]
                                _ = 1 - q ^ N := by ring
                            dsimp only [geom]
                            rw [inv_eq_one_div]
                            apply (le_div_iff₀ (sub_pos.mpr hq_lt_one)).mpr
                            rw [hclear]
                            linarith [pow_nonneg hq_pos.le N]) n
                  _ = K_tail * rho ^ alpha * D := by
                        dsimp only [K_tail]
                        ring)) (by
                calc
                  rho * ∑ i : Fin d,
                      |parabolicMorreyBoxVelocitySlope
                        (parabolicDyadicSourceBox
                          (parabolicDyadicAddressContaining d z hz 0).2).baseTime
                        (parabolicDyadicSourceBox
                          (parabolicDyadicAddressContaining d z hz 0).2).center
                        (parabolicDyadicSourceBox
                          (parabolicDyadicAddressContaining d z hz 0).2).radius u i| <=
                      rho * (K_root * J) := mul_le_mul_of_nonneg_left (by
                          simpa only [hroot_box_radius, hroot_box_time, hroot_box_center, K_root, J] using
                            (le_add_of_nonneg_left (abs_nonneg _)).trans (parabolicMorreyRootAffineCoefficient_le_parabolicSmoothJetLpNorm d u hu huc)) hrho_pos.le
                  _ <= rho ^ alpha * (K_root * J) :=
                    mul_le_mul_of_nonneg_right (by
                        simpa only [Real.rpow_one] using
                          (Real.rpow_le_rpow_of_exponent_ge hrho_pos hrho_one halpha_le_one))
                      (mul_nonneg (show 0 < K_root by
                          dsimp only [K_root]
                          positivity).le (by
                          dsimp only [J, parabolicSmoothJetLpNorm]
                          exact ENNReal.toReal_nonneg))
                  _ = K_root * rho ^ alpha * J := by ring)
          _ = (K_compare + K_tail) * rho ^ alpha * D + K_root * rho ^ alpha * J := by ring)
    _ <= (K_compare + K_tail) * rho ^ alpha * J + K_root * rho ^ alpha * J := by
      gcongr
    _ = C * rho ^ alpha * J := by
      dsimp only [C]
      ring
    _ = C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
        parabolicSmoothJetLpNorm d u := rfl

end HypoellipticAleksandrov.Parabolic
