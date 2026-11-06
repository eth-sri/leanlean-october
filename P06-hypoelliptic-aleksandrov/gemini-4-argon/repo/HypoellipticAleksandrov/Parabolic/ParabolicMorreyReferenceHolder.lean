module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffine
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffineIncrement
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxCoefficientBound
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxResidualMean
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedTail
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyGeometry
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointDecay
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointSelector
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyGeometry
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjectionClosed
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionRecovery
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicWeightedSlopeAnchor
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjection

/-!
# Reference-carrier parabolic Morrey Holder estimate

This module combines the affine-modulo nearby decay with the full-norm
anchoring of the common affine projection on the exact dyadic reference
carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators ENNReal
open MeasureTheory Set Filter
open scoped Topology

private theorem parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicMorreyDerivativeLpNorm d u <= parabolicSmoothJetLpNorm d u := by
  let E : ENNReal := parabolicELpNorm d (timeDerivative u) +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => velocityHessian u z i j)
  have hE : E <= parabolicSmoothJetELpNorm d u := by
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
      _ = _ := by ac_rfl
  have hreal :=
    ENNReal.toReal_mono (parabolicSmoothJetELpNorm_ne_top hu) hE
  have htoadd : E.toReal = (parabolicELpNorm d (timeDerivative u)).toReal +
      (∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
    apply ENNReal.toReal_add
    · exact hu.2.1.eLpNorm_ne_top
    · apply ENNReal.sum_ne_top.mpr
      intro i _
      apply ENNReal.sum_ne_top.mpr
      intro j _
      exact (hu.2.2.2 i j).eLpNorm_ne_top
  have htosum : (∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
      ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
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
      _ = ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
            apply Finset.sum_congr rfl
            intro i _
            apply ENNReal.toReal_sum
            intro j _
            exact (hu.2.2.2 i j).eLpNorm_ne_top
  have hleft : E.toReal = parabolicMorreyDerivativeLpNorm d u := by
    calc
      E.toReal = (parabolicELpNorm d (timeDerivative u)).toReal +
          (∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := htoadd
      _ = (parabolicELpNorm d (timeDerivative u)).toReal +
          ∑ i : Fin d, ∑ j : Fin d,
            (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
              rw [htosum]
      _ = parabolicMorreyDerivativeLpNorm d u := rfl
  calc
    parabolicMorreyDerivativeLpNorm d u = E.toReal := hleft.symm
    _ <= parabolicSmoothJetLpNorm d u := hreal

/- Compactly supported smooth data satisfy the local parabolic Holder estimate
on the exact dyadic reference carrier. -/
theorem exists_parabolicMorreyReferenceHolderFullNormConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (_hz : z ∈ parabolicDyadicReferenceCell d)
        (w : TimeVelocity d)
        (_hw : w ∈ parabolicDyadicReferenceCell d),
        parabolicCoordinateDist z w <= 1 ->
        ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
          HasCompactSupport u ->
          |u z - u w| <=
            C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
              parabolicSmoothJetLpNorm d u := by
  obtain ⟨C4, hC4_pos, hmodulo⟩ : ∃ C : Real, 0 < C ∧
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
    obtain ⟨C_tail, hC_tail_pos, htail⟩ : ∃ C : Real, 0 < C ∧
        ∀ (z : TimeVelocity d)
          (hz : z ∈ parabolicDyadicReferenceCell d)
          (u : TimeVelocity d -> Real),
          ContDiff Real 2 u ->
          HasCompactSupport u ->
          ∀ m : Nat,
            |u z -
                parabolicMorreyBoxAffineProjection
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz m).2).baseTime
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz m).2).center
                  (parabolicDyadicSourceBox
                    (parabolicDyadicAddressContaining d z hz m).2).radius
                  u z| <=
              C *
                (parabolicDyadicSourceBox
                  (parabolicDyadicAddressContaining d z hz m).2).radius ^
                  parabolicMorreyExponent d *
                (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ *
                parabolicMorreyDerivativeLpNorm d u := by
      obtain ⟨C, hCpos, htail⟩ :=
        exists_parabolicMorreyDyadicAddressPrefixProjectionClosedTailConst d hd
      refine ⟨C, hCpos, ?_⟩
      intro z hz u hu huc m
      let A : Nat -> ParabolicDyadicAddress d :=
        fun n => parabolicDyadicAddressContaining d z hz n
      let P : Nat -> Real := fun n =>
        parabolicMorreyBoxAffineProjection
          (parabolicDyadicSourceBox (A n).2).baseTime
          (parabolicDyadicSourceBox (A n).2).center
          (parabolicDyadicSourceBox (A n).2).radius u z
      let R : Real :=
        C * (parabolicDyadicSourceBox (A m).2).radius ^ parabolicMorreyExponent d *
          (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ *
          parabolicMorreyDerivativeLpNorm d u
      have hfinite : ∀ᶠ n in atTop, |P n - P m| <= R := by
        refine Filter.eventually_atTop.2 ⟨m, fun n hmn => ?_⟩
        exact htail (A m) (A n) u
          (parabolicDyadicAddressContaining_prefix d z hz hmn) hu huc z
          (by
            simpa only [A, parabolicDyadicAddressContaining] using
              parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n)
      have hradius : Tendsto (fun n =>
          (parabolicDyadicSourceBox (A n).2).radius) atTop (nhds 0) := by
        have htwo := tendsto_two_mul_parabolicDyadicIndexContaining_radius_atTop d z hz
        have hscale := htwo.const_mul ((2 : Real)⁻¹)
        rw [show (fun n => (parabolicDyadicSourceBox (A n).2).radius) =
            fun n => (2 : Real)⁻¹ *
              (2 * (parabolicDyadicSourceBox
                (parabolicDyadicIndexContaining d z hz n)).radius) by
          funext n
          dsimp only [A, parabolicDyadicAddressContaining]
          ring]
        simpa only [mul_zero] using hscale
      have hprojection : Tendsto P atTop (nhds (u z)) := by
        dsimp only [P]
        let t := (fun n => (parabolicDyadicSourceBox (A n).2).baseTime)
        let v := (fun n => (parabolicDyadicSourceBox (A n).2).center)
        let r := (fun n => (parabolicDyadicSourceBox (A n).2).radius)
        have hr := (fun n => parabolicDyadicSourceBox_radius_pos (A n).2)
        have hz := (fun n => by
            simpa only [A, parabolicDyadicAddressContaining] using
              parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n)
        exact tendsto_parabolicMorreyBoxAffineProjection_apply_of_continuous
          u hu.continuous z t v r hr hz hradius
      have hdiff : Tendsto (fun n => |P n - P m|) atTop (nhds |u z - P m|) :=
        (hprojection.sub tendsto_const_nhds).abs
      simpa only [P, R, A] using le_of_tendsto hdiff hfinite
    obtain ⟨C_P, hC_P_pos, hresidual⟩ :=
      exists_parabolicMorreyBoxAffineResidualMeanConst d hd
    let alpha : Real := parabolicMorreyExponent d
    let beta : Real := ((d : Real) + 2) / ((d : Real) + 1)
    let geom : Real := (1 - (2 : Real) ^ (-alpha))⁻¹
    let K : Real := (1 + 3 * (d : Real)) * 6 ^ beta * C_P *
      (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) * 3 ^ alpha
    let C : Real := 2 * (C_tail * geom + K)
    have halpha_pos : 0 < alpha := by
      dsimp only [alpha, parabolicMorreyExponent]
      have hd' : 0 < (d : Real) := by exact_mod_cast hd
      positivity
    have hbeta_pos : 0 < beta := by
      dsimp only [beta]
      positivity
    have htwopow_pos : 0 < (2 : Real) ^ (-alpha) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have htwopow_lt_one : (2 : Real) ^ (-alpha) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr halpha_pos)
    have hgeom_pos : 0 < geom := by
      dsimp only [geom]
      exact inv_pos.mpr (sub_pos.mpr htwopow_lt_one)
    have hK_pos : 0 < K := by
      dsimp only [K]
      positivity
    refine ⟨C, ?_, ?_⟩
    · dsimp only [C]
      positivity
    intro z hz w hw n hscale hscale_upper u hu huc
    let rho : Real := parabolicCoordinateDist z w
    let qz := parabolicDyadicSourceBox
      (parabolicDyadicAddressContaining d z hz n).2
    let qw := parabolicDyadicSourceBox
      (parabolicDyadicAddressContaining d w hw n).2
    let tMin : Real := min qz.baseTime qw.baseTime
    let vMid : PDE.Vec d := (z.2 + w.2) / 2
    have hqz_pos : 0 < qz.radius := by
      dsimp only [qz]
      exact parabolicDyadicSourceBox_radius_pos _
    have hrho_pos : 0 < rho := by
      dsimp only [rho]
      exact lt_of_lt_of_le hqz_pos hscale
    have hqw_radius : qz.radius = qw.radius := by
      change ((2 : Real) ^ n)⁻¹ = ((2 : Real) ^ n)⁻¹
      rfl
    have hqw_pos : 0 < qw.radius := by simpa only [hqw_radius] using hqz_pos
    have hscale_w : qw.radius ≤ rho := by simpa only [qz, qw, rho] using! hscale
    have hscale_upper_w : rho < 2 * qw.radius := by
      simpa only [qz, qw, rho] using! hscale_upper
    have hbig_pos : 0 < 3 * rho := mul_pos (by norm_num) hrho_pos
    obtain ⟨hsub_z, hsub_w, -, -⟩ :=
      parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox d z hz w hw n hscale
    have hz_closed : z ∈ parabolicClosedBox 1 qz.radius qz.baseTime qz.center := by
      change z ∈ parabolicClosedBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d z hz n)).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d z hz n)).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d z hz n)).center
      exact parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n
    have hw_closed : w ∈ parabolicClosedBox 1 qw.radius qw.baseTime qw.center := by
      change w ∈ parabolicClosedBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d w hw n)).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d w hw n)).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicIndexContaining d w hw n)).center
      exact parabolicDyadicAddressContaining_mem_closedForwardBox d w hw n
    obtain ⟨hres, hmean⟩ := hresidual tMin vMid (3 * rho) hbig_pos u hu huc
    have hratio_z : 3 * rho / qz.radius ≤ 6 := by
      apply (div_le_iff₀ hqz_pos).mpr
      nlinarith [hscale_upper]
    have hratio_w : 3 * rho / qw.radius ≤ 6 := by
      apply (div_le_iff₀ hqw_pos).mpr
      nlinarith [hscale_upper_w]
    have hratio_z_nonneg : 0 ≤ 3 * rho / qz.radius :=
      (div_pos (mul_pos (by norm_num) hrho_pos) hqz_pos).le
    have hratio_w_nonneg : 0 ≤ 3 * rho / qw.radius :=
      (div_pos (mul_pos (by norm_num) hrho_pos) hqw_pos).le
    have hratio_z_rpow : (3 * rho / qz.radius) ^ beta ≤ 6 ^ beta :=
      Real.rpow_le_rpow hratio_z_nonneg hratio_z hbeta_pos.le
    have hratio_w_rpow : (3 * rho / qw.radius) ^ beta ≤ 6 ^ beta :=
      Real.rpow_le_rpow hratio_w_nonneg hratio_w hbeta_pos.le
    have hD_nonneg : 0 ≤ parabolicMorreyDerivativeLpNorm d u := by
        unfold parabolicMorreyDerivativeLpNorm parabolicLpNorm parabolicELpNorm
        refine add_nonneg ENNReal.toReal_nonneg ?_
        refine Finset.sum_nonneg fun _ _ => ?_
        refine Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

      /- At the dyadic scale comparable to two reference points, the smooth value
      minus the canonical common forward-box affine projection has Morrey decay. -/
    have hbig_rpow : (3 * rho) ^ alpha = 3 ^ alpha * rho ^ alpha := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) ≤ 3) hrho_pos.le]
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
        (parabolicBox 1 (3 * rho) tMin vMid) hres := by
      rw [parabolicLpMeanNormOn_eq_toReal]
      exact ENNReal.toReal_nonneg
    have hnear_z :
        |parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
            parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z| ≤
          K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
      calc
        |parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
            parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z| ≤
            (1 + 3 * (d : Real)) * (3 * rho / qz.radius) ^ beta *
              parabolicLpMeanNormOn d
                (fun x => u x -
                  parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
                (parabolicBox 1 (3 * rho) tMin vMid) hres := by
              simpa only [beta] using hcompare_z
        _ ≤ (1 + 3 * (d : Real)) * 6 ^ beta *
              (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
                (3 * rho) ^ alpha * parabolicMorreyDerivativeLpNorm d u) := by
              gcongr
        _ = K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
              rw [hbig_rpow]
              dsimp only [K]
              ring
    have hnear_w :
        |parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
            parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w| ≤
          K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
      calc
        |parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
            parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w| ≤
            (1 + 3 * (d : Real)) * (3 * rho / qw.radius) ^ beta *
              parabolicLpMeanNormOn d
                (fun x => u x -
                  parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
                (parabolicBox 1 (3 * rho) tMin vMid) hres := by
              simpa only [beta] using hcompare_w
        _ ≤ (1 + 3 * (d : Real)) * 6 ^ beta *
              (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
                (3 * rho) ^ alpha * parabolicMorreyDerivativeLpNorm d u) := by
              gcongr
        _ = K * rho ^ alpha * parabolicMorreyDerivativeLpNorm d u := by
              rw [hbig_rpow]
              dsimp only [K]
              ring
    calc
      |(u z - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z) -
          (u w - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w)| =
          |(u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z) +
            (parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
              parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z) -
            ((u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w) +
              (parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
                parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w))| := by
                  congr 1
                  ring
      _ ≤ |u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z| +
            |parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
              parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z| +
            (|u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w| +
              |parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
                parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w|) := by
          calc
            _ ≤ |(u z - parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z) +
                (parabolicMorreyBoxAffineProjection qz.baseTime qz.center qz.radius u z -
                  parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z)| +
                |(u w - parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w) +
                  (parabolicMorreyBoxAffineProjection qw.baseTime qw.center qw.radius u w -
                    parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w)| := by
                      simpa only [sub_zero, zero_sub, abs_neg] using
                        abs_sub_le
                          ((u z - parabolicMorreyBoxAffineProjection
                              qz.baseTime qz.center qz.radius u z) +
                            (parabolicMorreyBoxAffineProjection
                              qz.baseTime qz.center qz.radius u z -
                              parabolicMorreyBoxAffineProjection
                                tMin vMid (3 * rho) u z))
                          0
                          ((u w - parabolicMorreyBoxAffineProjection
                              qw.baseTime qw.center qw.radius u w) +
                            (parabolicMorreyBoxAffineProjection
                              qw.baseTime qw.center qw.radius u w -
                              parabolicMorreyBoxAffineProjection
                                tMin vMid (3 * rho) u w))
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
  obtain ⟨CI, hCI_pos, hincrement⟩ : ∃ C : Real, 0 < C ∧
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
        ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
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
    obtain ⟨C_tail, hC_tail_pos, htail⟩ :=
      exists_parabolicMorreyDyadicContainingRadiusWeightedSlopeTailConst d hd
    obtain ⟨C_P, hC_P_pos, hresidual⟩ :=
      exists_parabolicMorreyBoxAffineResidualMeanConst d hd
    let alpha : Real := parabolicMorreyExponent d
    let beta : Real := ((d : Real) + 2) / ((d : Real) + 1)
    let q : Real := (2 : Real) ^ (-(1 - alpha))
    let geom : Real := (1 - q)⁻¹
    let K_compare : Real := 2 * (1 + 3 * (d : Real)) * 6 ^ beta * C_P *
      (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) * 3 ^ alpha
    let K_tail : Real := 2 * C_tail * geom
    let K_root : Real := 1 + 3 * (d : Real)
    let C : Real := K_compare + K_tail + K_root
    have halpha_pos : 0 < alpha := by
      dsimp only [alpha, parabolicMorreyExponent]
      have hd' : 0 < (d : Real) := by exact_mod_cast hd
      positivity
    have halpha_le_one : alpha <= 1 := by
      dsimp only [alpha, parabolicMorreyExponent]
      have hden : 0 < (d : Real) + 1 := by positivity
      apply (div_le_iff₀ hden).mpr
      linarith
    have hbeta_pos : 0 < beta := by
      dsimp only [beta]
      positivity
    have hq_pos : 0 < q := by
      dsimp only [q]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hq_lt_one : q < 1 := by
      dsimp only [q]
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      have halpha_lt_one : alpha < 1 := by
        dsimp only [alpha, parabolicMorreyExponent]
        have hden : 0 < (d : Real) + 1 := by positivity
        apply (div_lt_iff₀ hden).mpr
        have hlt : (d : Real) < (d : Real) + 1 := by
          linarith
        simpa only [one_mul] using hlt
      linarith
    have hgeom_pos : 0 < geom := by
      dsimp only [geom]
      exact inv_pos.mpr (sub_pos.mpr hq_lt_one)
    have hK_compare_pos : 0 < K_compare := by
      dsimp only [K_compare]
      positivity
    have hK_tail_pos : 0 < K_tail := by
      dsimp only [K_tail]
      positivity
    have hK_root_pos : 0 < K_root := by
      dsimp only [K_root]
      positivity
    refine ⟨C, by dsimp only [C]; positivity, ?_⟩
    intro z hz w hw n hscale hscale_upper hrho_one u hu huc
    let rho : Real := parabolicCoordinateDist z w
    let qz := parabolicDyadicSourceBox
      (parabolicDyadicAddressContaining d z hz n).2
    let qw := parabolicDyadicSourceBox
      (parabolicDyadicAddressContaining d w hw n).2
    let tMin : Real := min qz.baseTime qw.baseTime
    let vMid : PDE.Vec d := (z.2 + w.2) / 2
    let D : Real := parabolicMorreyDerivativeLpNorm d u
    let J : Real := parabolicSmoothJetLpNorm d u
    have hqz_pos : 0 < qz.radius := by
      dsimp only [qz]
      exact parabolicDyadicSourceBox_radius_pos _
    have hrho_pos : 0 < rho := by
      dsimp only [rho]
      exact lt_of_lt_of_le hqz_pos hscale
    have hqz_le_rho : qz.radius <= rho := by simpa only [qz, rho] using hscale
    have hrho_lt_two_qz : rho < 2 * qz.radius := by
      simpa only [qz, rho] using hscale_upper
    have hbig_pos : 0 < 3 * rho := mul_pos (by norm_num) hrho_pos
    have hratio : 3 * rho / qz.radius <= 6 := by
      apply (div_le_iff₀ hqz_pos).mpr
      nlinarith [hrho_lt_two_qz]
    have hratio_nonneg : 0 <= 3 * rho / qz.radius :=
      (div_pos (mul_pos (by norm_num) hrho_pos) hqz_pos).le
    have hratio_rpow : (3 * rho / qz.radius) ^ beta <= 6 ^ beta :=
      Real.rpow_le_rpow hratio_nonneg hratio hbeta_pos.le
    have hD_nonneg : 0 <= D := by
      dsimp only [D, parabolicMorreyDerivativeLpNorm, parabolicLpNorm,
        parabolicELpNorm]
      exact add_nonneg ENNReal.toReal_nonneg
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    have hJ_nonneg : 0 <= J := by
      dsimp only [J, parabolicSmoothJetLpNorm]
      exact ENNReal.toReal_nonneg
    have hbig_rpow : (3 * rho) ^ alpha = 3 ^ alpha * rho ^ alpha := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) <= 3) hrho_pos.le]
    obtain ⟨hsub_z, -, -, -⟩ :=
      parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox d z hz w hw n hscale
    obtain ⟨hres, hmean⟩ := hresidual tMin vMid (3 * rho) hbig_pos u hu huc
    have hmean_nonneg : 0 <= parabolicLpMeanNormOn d
        (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
        (parabolicBox 1 (3 * rho) tMin vMid) hres := by
      rw [parabolicLpMeanNormOn_eq_toReal]
      exact ENNReal.toReal_nonneg
    have hdisc := parabolicMorreyNestedProjection_discrepancy_le_largeResidual
      tMin vMid hbig_pos qz.baseTime qz.center hqz_pos hsub_z u hres
    have hslope_disc : qz.radius * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
          parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| <=
        (1 + 3 * (d : Real)) * (3 * rho / qz.radius) ^ beta *
          parabolicLpMeanNormOn d
            (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
            (parabolicBox 1 (3 * rho) tMin vMid) hres := by
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans hdisc
    have hcompare : rho * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i -
          parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i| <=
        K_compare * rho ^ alpha * D := by
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
        _ <= 2 * ((1 + 3 * (d : Real)) * (3 * rho / qz.radius) ^ beta *
            parabolicLpMeanNormOn d
              (fun x => u x - parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u x)
              (parabolicBox 1 (3 * rho) tMin vMid) hres) := by
                gcongr
                · apply (div_le_iff₀ hqz_pos).mpr
                  linarith
        _ <= 2 * ((1 + 3 * (d : Real)) * 6 ^ beta *
            (C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
              (3 * rho) ^ alpha * D)) := by
                gcongr
        _ = K_compare * rho ^ alpha * D := by
          rw [hbig_rpow]
          dsimp only [K_compare]
          ring
    have hgeom : ∀ N : Nat, (∑ k ∈ Finset.range N, q ^ k) <= geom := by
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
      linarith [pow_nonneg hq_pos.le N]
    have htail_raw := htail z hz u hu huc n
    have htail : rho * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
          parabolicMorreyBoxVelocitySlope
            (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).center
            (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).radius u i| <=
        K_tail * rho ^ alpha * D := by
      have hrpow :=
        Real.rpow_le_rpow hqz_pos.le hqz_le_rho halpha_pos.le
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
              exact hgeom n
        _ = K_tail * rho ^ alpha * D := by
              dsimp only [K_tail]
              ring
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
    have hroot_coefficient :=
      parabolicMorreyRootAffineCoefficient_le_parabolicSmoothJetLpNorm d u hu huc
    have hroot_slope : ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope
          (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).baseTime
          (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).center
          (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).radius u i| <=
        K_root * J := by
      simpa only [hroot_box_radius, hroot_box_time, hroot_box_center, K_root, J] using
        (le_add_of_nonneg_left (abs_nonneg _)).trans hroot_coefficient
    have hrho_rpow : rho <= rho ^ alpha := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge hrho_pos hrho_one halpha_le_one)
    have hroot : rho * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope
          (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).baseTime
          (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).center
          (parabolicDyadicSourceBox (parabolicDyadicAddressContaining d z hz 0).2).radius u i| <=
        K_root * rho ^ alpha * J := by
      calc
        rho * ∑ i : Fin d,
            |parabolicMorreyBoxVelocitySlope
              (parabolicDyadicSourceBox
                (parabolicDyadicAddressContaining d z hz 0).2).baseTime
              (parabolicDyadicSourceBox
                (parabolicDyadicAddressContaining d z hz 0).2).center
              (parabolicDyadicSourceBox
                (parabolicDyadicAddressContaining d z hz 0).2).radius u i| <=
            rho * (K_root * J) := mul_le_mul_of_nonneg_left hroot_slope hrho_pos.le
        _ <= rho ^ alpha * (K_root * J) :=
          mul_le_mul_of_nonneg_right hrho_rpow
            (mul_nonneg hK_root_pos.le hJ_nonneg)
        _ = K_root * rho ^ alpha * J := by ring
    have hslope : rho * ∑ i : Fin d,
        |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| <=
        (K_compare + K_tail) * rho ^ alpha * D + K_root * rho ^ alpha * J := by
      have htriangle : ∑ i : Fin d,
          |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| <=
          ∑ i : Fin d,
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
                (parabolicDyadicAddressContaining d z hz 0).2).radius u i| := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        let a := parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i -
          parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i
        let b := parabolicMorreyBoxVelocitySlope qz.baseTime qz.center qz.radius u i -
          parabolicMorreyBoxVelocitySlope
            (parabolicDyadicSourceBox
              (parabolicDyadicAddressContaining d z hz 0).2).baseTime
            (parabolicDyadicSourceBox
              (parabolicDyadicAddressContaining d z hz 0).2).center
            (parabolicDyadicSourceBox
              (parabolicDyadicAddressContaining d z hz 0).2).radius u i
        let c := parabolicMorreyBoxVelocitySlope
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz 0).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz 0).2).center
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz 0).2).radius u i
        have habc : a + b + c =
            parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i := by
          dsimp only [a, b, c]
          ring
        calc
          |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| = |a + b + c| :=
            congrArg abs habc.symm
          _ <= |a + b| + |c| := abs_add_le _ _
          _ <= (|a| + |b|) + |c| := add_le_add_left (abs_add_le _ _) _
          _ = |a| + |b| + |c| := by ring
          _ = _ := by rfl
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
          mul_le_mul_of_nonneg_left htriangle hrho_pos.le
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
          add_le_add (add_le_add hcompare htail) hroot
        _ = (K_compare + K_tail) * rho ^ alpha * D + K_root * rho ^ alpha * J := by ring
    have hprojection :
        |parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u z -
          parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u w| <=
        rho * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| := by
      have hvelocity (i : Fin d) : |z.2 i - w.2 i| <= rho := by
        have hnorm : ‖z.2 - w.2‖ <= rho := by
          dsimp only [rho, parabolicCoordinateDist]
          exact le_max_right _ _
        have hcoordinate := (pi_norm_le_iff_of_nonneg hrho_pos.le).mp hnorm i
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoordinate
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
                congr 1
                calc
                  parabolicMorreyBoxAverage tMin vMid (3 * rho) u +
                      ∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                        (z.2 i - vMid i) -
                      (parabolicMorreyBoxAverage tMin vMid (3 * rho) u +
                        ∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                          (w.2 i - vMid i)) =
                      (∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                        (z.2 i - vMid i)) -
                      ∑ i : Fin d, parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i *
                        (w.2 i - vMid i) := by ring
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
              apply Finset.sum_congr rfl
              intro i _
              rw [abs_mul]
        _ <= ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| * rho :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hvelocity i) (abs_nonneg _)
        _ = rho * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| := by
          rw [Finset.mul_sum]
          ring_nf
    have huJet :=
      parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
    have hD_le_J : D <= J := by
      dsimp only [D, J]
      let E : ENNReal := parabolicELpNorm d (timeDerivative u) +
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNorm d (fun z => velocityHessian u z i j)
      have hE : E <= parabolicSmoothJetELpNorm d u := by
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
          _ = _ := by ac_rfl
      have hreal :=
        ENNReal.toReal_mono (parabolicSmoothJetELpNorm_ne_top huJet) hE
      have htoadd : E.toReal = (parabolicELpNorm d (timeDerivative u)).toReal +
          (∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
        apply ENNReal.toReal_add
        · exact huJet.2.1.eLpNorm_ne_top
        · apply ENNReal.sum_ne_top.mpr
          intro i _
          apply ENNReal.sum_ne_top.mpr
          intro j _
          exact (huJet.2.2.2 i j).eLpNorm_ne_top
      have htosum : (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
          ∑ i : Fin d, ∑ j : Fin d,
            (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
        calc
          (∑ i : Fin d, ∑ j : Fin d,
              parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
              ∑ i : Fin d, (∑ j : Fin d,
                parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
                  apply ENNReal.toReal_sum
                  intro i _
                  apply ENNReal.sum_ne_top.mpr
                  intro j _
                  exact (huJet.2.2.2 i j).eLpNorm_ne_top
          _ = ∑ i : Fin d, ∑ j : Fin d,
              (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
                apply Finset.sum_congr rfl
                intro i _
                apply ENNReal.toReal_sum
                intro j _
                exact (huJet.2.2.2 i j).eLpNorm_ne_top
      have hleft : E.toReal = parabolicMorreyDerivativeLpNorm d u := by
        calc
          E.toReal = (parabolicELpNorm d (timeDerivative u)).toReal +
              (∑ i : Fin d, ∑ j : Fin d,
                parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := htoadd
          _ = (parabolicELpNorm d (timeDerivative u)).toReal +
              ∑ i : Fin d, ∑ j : Fin d,
                (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by rw [htosum]
          _ = parabolicMorreyDerivativeLpNorm d u := rfl
      calc
        parabolicMorreyDerivativeLpNorm d u = E.toReal := hleft.symm
        _ <= parabolicSmoothJetLpNorm d u := hreal
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
          rho * ∑ i : Fin d, |parabolicMorreyBoxVelocitySlope tMin vMid (3 * rho) u i| := by
            simpa only [qz, qw, tMin, vMid, rho] using hprojection
      _ <= (K_compare + K_tail) * rho ^ alpha * D + K_root * rho ^ alpha * J := hslope
      _ <= (K_compare + K_tail) * rho ^ alpha * J + K_root * rho ^ alpha * J := by
        gcongr
      _ = C * rho ^ alpha * J := by
        dsimp only [C]
        ring
      _ = C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
          parabolicSmoothJetLpNorm d u := by
        rfl
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
    let P : TimeVelocity d -> Real := fun x =>
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
      simpa only [P, rho, alpha, J] using
        hincrement z hz w hw n hn_lower hn_upper hrho_one u hu huc
    have hujet :=
      parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
    have hderivative_le_jet : D <= J := by
      simpa only [D, J] using
        parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm hujet
    have hrho_nonneg : 0 <= rho := by
      dsimp only [rho]
      exact parabolicCoordinateDist_nonneg z w
    have hC4rho_nonneg :=
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
      _ = _ := by simp only [rho, alpha, J]

end HypoellipticAleksandrov.Parabolic
