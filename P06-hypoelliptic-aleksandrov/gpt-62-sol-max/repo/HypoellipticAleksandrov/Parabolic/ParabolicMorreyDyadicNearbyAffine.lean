module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointDecay
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyGeometry
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjectionClosed
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyBoxResidualMean

/-!
# Affine-modulo nearby-pair parabolic Morrey decay

This module combines the dyadic pointwise tail with a literal common nearby
forward box.  It does not assert a common dyadic address or a raw Holder bound.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

/-- At the dyadic scale comparable to two reference points, the smooth value
minus the canonical common forward-box affine projection has Morrey decay. -/
theorem exists_parabolicMorreyDyadicNearbyAffineModuloDecayConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (hz : z ∈ parabolicDyadicReferenceCell d)
        (w : TimeVelocity d)
        (hw : w ∈ parabolicDyadicReferenceCell d)
        (n : Nat),
        (parabolicDyadicSelectedBox z hz n).radius ≤
            parabolicCoordinateDist z w →
        parabolicCoordinateDist z w <
          2 * (parabolicDyadicSelectedBox z hz n).radius →
        ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
          HasCompactSupport u ->
          |(u z - parabolicMorreyBoxAffineProjection
              (min
                (parabolicDyadicSelectedBox z hz n).baseTime
                (parabolicDyadicSelectedBox w hw n).baseTime)
              ((z.2 + w.2) / 2)
              (3 * parabolicCoordinateDist z w) u z) -
            (u w - parabolicMorreyBoxAffineProjection
              (min
                (parabolicDyadicSelectedBox z hz n).baseTime
                (parabolicDyadicSelectedBox w hw n).baseTime)
              ((z.2 + w.2) / 2)
              (3 * parabolicCoordinateDist z w) u w)| ≤
            C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
              parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C_tail, hC_tail_pos, htail⟩ :=
    exists_parabolicMorreyDyadicContainingProjectionValueDecayConst d hd
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
  let rho := parabolicCoordinateDist z w
  let qz := parabolicDyadicSelectedBox z hz n
  let qw := parabolicDyadicSelectedBox w hw n
  let tMin := min qz.baseTime qw.baseTime
  let vMid := (z.2 + w.2) / 2
  let F := parabolicMorreyBoxAffineProjection tMin vMid (3 * rho) u
  let D := parabolicMorreyDerivativeLpNorm d u
  have hD : 0 ≤ D := parabolicMorreyDerivativeLpNorm_nonneg d u
  have hrho : 0 < rho := (parabolicDyadicSourceBox_radius_pos _).trans_le hscale
  have hbig : 0 < 3 * rho := by positivity
  obtain ⟨hsz, hsw, _, _⟩ := parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox
    d z hz w hw n hscale
  obtain ⟨hres, hmean⟩ := hresidual tMin vMid (3 * rho) hbig u hu huc
  let M := parabolicLpMeanNormOn d (fun x => u x - F x) (parabolicBox 1 (3 * rho) tMin vMid) hres
  have hM : 0 ≤ M := by
    dsimp only [M]
    rw [parabolicLpMeanNormOn_eq_toReal]
    exact ENNReal.toReal_nonneg
  have hbigpow := Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hrho.le (z := alpha)
  have approx (p : TimeVelocity d) (hp : p ∈ parabolicDyadicReferenceCell d)
      (hsub : inkSpotsSourceBox (parabolicDyadicSelectedBox p hp n) ⊆
        parabolicBox 1 (3 * rho) tMin vMid) :
      |u p - F p| ≤ (C_tail * geom + K) * rho ^ alpha * D := by
    let q := parabolicDyadicSelectedBox p hp n
    let G := parabolicMorreyBoxAffineProjection q.baseTime q.center q.radius u
    have hq : 0 < q.radius := parabolicDyadicSourceBox_radius_pos _
    have hs : q.radius ≤ rho := hscale
    have hl : rho < 2 * q.radius := hscale_upper
    have hratio : 3 * rho / q.radius ≤ 6 := (div_le_iff₀ hq).mpr (by linarith)
    have hpow := Real.rpow_le_rpow (div_nonneg hbig.le hq.le) hratio hbeta_pos.le
    have ht : |u p - G p| ≤ C_tail * q.radius ^ alpha * geom * D := htail p hp u hu huc n
    have ht' : |u p - G p| ≤ C_tail * rho ^ alpha * geom * D := ht.trans (by gcongr)
    have hc : |G p - F p| ≤ (1 + 3 * (d : ℝ)) * (3 * rho / q.radius) ^ beta * M :=
      parabolicMorreyNestedProjection_abs_sub_le_largeResidual_closed tMin vMid hbig
        q.baseTime q.center hq hsub u p
        (parabolicDyadicAddressContaining_mem_closedForwardBox d p hp n) hres
    have hc' : |G p - F p| ≤ K * rho ^ alpha * D := by
      calc
        _ ≤ (1 + 3 * (d : ℝ)) * (3 * rho / q.radius) ^ beta * M := hc
        _ ≤ (1 + 3 * (d : ℝ)) * 6 ^ beta *
            (C_P * (2 : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1)) * (3 * rho) ^ alpha * D) := by
          gcongr
        _ = _ := by rw [hbigpow]; dsimp only [K]; ring
    convert (abs_sub_le (u p) (G p) (F p)).trans (add_le_add ht' hc') using 1 <;> ring
  change |(u z - F z) - (u w - F w)| ≤ C * rho ^ alpha * D
  calc
    _ ≤ |u z - F z| + |u w - F w| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (u z - F z) 0 (u w - F w)
    _ ≤ _ := add_le_add (approx z hz hsz) (approx w hw hsw)
    _ = C * rho ^ alpha * D := by dsimp only [C]; ring

end HypoellipticAleksandrov.Parabolic
