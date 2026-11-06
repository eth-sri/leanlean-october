module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincarePhysical
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNormTransport
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm

/-!
# Mean residual estimate on a physical parabolic Morrey box

This module combines the physical affine Poincare estimate with normalized
volume and derivative-norm restriction to control the canonical affine
residual of compactly supported smooth data.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal

theorem exists_parabolicMorreyBoxAffineResidualMeanConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C_P : Real, 0 < C_P ∧
      ∀ (t₀ : Real) (v₀ : PDE.Vec d) (r : Real), 0 < r ->
      ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∃ hres : MemLp
          (fun z => u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z)
          (parabolicExponent d)
          (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)),
          parabolicLpMeanNormOn d
            (fun z => u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z)
            (parabolicBox 1 r t₀ v₀) hres <=
            C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
              r ^ parabolicMorreyExponent d * parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C_P, hC_P_pos, hC_P⟩ := exists_parabolicMorreyBoxAffinePoincareConst d hd
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro t₀ v₀ r hr u hu huc
  let Q := parabolicBox 1 r t₀ v₀
  let f : TimeVelocity d -> Real := fun z =>
    u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z
  have hres : MemLp f (parabolicExponent d) (parabolicNormalizedVolumeOn Q) := by
    let f : TimeVelocity d -> Real := fun z =>
      u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z
    have _h_inl_9 : Continuous (parabolicMorreyBoxAffineProjection t₀ v₀ r u) := by
      unfold parabolicMorreyBoxAffineProjection
      apply Continuous.add continuous_const
      apply continuous_finset_sum
      intro i _
      exact continuous_const.mul ((continuous_apply i).comp continuous_snd |>.sub
        continuous_const)
    have hf : Continuous f := hu.continuous.sub
      _h_inl_9
    have hunitRaw := Continuous.memLp_parabolicMorreyUnitBox (hf.comp (contDiff_parabolicAffine t₀ v₀ r).continuous)
    have hunitMean : MemLp (pullbackScalar f t₀ v₀ r) (parabolicExponent d)
        (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) :=
      memLp_parabolicNormalizedVolumeOn_of_memLp
        (ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).1 hunitRaw
    exact (memLp_parabolicNormalizedVolumeOn_parabolicBox_iff t₀ v₀ hr f).mpr hunitMean
  refine ⟨hres, ?_⟩
  have hlocal : parabolicLpMeanNormOn d (fun z => u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z) (parabolicBox 1 r t₀ v₀) hres <= C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) * r ^ parabolicMorreyExponent d * parabolicMorreyDerivativeLpNormOn d u (parabolicBox 1 r t₀ v₀) := by
    have hP : (r ^ 2)⁻¹ * parabolicLpNormOn d (fun z => u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z) (parabolicBox 1 r t₀ v₀) <= C_P * parabolicMorreyDerivativeLpNormOn d u (parabolicBox 1 r t₀ v₀) := by
      simpa only [parabolicMorreyDerivativeLpNormOn, Q] using hC_P t₀ v₀ r hr u hu
    let f : TimeVelocity d -> Real := fun z =>
      u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z
    let Q := parabolicBox 1 r t₀ v₀
    let A : Real := parabolicMorreyDerivativeLpNormOn d u Q
    have hraw := memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
      (volume_parabolicMorreyBox_pos t₀ v₀ hr)
      (volume_parabolicMorreyBox_lt_top t₀ v₀ hr) hres
    have hrawbound : parabolicLpNormOn d f Q <= r ^ 2 * (C_P * A) := by
      calc
        parabolicLpNormOn d f Q = r ^ 2 * ((r ^ 2)⁻¹ * parabolicLpNormOn d f Q) := by
          field_simp [hr.ne']
        _ <= r ^ 2 * (C_P * A) := mul_le_mul_of_nonneg_left (by
          simpa only [f, Q, A] using hP) (sq_nonneg r)
    change parabolicLpMeanNormOn d f Q hres <=
      C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
        r ^ parabolicMorreyExponent d * A
    rw [parabolicLpMeanNormOn_eq_volume_toReal_inv_rpow_mul_parabolicLpNormOn
      (volume_parabolicMorreyBox_pos t₀ v₀ hr)
      (volume_parabolicMorreyBox_lt_top t₀ v₀ hr) f hraw hres,
      volume_parabolicMorreyBox_toReal t₀ v₀ hr]
    refine (mul_le_mul_of_nonneg_left (by simpa only [Q] using hrawbound)
      (Real.rpow_nonneg (inv_nonneg.mpr
        (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hr.le _))) _)).trans_eq ?_
    have hp : (1 / parabolicExponent d).toReal = 1 / ((d : Real) + 1) := by
      unfold parabolicExponent
      have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
      rw [hcast, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
      norm_num
    rw [hp]
    change ((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)) *
        (r ^ 2 * (C_P * A)) = _
    have _h_inl_10 : ((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)) * r ^ 2 = (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) * r ^ parabolicMorreyExponent d := by
      have htwo : (0 : Real) < 2 := by norm_num
      have hdenom : (d : Real) + 1 ≠ 0 := by positivity
      rw [Real.inv_rpow (mul_nonneg (pow_nonneg htwo.le _) (pow_nonneg hr.le _)),
        Real.mul_rpow (pow_nonneg htwo.le _) (pow_nonneg hr.le _), mul_inv_rev,
        ← Real.rpow_natCast 2 d, ← Real.rpow_natCast r (d + 2),
        ← Real.rpow_mul hr.le, ← Real.rpow_mul htwo.le,
        ← Real.rpow_neg hr.le, ← Real.rpow_neg htwo.le,
        ← Real.rpow_natCast r 2]
      rw [show (r ^ (-(↑(d + 2) * (1 / ((d : Real) + 1)))) *
          2 ^ (-(↑d * (1 / ((d : Real) + 1))))) * r ^ ((2 : Nat) : Real) =
          2 ^ (-(↑d * (1 / ((d : Real) + 1)))) *
            (r ^ (-(↑(d + 2) * (1 / ((d : Real) + 1)))) *
              r ^ ((2 : Nat) : Real)) by ring,
        ← Real.rpow_add hr]
      unfold parabolicMorreyExponent
      congr 1
      · field_simp [hdenom]
      · congr 1
        push_cast
        field_simp [hdenom]
        ring
    rw [show ((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)) *
        (r ^ 2 * (C_P * A)) =
        (((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)) * r ^ 2) *
          C_P * A by ring,
      _h_inl_10]
    ring
  have huJet :=
    parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
  exact hlocal.trans <| by
    gcongr
    exact parabolicMorreyDerivativeLpNormOn_le u Q huJet

end HypoellipticAleksandrov.Parabolic
