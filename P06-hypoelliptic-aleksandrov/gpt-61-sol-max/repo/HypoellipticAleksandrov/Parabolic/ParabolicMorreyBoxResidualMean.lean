module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincarePhysical
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNormTransport
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep

open private HypoellipticAleksandrov.Parabolic.dyadic_parent_normalization_factor from HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep
open private HypoellipticAleksandrov.Parabolic.smooth_parent_residual_memLp from HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep
open private HypoellipticAleksandrov.Parabolic.continuous_parabolicMorreyBoxAffineProjection from HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep


/-!
# Mean residual estimate on a physical parabolic Morrey box

This module combines the physical affine Poincare estimate with normalized
volume and derivative-norm restriction to control the canonical affine
residual of compactly supported smooth data.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set


variable {d : Nat}










private theorem parabolicMorreyBoxAffineResidual_mean_bound
     (C : Real) (t : Real) (v : PDE.Vec d) {r : Real} (hr : 0 < r)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hP : (r ^ 2)⁻¹ *
      parabolicLpNormOn d
        (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
        (parabolicBox 1 r t v) <=
      C * parabolicMorreyDerivativeLpNormOn d u (parabolicBox 1 r t v))
    (hres : MemLp (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t v))) :
    parabolicLpMeanNormOn d
        (fun z => u z - parabolicMorreyBoxAffineProjection t v r u z)
        _ hres <=
      C * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
        r ^ parabolicMorreyExponent d *
          parabolicMorreyDerivativeLpNormOn d u (parabolicBox 1 r t v) := by
  let sharedTerm_81d2a227f0 := (((2 : Real) ^ d * r ^ (d + 2))⁻¹ ^ (1 / ((d : Real) + 1)))
  let f  := fun z =>
    u z - parabolicMorreyBoxAffineProjection t v r u z
  let Q  := parabolicBox 1 r t v
  let A : Real := parabolicMorreyDerivativeLpNormOn d u Q
  have hraw := memLp_restrict_of_memLp_parabolicNormalizedVolumeOn
    (volume_parabolicMorreyBox_pos t v hr)
    (volume_parabolicMorreyBox_lt_top t v hr) hres

  change parabolicLpMeanNormOn d f Q hres <=
    C * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
      r ^ parabolicMorreyExponent d * A
  rw [parabolicLpMeanNormOn_eq_volume_toReal_inv_rpow_mul_parabolicLpNormOn
    (volume_parabolicMorreyBox_pos t v hr)
    (volume_parabolicMorreyBox_lt_top t v hr) f hraw hres,
    volume_parabolicMorreyBox_toReal t v hr]
  refine (mul_le_mul_of_nonneg_left ((by
      calc
        parabolicLpNormOn d f Q = r ^ 2 * ((r ^ 2)⁻¹ * parabolicLpNormOn d f Q) := by
          field_simp [hr.ne']
        _ <= r ^ 2 * (C * A) := mul_le_mul_of_nonneg_left (hP) (sq_nonneg r)))
    (Real.rpow_nonneg (inv_nonneg.mpr
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hr.le _))) _)).trans_eq ?_
  have hp : (1 / parabolicExponent d).toReal = 1 / ((d : Real) + 1) := by
    unfold parabolicExponent
    have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
    rw [hcast, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
    norm_num
  rw [hp]
  change sharedTerm_81d2a227f0 *
      (r ^ 2 * (C * A)) = _
  rw [show sharedTerm_81d2a227f0 *
      (r ^ 2 * (C * A)) =
      (sharedTerm_81d2a227f0 * r ^ 2) *
        C * A by ring,
    _root_.HypoellipticAleksandrov.Parabolic.dyadic_parent_normalization_factor hr]
  ring

/-- On every positive-radius forward physical box, the canonical affine
residual of compactly supported `C²` data has its normalized `L^(d + 1)` mean
controlled by the global derivative-only Morrey norm. -/
theorem exists_parabolicMorreyBoxAffineResidualMeanConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C_P : Real, 0 < C_P ∧
      ∀ (t₀ : Real) (v₀ : PDE.Vec d) (r : Real), 0 < r ->
      ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d, ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∃ hres : MemLp
          (fun z => u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z)
          (parabolicExponent d)
          (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)),
          parabolicLpMeanNormOn d
            (fun z => u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z)
            _ hres <=
            C_P * (2 : Real) ^ (-(d : Real) / ((d : Real) + 1)) *
              r ^ parabolicMorreyExponent d * parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C_P, hC_P_pos, hC_P⟩ := exists_parabolicMorreyBoxAffinePoincareConst d hd
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro t₀ v₀ r hr u hu huc


  have hres  := _root_.HypoellipticAleksandrov.Parabolic.smooth_parent_residual_memLp t₀ v₀ hr u hu
  refine ⟨hres, ?_⟩
  have hlocal := parabolicMorreyBoxAffineResidual_mean_bound C_P t₀ v₀ hr u
    (hC_P t₀ v₀ r hr u hu)
    hres

  exact hlocal.trans <| by
    gcongr
    exact parabolicMorreyDerivativeLpNormOn_le u (parabolicBox 1 r t₀ v₀) (parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc)

end HypoellipticAleksandrov.Parabolic
