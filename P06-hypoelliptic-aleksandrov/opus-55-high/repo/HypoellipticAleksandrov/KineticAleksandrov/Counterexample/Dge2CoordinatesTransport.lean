module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesDifferential
import Mathlib.Tactic.LinearCombination

/-! # Exact transport contraction of the homogeneous ansatz -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

variable {d : ℕ} (alpha : ℝ) (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v w : PDE.Vec d)

/-- The full joint derivative splits into the two literal slice derivatives. -/
theorem fderiv_uncurry_split 
    (y e u w : PDE.Vec d) (hphi : DifferentiableAt ℝ (Function.uncurry phi) (y, e)) :
    fderiv ℝ (Function.uncurry phi) (y, e) (u, w) =
      fderiv ℝ (fun z => phi z e) y u + fderiv ℝ (fun z => phi y z) e w := by
  have hiy : HasFDerivAt (fun z : PDE.Vec d => (z, e))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
        (0)) y := by
    fun_prop
  have hie : HasFDerivAt (fun z : PDE.Vec d => (y, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod
        (ContinuousLinearMap.id ℝ _)) e := by
    fun_prop
  have hy := hphi.hasFDerivAt.comp y hiy
  have he := hphi.hasFDerivAt.comp e hie
  have hy' : HasFDerivAt (fun z => phi z e)
      ((fderiv ℝ (Function.uncurry phi) (y, e)).comp
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod 0)) y := by
    fun_prop
  have he' : HasFDerivAt (fun z => phi y z)
      ((fderiv ℝ (Function.uncurry phi) (y, e)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ _))) e := by
    fun_prop
  rw [hy'.fderiv, he'.fderiv]
  have hsplit : (u, w) = ((u, 0)) + (0, w) := by simp
  rw [hsplit, map_add]
  simp

/-- The normalized velocity differential has the exact inverse-radius factor. -/
theorem normalizedVelocityDifferential_apply  (hx : x ≠ 0) :
    normalizedVelocityDifferential x v w =
      (-(1 / 3 : ℝ) * (PDE.vecEuclideanNorm x)⁻¹ *
        PDE.vecDot (positionDirection x) w) • normalizedVelocity x v := by
  have hr  := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3) - 1) =
      (PDE.vecEuclideanNorm x)⁻¹ * Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3)) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
    ring
  simp only [normalizedVelocityDifferential, ContinuousLinearMap.smulRight_apply,
    smul_apply, positionRadiusDifferential_apply, normalizedVelocity,
    smul_smul, hp]
  ring

/-- The cube-root physical velocity is recovered exactly from the normalized velocity. -/
theorem velocity_eq_cubeRoot_smul  (x v : PDE.Vec d) (hx : x ≠ 0) :
    v = Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) • normalizedVelocity x v := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  unfold normalizedVelocity
  rw [smul_smul]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add hr]
  norm_num

/-- The exact position derivative gives the angular expression before transport contraction. -/
theorem fderiv_homogeneousAnsatz_position  (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    fderiv ℝ (fun z => homogeneousAnsatz alpha phi z v) x w =
      Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
        (PDE.vecDot (positionDirection x) w *
          (alpha / 3 * phi (normalizedVelocity x v) (positionDirection x) -
            (1 / 3 : ℝ) * fderiv ℝ (fun z => phi z (positionDirection x))
              (normalizedVelocity x v) (normalizedVelocity x v)) +
          fderiv ℝ (fun z => phi (normalizedVelocity x v) z) (positionDirection x)
            (w - PDE.vecDot (positionDirection x) w • positionDirection x)) := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      (PDE.vecEuclideanNorm x)⁻¹ =
      Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
    ring
  rw [(hasFDerivAt_homogeneousAnsatz_position alpha phi x v hx hphi).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, positionRadiusDifferential_apply,
    normalizedVelocityDifferential_apply x v w hx, positionDirectionDifferential_apply]
  rw [fderiv_uncurry_split phi _ _ _ _ hphi, map_smul, map_smul]
  linear_combination
    (PDE.vecDot _ w *
      (-(1 / 3) * fderiv ℝ _
        _ (normalizedVelocity x v)) +
      fderiv ℝ _ _
        (w - PDE.vecDot _ w • positionDirection x)) * hp

/-- Transport and the velocity Hessian have the identical kinetic prefactor. -/
theorem homogeneousAnsatz_transport  (x v : PDE.Vec d) (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    fderiv ℝ (fun z => homogeneousAnsatz alpha phi z v) x v =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) *
        ansatzTransport alpha phi (normalizedVelocity x v) (positionDirection x) := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hv := velocity_eq_cubeRoot_smul x v hx
  have hdot : PDE.vecDot (positionDirection x) v =
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) *
        PDE.vecDot (normalizedVelocity x v) (positionDirection x) := by
    conv_lhs => rhs; rw [hv]
    unfold PDE.vecDot
    simp only [Pi.smul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htangent : v - PDE.vecDot (positionDirection x) v • positionDirection x =
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) •
        (normalizedVelocity x v -
          PDE.vecDot (normalizedVelocity x v) (positionDirection x) • positionDirection x) := by
    rw [hdot, smul_sub, smul_smul, ← hv]
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hr]
    ring
  rw [fderiv_homogeneousAnsatz_position alpha phi x v v hx hphi, htangent, hdot, map_smul]
  calc
    _ = (Real.rpow _ _ *
        Real.rpow _ (1 / 3)) *
        ansatzTransport alpha phi _ _ := by
      unfold ansatzTransport
      ring
    _ = _ := by rw [hp]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
