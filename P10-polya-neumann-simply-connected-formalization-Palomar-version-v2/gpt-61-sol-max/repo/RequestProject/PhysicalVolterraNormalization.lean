module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalVekuaTrace

/-!
# Ordinary averaged normalization of the genuine Vekua trace

Scalar multiplication commutes with every actual interval primitive.
The pointwise boundary series therefore has exactly the same form in
averaged Fourier coordinates, with the genuine sqrt(2π) normalization.
-/

public section

open scoped ContDiff



namespace PolyaNeumann

open Set Metric

theorem volterraPrimitiveIterate_const_mul a h c j :
    volterraPrimitiveIterate a (fun θ => c * h θ) j =
      fun θ => c * volterraPrimitiveIterate a h j θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext θ
    change (∫ s in (0)..θ,
      a s * volterraPrimitiveIterate a (fun t => c * h t) j s) =
      c * (∫ s in (0)..θ, a s * volterraPrimitiveIterate a h j s)
    rw [← intervalIntegral.integral_const_mul]
    grind

theorem hardyFourierTrace_const_mul c h θ :
    hardyFourierTrace (fun n => c * h n) θ = c * hardyFourierTrace h θ := by
  unfold hardyFourierTrace
  simp  [mul_assoc]
  exact tsum_mul_left

theorem hardyFourierTrace_normalizedHardyAverage b θ :
    hardyFourierTrace (normalizedHardyAverage b) θ =
      (Real.sqrt circlePeriod : ℂ)⁻¹ * hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ :=
  hardyFourierTrace_const_mul _ _ _

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)

/-- The genuine ordinary coordinate trace is the convergent Volterra
series of its original averaged input. -/
theorem localConformalVekuaBoundary_average_volterra_hasSum_of_H1
    E (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) θ :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j *
      (F (unitCircleMap θ) - F 1) ^ j *
      volterraPrimitiveIterate (fun s => star (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ)
      (hardyFourierTrace (normalizedHardyAverage
        (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b)) θ) := by
  let c  := (Real.sqrt circlePeriod : ℂ)⁻¹
  have hfun : hardyFourierTrace (normalizedHardyAverage b) =
      fun t => c * hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) t := by
    funext t
    exact hardyFourierTrace_normalizedHardyAverage b t
  have hs := (localConformalVekuaBoundary_volterra_hasSum_of_H1 hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E b hbn hb1 θ).mul_left c
  simp only [starRingEnd_apply] at hs
  convert hs using 1
  · funext j
    rw [hfun, volterraPrimitiveIterate_const_mul]
    ring
  · exact hardyFourierTrace_normalizedHardyAverage _ θ

end PhysicalCoordinates

end PolyaNeumann
