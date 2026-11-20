module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.PlanarNotation

/-!
# Ordinary averaged normalization of the genuine Vekua trace

Scalar multiplication commutes with every actual interval primitive.
The pointwise boundary series therefore has exactly the same form in
averaged Fourier coordinates, with the genuine sqrt(2π) normalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Metric

theorem volterraPrimitiveIterate_const_mul (a h : ℝ → ℂ) (c : ℂ) (j : ℕ) :
    volterraPrimitiveIterate a (fun θ => c * h θ) j =
      fun θ => c * volterraPrimitiveIterate a h j θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext θ
    change (∫ s in (0 : ℝ)..θ,
      a s * volterraPrimitiveIterate a (fun t => c * h t) j s) =
      c * (∫ s in (0 : ℝ)..θ, a s * volterraPrimitiveIterate a h j s)
    rw [← intervalIntegral.integral_const_mul]
    grind

theorem hardyFourierTrace_const_mul (c : ℂ) (h : ℤ → ℂ) (θ : ℝ) :
    hardyFourierTrace (fun n => c * h n) θ = c * hardyFourierTrace h θ := by
  unfold hardyFourierTrace
  simp only [mul_assoc]
  exact tsum_mul_left

theorem hardyFourierTrace_normalizedHardyAverage (b : L2Z) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage b) θ =
      fourierScale⁻¹ * hardyFourierTrace (fromL2 halfOrder b) θ :=
  hardyFourierTrace_const_mul _ _ _

section PhysicalCoordinates

/-- The genuine ordinary coordinate trace is the convergent Volterra
series of its original averaged input. -/
theorem localConformalVekuaBoundary_average_volterra_hasSum_of_H1 (Φ : DiskCoordinates) (E : ℂ)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b))
    (θ : ℝ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j *
      (Φ.map (unitCirclePt θ) - Φ.map 1) ^ j *
      volterraPrimitiveIterate (fun s => star (deriv Φ.boundary s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ)
      (hardyFourierTrace (normalizedHardyAverage
        (Φ.vekuaBoundary E b)) θ) := by
  let c  := fourierScale⁻¹
  have hfun : hardyFourierTrace (normalizedHardyAverage b) =
      fun t => c * hardyFourierTrace (fromL2 halfOrder b) t := by
    funext t
    exact hardyFourierTrace_normalizedHardyAverage b t
  have hs := (localConformalVekuaBoundary_volterra_hasSum_of_H1 Φ E b hbn hb1 θ).mul_left c
  simp only [starRingEnd_apply] at hs
  convert hs using 1
  · funext j
    rw [hfun, volterraPrimitiveIterate_const_mul]
    ring
  · exact hardyFourierTrace_normalizedHardyAverage _ θ

end PhysicalCoordinates

end PolyaNeumann

end
