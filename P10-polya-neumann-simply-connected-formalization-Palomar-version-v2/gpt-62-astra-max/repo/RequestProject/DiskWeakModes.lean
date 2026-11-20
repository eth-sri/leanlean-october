module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskHalfTrace
public import RequestProject.PlanarNotation

/-!
# Harmonic tests in the actual weak disk equation

The compact harmonic extensions are actual H¹ test vectors. Their weak
gradient pairing gives the Fourier coefficients of the genuine trace,
and their normalized half traces are single Fourier basis vectors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

section

variable (m : ℕ) (f : smoothTraceTests) (u : NeumannH1 unitDisk) (n : ℤ)

include m in
def diskHolomorphicH1Test : NeumannH1 unitDisk :=
  smoothTraceH1 unitDisk
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

include m in
def diskAntiholomorphicH1Test : NeumannH1 unitDisk :=
  smoothTraceH1 unitDisk
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

theorem diskH1Gradient_holomorphicTest :
    diskH1Gradient (diskHolomorphicH1Test m) = diskHolomorphicGradient m := rfl

theorem diskH1Gradient_antiholomorphicTest :
    diskH1Gradient (diskAntiholomorphicH1Test m) = diskAntiholomorphicGradient m := rfl

theorem disk_gradient_form_holomorphicTest :
    (∑ i : Fin 2, ⟪h1Gradient unitDisk i (diskHolomorphicH1Test m),
      h1Gradient unitDisk i u⟫_ℂ) =
      (anglePeriod : ℂ) * (m : ℂ) *
        angleCoeff (diskH1Trace u : ℝ → ℂ) (m : ℤ) := disk_h1_fourier_green_pos m u

theorem disk_gradient_form_antiholomorphicTest :
    (∑ i : Fin 2, ⟪h1Gradient unitDisk i (diskAntiholomorphicH1Test m),
      h1Gradient unitDisk i u⟫_ℂ) =
      (anglePeriod : ℂ) * (m : ℂ) *
        angleCoeff (diskH1Trace u : ℝ → ℂ) (-(m : ℤ)) := disk_h1_fourier_green_neg m u

private theorem twoPi_fourier_mode (θ : ℝ) :
    fourier  n (θ : ParamCircle) =
      Complex.exp ((n : ℂ) * Complex.I * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem fourierCoeffOn_twoPi_exp (k : ℤ) :
    angleCoeff (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) k =
      (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
  have hm : (fun θ : ℝ => Complex.exp (n * Complex.I * θ)) =
      (fun θ : ℝ => fourier  n (θ : ParamCircle)) := by
    funext θ
    exact (twoPi_fourier_mode n θ).symm
  have hl : AddCircle.liftIoc anglePeriod 0
      (fun θ : ℝ => fourier  n (θ : ParamCircle)) =
      fourier  n := by
    funext q
    exact congrArg (fourier n) ((AddCircle.equivIoc anglePeriod 0).symm_apply_apply q)
  have hc := fourierCoeff_liftIoc_eq (T := anglePeriod) (a := 0)
    (fun θ => Complex.exp (n * Complex.I * θ)) k
  simp at hc
  rw [← hc, hm, hl, fourierCoeff_fourier]

theorem diskHalfTrace_smooth_fourier_test
    (hf : ∀ θ, f (unitCirclePt θ) = Complex.exp ((n : ℂ) * Complex.I * θ)) :
    diskHalfTrace (smoothTraceH1 unitDisk f) =
      ((Real.sqrt (sobWeight n) : ℂ) * fourierScale) • stdBasisZ n := by
  have hae : (diskH1Trace (smoothTraceH1 unitDisk f))
      =ᵐ[angleMeasure]
      (fun θ => Complex.exp (n * Complex.I * θ)) := by
    
    filter_upwards [(h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
      unitCircle_isBoundaryParam f)] with θ hθ
    exact hθ.trans (hf θ)
  have hc := fourierCoeffOn_congr_ae two_pi_pos hae
  ext k
  simp only [diskHalfTrace_apply, boundaryFourier_apply, congrFun hc k, fourierCoeffOn_twoPi_exp, stdBasisZ_apply, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases hkn : k = n
  · subst k
    simp [sobWeight]
  · simp [hkn]

theorem diskHalfTrace_holomorphicTest :
    diskHalfTrace (diskHolomorphicH1Test m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * fourierScale) •
        stdBasisZ (m : ℤ) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskHolomorphicMode m) (unitCirclePt θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (by norm_num),
    diskHolomorphicMode_unitCircle]
  rfl

theorem diskHalfTrace_antiholomorphicTest :
    diskHalfTrace (diskAntiholomorphicH1Test m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * fourierScale) •
        stdBasisZ (-(m : ℤ)) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskAntiholomorphicMode m) (unitCirclePt θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (by norm_num),
    diskAntiholomorphicMode_unitCircle]
  simp

end

end PolyaNeumann

end
