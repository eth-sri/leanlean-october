module

public import RequestProject.DiskHalfTrace

/-!
# Harmonic tests in the actual weak disk equation

The compact harmonic extensions are actual H¹ test vectors. Their weak
gradient pairing gives the Fourier coefficients of the genuine trace,
and their normalized half traces are single Fourier basis vectors.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

local instance diskWeakModeTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

local notation "Φ0" => ball 0 1

def diskHolomorphicH1Test (m : ℕ) : NeumannH1 (Φ0) :=
  smoothTraceH1 (Φ0)
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

def diskAntiholomorphicH1Test (m : ℕ) : NeumannH1 (Φ0) :=
  smoothTraceH1 (Φ0)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

theorem diskH1Gradient_holomorphicTest m :
    diskH1Gradient (diskHolomorphicH1Test m) = diskHolomorphicGradient m := rfl

theorem diskH1Gradient_antiholomorphicTest m :
    diskH1Gradient (diskAntiholomorphicH1Test m) = diskAntiholomorphicGradient m := rfl

theorem disk_gradient_form_holomorphicTest m
    u :
    (∑ i : Fin 2, ⟪h1Gradient (Φ0) i (diskHolomorphicH1Test m),
      h1Gradient (Φ0) i u⟫_ℂ) =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (m : ℤ) := by
  have h := disk_h1_fourier_green_pos m u
  rw [← diskH1Gradient_holomorphicTest, PiLp.inner_apply] at h
  exact h

theorem disk_gradient_form_antiholomorphicTest m
    u :
    (∑ i : Fin 2, ⟪h1Gradient (Φ0) i (diskAntiholomorphicH1Test m),
      h1Gradient (Φ0) i u⟫_ℂ) =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (-(m : ℤ)) := by
  have h := disk_h1_fourier_green_neg m u
  rw [← diskH1Gradient_antiholomorphicTest, PiLp.inner_apply] at h
  exact h

theorem fourierCoeffOn_twoPi_exp (n k : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) k =
      (Pi.single n 1 : ℤ → ℂ) k := by
  have hc := fourierCoeff_liftIoc_eq (T := 2 * π) (a := 0)
    (fun θ => Complex.exp (n * Complex.I * θ)) k
  simp at hc
  rw [← hc, show (fun θ : ℝ => Complex.exp (n * Complex.I * θ)) = (fun θ : ℝ => fourier (T := 2 * π) n (θ : AddCircle (2 * π))) by
    funext θ
    exact (show fourier (T := 2 * π) n (θ : AddCircle (2 * π)) = Complex.exp ((n : ℂ) * Complex.I * θ) by
      rw [fourier_coe_apply]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]).symm, show AddCircle.liftIoc (2 * π) 0 (fun θ => fourier (T := 2 * π) n (θ : AddCircle (2 * π))) = fourier (T := 2 * π) n by
    funext q
    exact congrArg (fourier n) ((AddCircle.equivIoc (2 * π) 0).symm_apply_apply q), fourierCoeff_fourier]

theorem diskHalfTrace_smooth_fourier_test (f : smoothTraceTests) (n : ℤ)
    (hf : ∀ θ, f (circleMap 0 1 θ) = Complex.exp (n * Complex.I * θ)) :
    diskHalfTrace (smoothTraceH1 (Φ0) f) =
      ((Real.sqrt (sobWeight n) : ℂ) * (Real.sqrt (2 * π) : ℂ)) • stdBasisZ n := by
  apply lp.ext
  funext k
  simp [boundaryFourier_apply, congrFun (fourierCoeffOn_congr_ae two_pi_pos (show diskH1Trace (smoothTraceH1 (Φ0) f) =ᵐ[volume.restrict (Ioc 0 (2 * π))] (fun θ => Complex.exp (n * Complex.I * θ)) by
    filter_upwards [h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam f] with θ hθ
    exact hθ.trans (hf θ))) k, fourierCoeffOn_twoPi_exp, stdBasisZ_apply]
  by_cases hkn : k = n
  · subst k
    simp [sobWeight]
  · simp [hkn]

theorem diskHalfTrace_holomorphicTest m :
    diskHalfTrace (diskHolomorphicH1Test m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt (2 * π) : ℂ)) •
        stdBasisZ (m : ℤ) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskHolomorphicMode m) (circleMap 0 1 θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ)),
    diskHolomorphicMode_unitCircle]
  simp

theorem diskHalfTrace_antiholomorphicTest m :
    diskHalfTrace (diskAntiholomorphicH1Test m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt (2 * π) : ℂ)) •
        stdBasisZ (-(m : ℤ)) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskAntiholomorphicMode m) (circleMap 0 1 θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ)),
    diskAntiholomorphicMode_unitCircle]
  simp only [Int.cast_neg, Int.cast_natCast]
  congr 1
  ring

end PolyaNeumann

end
