module

public import RequestProject.DiskHalfTrace

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

local instance diskWeakModeTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

def diskHolomorphicH1Test (m : ℕ) : NeumannH1 (ball (0 : ℂ) 1) :=
  smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

def diskAntiholomorphicH1Test (m : ℕ) : NeumannH1 (ball (0 : ℂ) 1) :=
  smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

variable (m : ℕ) (u : NeumannH1 (ball 0 1)) (n : ℤ)

theorem diskH1Gradient_holomorphicTest :
    diskH1Gradient (diskHolomorphicH1Test m) = diskHolomorphicGradient m := rfl

theorem diskH1Gradient_antiholomorphicTest :
    diskH1Gradient (diskAntiholomorphicH1Test m) = diskAntiholomorphicGradient m := rfl

theorem disk_gradient_form_holomorphicTest :
    (∑ i : Fin 2, ⟪h1Gradient (ball 0 1) i (diskHolomorphicH1Test m),
      h1Gradient (ball 0 1) i u⟫_ℂ) =
      2 * π * m *
        fourierCoeffOn two_pi_pos (diskH1Trace u) m := by
  have h := disk_h1_fourier_green_pos m u
  assumption

theorem disk_gradient_form_antiholomorphicTest :
    (∑ i : Fin 2, ⟪h1Gradient (ball 0 1) i (diskAntiholomorphicH1Test m),
      h1Gradient (ball 0 1) i u⟫_ℂ) =
      2 * π * m *
        fourierCoeffOn two_pi_pos (diskH1Trace u) (-m) := by
  have h := disk_h1_fourier_green_neg m u
  assumption

private theorem twoPi_fourier_mode (θ : ℝ) :
    fourier (T := 2 * π) n (θ : AddCircle (2 * π)) =
      Complex.exp ((n : ℂ) * Complex.I * θ) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem fourierCoeffOn_twoPi_exp (n k : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => Complex.exp (n * Complex.I * θ)) k =
      (Pi.single n 1 : ℤ → ℂ) k := by
  have hm : (fun θ : ℝ => Complex.exp (n * Complex.I * θ)) =
      (fun θ : ℝ => fourier (T := 2 * π) n θ) := by
    funext θ
    exact (twoPi_fourier_mode n θ).symm
  have hl : AddCircle.liftIoc (2 * π) 0
      (fun θ  => fourier (T := 2 * π) n θ) =
      fourier  n := by
    funext q
    change fourier n (AddCircle.equivIoc (2 * π) 0 q) = _
    norm_num
  have hc := fourierCoeff_liftIoc_eq (T := 2 * π) (a := 0)
    (fun θ => Complex.exp (n * Complex.I * θ)) k
  simp_all [fourierCoeff_fourier]

theorem diskHalfTrace_smooth_fourier_test (f : smoothTraceTests) (n : ℤ)
    (hf : ∀ θ, f (circleMap 0 1 θ) = Complex.exp (n * Complex.I * θ)) :
    diskHalfTrace (smoothTraceH1 (ball 0 1) f) =
      ((Real.sqrt (sobWeight n) : ℂ) * Real.sqrt (2 * π)) • stdBasisZ n := by
  have hae : diskH1Trace (smoothTraceH1 (ball 0 1) f)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun θ => Complex.exp (n * Complex.I * θ)) := by
    filter_upwards [h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
      unitCircle_isBoundaryParam f] with θ hθ
    exact hθ.trans (hf θ)
  apply lp.ext
  funext k
  simp only [diskHalfTrace_apply, boundaryFourier_apply,
    congrFun (fourierCoeffOn_congr_ae two_pi_pos hae) k, fourierCoeffOn_twoPi_exp, stdBasisZ_apply]
  by_cases hkn : k = n
  all_goals simp_all [sobWeight]

theorem diskHalfTrace_holomorphicTest :
    diskHalfTrace (diskHolomorphicH1Test m) =
      ((Real.sqrt (sobWeight m) : ℂ) * Real.sqrt (2 * π)) •
        stdBasisZ m := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  simp [diskHarmonicCutoff_eq_closedDisk _     (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ)), diskHolomorphicMode_unitCircle] 

theorem diskHalfTrace_antiholomorphicTest :
    diskHalfTrace (diskAntiholomorphicH1Test m) =
      ((Real.sqrt (sobWeight (-m)) : ℂ) * Real.sqrt (2 * π)) •
        stdBasisZ (-m) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  simp [diskHarmonicCutoff_eq_closedDisk _     (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ)), diskAntiholomorphicMode_unitCircle]

end PolyaNeumann

end
