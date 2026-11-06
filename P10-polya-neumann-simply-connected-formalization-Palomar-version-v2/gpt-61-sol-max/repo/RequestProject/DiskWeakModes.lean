module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

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
open scoped InnerProductSpace



def diskHolomorphicH1Test m  :=
  smoothTraceH1 unitDisk
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

def diskAntiholomorphicH1Test m  :=
  smoothTraceH1 unitDisk
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

section
variable (m : ℕ) (u : NeumannH1 unitDisk)
include m u

theorem disk_gradient_form_holomorphicTest :
    (∑ i : Coord, ⟪h1Gradient unitDisk i (diskHolomorphicH1Test m),
      h1Gradient unitDisk i u⟫_ℂ) =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ComplexCurve) (m : ℤ) := by
  have h := disk_h1_fourier_green_pos m u
  assumption

theorem disk_gradient_form_antiholomorphicTest :
    (∑ i : Coord, ⟪h1Gradient unitDisk i (diskAntiholomorphicH1Test m),
      h1Gradient unitDisk i u⟫_ℂ) =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ComplexCurve) (-(m : ℤ)) := by
  have h := disk_h1_fourier_green_neg m u
  assumption

end


private theorem twoPi_fourier_mode n (θ : ℝ) :
    fourier (T := 2 * π) n (θ : AddCircle circlePeriod) =
      Complex.exp ((n : ℂ) * Complex.I * θ) := by
  rw [fourier_coe_apply]
  push_cast
  field_simp

theorem fourierCoeffOn_twoPi_exp (n k : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) k =
      (Pi.single n (1 : ℂ) : FourierSeq) k := by
  have hm : (fun θ : ℝ => Complex.exp ((n : ℂ) * Complex.I * θ)) =
      (fun θ : ℝ => fourier (T := 2 * π) n (θ : AddCircle circlePeriod)) := by
    grind only [twoPi_fourier_mode]
  have hl : AddCircle.liftIoc circlePeriod 0
      (fun θ : ℝ => fourier (T := 2 * π) n (θ : AddCircle circlePeriod)) =
      fourier (T := 2 * π) n := by
    funext q
    change fourier n (((AddCircle.equivIoc circlePeriod 0 q))) = _
    simp_all
  have hc := fourierCoeff_liftIoc_eq (T := 2 * π) (a := 0)
    (fun θ => Complex.exp (n * Complex.I * θ)) k
  simp   at hc
  rw [← hc, hm, hl, fourierCoeff_fourier]

theorem diskHalfTrace_smooth_fourier_test (f : smoothTraceTests) (n : ℤ)
    (hf : ∀ θ, f (unitCircleMap θ) = Complex.exp ((n : ℂ) * Complex.I * θ)) :
    diskHalfTrace (smoothTraceH1 unitDisk f) =
      ((Real.sqrt (sobWeight n) : ℂ) * (Real.sqrt circlePeriod : ℂ)) • stdBasisZ n := by
  have hae : (diskH1Trace (smoothTraceH1 unitDisk f) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval]
      (fun θ => Complex.exp ((n : ℂ) * Complex.I * θ)) := by
    have h := h1BoundaryTrace_smooth_ae unitDisk_bounded isLipschitzDomain_unitDisk
      unitCircle_isBoundaryParam f
    measurability
  have hc := fourierCoeffOn_congr_ae two_pi_pos hae
  apply lp.ext
  funext k
  simp  [boundaryFourier_apply, congrFun hc k, fourierCoeffOn_twoPi_exp, stdBasisZ_apply]
  by_cases hkn : k = n
  · subst k
    simp [sobWeight]
  · simp [hkn]

theorem diskHalfTrace_holomorphicTest (m : ℕ) :
    diskHalfTrace (diskHolomorphicH1Test m) =
      ((Real.sqrt (sobWeight (m : ℤ)) : ℂ) * (Real.sqrt circlePeriod : ℂ)) •
        stdBasisZ (m : ℤ) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskHolomorphicMode m) (unitCircleMap θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ)),
    diskHolomorphicMode_unitCircle]
  simp  

theorem diskHalfTrace_antiholomorphicTest (m : ℕ) :
    diskHalfTrace (diskAntiholomorphicH1Test m) =
      ((Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt circlePeriod : ℂ)) •
        stdBasisZ (-(m : ℤ)) := by
  apply diskHalfTrace_smooth_fourier_test
  intro θ
  change diskHarmonicCutoff (diskAntiholomorphicMode m) (unitCircleMap θ) = _
  rw [diskHarmonicCutoff_eq_closedDisk _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ)),
    diskAntiholomorphicMode_unitCircle]
  simp_all

end PolyaNeumann

end
