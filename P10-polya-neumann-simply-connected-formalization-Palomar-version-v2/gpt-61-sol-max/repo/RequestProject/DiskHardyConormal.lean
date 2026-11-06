module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalHardyExtension
public import RequestProject.LocalConformalGradient
public import RequestProject.ConormalNormalization

/-!
# Actual Hardy energy and the normalized principal conormal operator

The genuine H¹ mode series is paired with arbitrary H¹ test vectors.
The mode Green identity and the exact half-trace amplitudes identify its
physical energy functional with the bounded principal Fourier operator.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Real InnerProductSpace ComplexConjugate

theorem common_conormal_inner_single x n :
    ⟪x, stdBasisZ n⟫_ℂ = conj (x n) := by
  rw [stdBasisZ_apply, lp.inner_single_right]
  simp 

theorem normalizedConormalPrincipal_single (n : ℤ) :
    normalizedConormalPrincipal (stdBasisZ n) =
      ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) • stdBasisZ n := by
  apply lp.ext
  funext k
  rw [normalizedConormal_principal_apply]
  simp  [stdBasisZ_apply]
  grind

private theorem conormal_scale_cancel m t a
    (ht : t ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ)) :
    ((t : ℂ) * (((m : ℝ) / (1 + (m : ℝ)) : ℝ) : ℂ)) * conj ((t : ℂ) * a) =
      (2 * π : ℂ) * (m : ℂ) * conj a := by
  have hm : (1 + (m : ℝ)) ≠ 0 := by positivity
  have hr : t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) = 2 * π * (m : ℝ) := by
    grind
  calc
    _ = ((t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) : ℝ)) * conj a := by
      simp  
      ring
    _ = _ := by rw [hr]; push_cast; ring

private theorem conormal_halfTrace_neg w (m : ℕ) :
    diskHalfTrace w (-(m : ℤ)) = (diskHardyTraceScale m : ℂ) *
      fourierCoeffOn Real.two_pi_pos (diskH1Trace w : ComplexCurve) (-(m : ℤ)) := by
  rw [diskHalfTrace_apply, boundaryFourier_apply]
  simp  [diskHardyTraceScale, sobWeight]
  ring

theorem diskAntiholomorphicH1Test_principal_conormal m
    w :
    (∑ i : Coord, ⟪h1Gradient unitDisk i w,
      h1Gradient unitDisk i (diskAntiholomorphicH1Test m)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal
        (diskHalfTrace (diskAntiholomorphicH1Test m))⟫_ℂ := by
  have hg := congrArg conj (disk_gradient_form_antiholomorphicTest m w)
  simp only [map_sum, inner_conj_symm, map_mul, Complex.conj_ofReal,
    Complex.conj_natCast, map_ofNat] at hg
  rw [hg, diskHalfTrace_antiholomorphicTest, map_smul,
    normalizedConormalPrincipal_single, smul_smul, inner_smul_right,
    common_conormal_inner_single, conormal_halfTrace_neg]
  have ha : |-(m : ℝ)| = (m : ℝ) := by
    simp_all
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [ha]
  have hs : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      (Real.sqrt circlePeriod : ℂ) = (diskHardyTraceScale m : ℂ) := by
    simp  [diskHardyTraceScale]
  rw [hs, conormal_scale_cancel m _ _ (diskHardyTraceScale_sq m)]

def h1GradientPairRight (Ω : PlanarSet) (w : NeumannH1 Ω) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (h1GradientVector Ω w)).comp (h1GradientVector Ω)

theorem h1GradientPairRight_apply Ω w u :
    h1GradientPairRight Ω w u =
      ∑ i : Coord, ⟪h1Gradient Ω i w, h1Gradient Ω i u⟫_ℂ := rfl

theorem diskHardyExtension_principal_conormal b
    w :
    (∑ i : Coord, ⟪h1Gradient unitDisk i w,
      h1Gradient unitDisk i (diskHardyExtension b)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  let A := h1GradientPairRight (ball 0 1) w
  let B := (innerSL ℂ (diskHalfTrace w)).comp
    (normalizedConormalPrincipal.comp diskHalfTrace)
  have hm (m : ℕ) : A (diskAntiholomorphicH1Test m) =
      B (diskAntiholomorphicH1Test m) := by
    solve_by_elim (maxDepth := 2) [h1GradientPairRight, diskHalfTrace, normalizedConormalPrincipal, h1GradientPairRight_apply, diskAntiholomorphicH1Test_principal_conormal]
  have hA := A.hasSum (diskHardyExtension_hasSum b)
  have hB := B.hasSum (diskHardyExtension_hasSum b)
  have h := (hA.congr_fun (fun m => by simp [hm])).unique hB
  change h1GradientPairRight (ball 0 1) w (diskHardyExtension b) =
    ⟪diskHalfTrace w, normalizedConormalPrincipal (diskHalfTrace (diskHardyExtension b))⟫_ℂ at h
  simpa only [h1GradientPairRight_apply, diskHalfTrace_diskHardyExtension] using h

section PhysicalCoordinate

variable {R C K } (hR : 1 < R) (F )
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

theorem localConformalHardyH1Extension_principal_conormal b
    w :
    (∑ i : Coord, ⟪h1Gradient (F '' unitDisk) i w,
      h1Gradient (F '' unitDisk) i
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes b)⟫_ℂ) =
      ⟪localConformalDiskHalfTrace hR F hFs hL w,
        normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  rw [← localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC,
    localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_principal_conormal b (localConformalH1Pullback hR F hFs hL w)

end PhysicalCoordinate

end PolyaNeumann

end
