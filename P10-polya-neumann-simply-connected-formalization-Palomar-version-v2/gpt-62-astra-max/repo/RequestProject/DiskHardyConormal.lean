module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalHardyExtension
public import RequestProject.LocalConformalGradient
public import RequestProject.ConormalNormalization
public import RequestProject.MatrixHSSymmetry
public import RequestProject.PlanarNotation

/-!
# Actual Hardy energy and the normalized principal conormal operator

The genuine H¹ mode series is paired with arbitrary H¹ test vectors.
The mode Green identity and the exact half-trace amplitudes identify its
physical energy functional with the bounded principal Fourier operator.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Metric
open scoped Real InnerProductSpace ComplexConjugate

section

variable (m : ℕ) (b : L2Z) (w : NeumannH1 unitDisk) (Ω : Set ℂ)

theorem normalizedConormalPrincipal_single (n : ℤ) :
    normalizedConormalPrincipal (stdBasisZ n) =
      ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) • stdBasisZ n := by
  apply lp.ext
  funext k
  rw [normalizedConormal_principal_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, stdBasisZ_apply, lp.single_apply]
  by_cases hkn : k = n
  · subst k
    simp
  · simp [hkn]

private theorem conormal_scale_cancel (t : ℝ) (a : ℂ)
    (ht : t ^ 2 = anglePeriod * ((m + 1 : ℕ) : ℝ)) :
    ((t : ℂ) * (((m : ℝ) / (1 + (m : ℝ)) : ℝ) : ℂ)) * conj ((t : ℂ) * a) =
      (anglePeriod : ℂ) * (m : ℂ) * conj a := by
  have hm : (1 + m) ≠ 0 := by positivity
  have hr : t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) = anglePeriod * (m : ℝ) := by
    rw [ht]
    push_cast
    field_simp [hm]
    ring
  calc
    _ = ((t ^ 2 * (m / (1 + m)) : ℝ) : ℂ) * conj a := by
      simp <;> ring
    _ = _ := by simp [hr]

private theorem conormal_halfTrace_neg (m : ℕ) :
    diskHalfTrace w (-(m : ℤ)) = (diskHardyTraceScale m : ℂ) *
      angleCoeff (diskH1Trace w : ℝ → ℂ) (-(m : ℤ)) := by
  rw [diskHalfTrace_apply, boundaryFourier_apply]
  simp only [diskHardyTraceScale, sobWeight, Complex.ofReal_mul]
  ring

theorem diskAntiholomorphicH1Test_principal_conormal :
    (∑ i : Fin 2, ⟪h1Gradient unitDisk i w,
      h1Gradient unitDisk i (diskAntiholomorphicH1Test m)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal
        (diskHalfTrace (diskAntiholomorphicH1Test m))⟫_ℂ := by
  have hg := congrArg conj (disk_gradient_form_antiholomorphicTest m w)
  simp only [map_sum, inner_conj_symm, map_mul, Complex.conj_ofReal,
    Complex.conj_natCast, map_ofNat] at hg
  rw [hg, diskHalfTrace_antiholomorphicTest, map_smul,
    normalizedConormalPrincipal_single, smul_smul, inner_smul_right,
    matrix_inner_std_right, conormal_halfTrace_neg]
  have ha : |-(m : ℝ)| = (m : ℝ) := by
    simp
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [ha]
  have hs : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      fourierScale = (diskHardyTraceScale m : ℂ) := by
    simp [diskHardyTraceScale, Complex.ofReal_mul]
  rw [hs, conormal_scale_cancel m _ _ (diskHardyTraceScale_sq m)]

def h1GradientPairRight (w : NeumannH1 Ω) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (h1GradientVector Ω w)).comp (h1GradientVector Ω)

theorem h1GradientPairRight_apply (w u : NeumannH1 Ω) :
    h1GradientPairRight Ω w u =
      ∑ i : Fin 2, ⟪h1Gradient Ω i w, h1Gradient Ω i u⟫_ℂ := rfl

theorem diskHardyExtension_principal_conormal :
    (∑ i : Fin 2, ⟪h1Gradient unitDisk i w,
      h1Gradient unitDisk i (diskHardyExtension b)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  let A := h1GradientPairRight unitDisk w
  let B := (innerSL ℂ (diskHalfTrace w)).comp
    (normalizedConormalPrincipal.comp diskHalfTrace)
  have hm (m : ℕ) : A (diskAntiholomorphicH1Test m) =
      B (diskAntiholomorphicH1Test m) := by
    exact diskAntiholomorphicH1Test_principal_conormal m w
  have hA := A.hasSum (diskHardyExtension_hasSum b)
  
  have he : (fun m : ℕ => A ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m)) =
      (fun m : ℕ => B ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m)) := by
    simp only [map_smul, hm]
  rw [he] at hA
  have h := hA.unique (B.hasSum (diskHardyExtension_hasSum b))
  change h1GradientPairRight unitDisk w (diskHardyExtension b) =
    ⟪diskHalfTrace w, normalizedConormalPrincipal (diskHalfTrace (diskHardyExtension b))⟫_ℂ at h
  simpa [h1GradientPairRight_apply, diskHalfTrace_diskHardyExtension] using h

end

section PhysicalCoordinate

theorem localConformalHardyH1Extension_principal_conormal (Φ : DiskCoordinates) (b : L2Z)
    (w : NeumannH1 Φ.domain) :
    (∑ i : Fin 2, ⟪h1Gradient Φ.domain i w,
      h1Gradient Φ.domain i
        (Φ.hardyH1Extension b)⟫_ℂ) =
      ⟪Φ.pulledBackHalfTrace Φ.lipschitzDomain w,
        normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  rw [← localConformalH1Pullback_gradient_inner Φ,
    localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_principal_conormal b (Φ.h1Pullback Φ.lipschitzDomain w)

end PhysicalCoordinate

end PolyaNeumann

end
