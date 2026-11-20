module

public import RequestProject.ConformalDiskCoordinates

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Real InnerProductSpace ComplexConjugate

private theorem conormal_inner_single (x : L2Z) (n : ℤ) :
    ⟪x, stdBasisZ n⟫_ℂ = conj (x n) := by simp_all [stdBasisZ_apply, lp.inner_single_right]

theorem normalizedConormalPrincipal_single (n : ℤ) :
    normalizedConormalPrincipal (stdBasisZ n) =
      ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) • stdBasisZ n := by
  apply lp.ext
  funext k
  rw [normalizedConormal_principal_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, stdBasisZ_apply, lp.single_apply]
  grind

private theorem conormal_scale_cancel (m : ℕ) (t : ℝ) (a : ℂ)
    (ht : t ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ)) :
    ((t : ℂ) * (((m : ℝ) / (1 + (m : ℝ)) : ℝ) : ℂ)) * conj ((t : ℂ) * a) =
      (2 * π : ℂ) * (m : ℂ) * conj a := by
  have hm : (1 + (m : ℝ)) ≠ 0 := by positivity
  have hr : t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) = 2 * π * (m : ℝ) := by
    grind
  calc
    _ = ((t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) : ℝ) : ℂ) * conj a := by
      simp only [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    _ = _ := by simp_all

private theorem conormal_halfTrace_neg (w : NeumannH1 (ball (0 : ℂ) 1)) (m : ℕ) :
    diskHalfTrace w (-(m : ℤ)) = (diskHardyTraceScale m : ℂ) *
      fourierCoeffOn Real.two_pi_pos (diskH1Trace w : ℝ → ℂ) (-(m : ℤ)) := by
  rw [diskHalfTrace_apply, boundaryFourier_apply]
  simp only [diskHardyTraceScale, sobWeight, Complex.ofReal_mul]
  ring

theorem diskAntiholomorphicH1Test_principal_conormal (m : ℕ)
    (w : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i w,
      h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal
        (diskHalfTrace (diskAntiholomorphicH1Test m))⟫_ℂ := by
  have hg := congrArg conj (disk_gradient_form_antiholomorphicTest m w)
  simp only [map_sum, inner_conj_symm, map_mul, Complex.conj_ofReal,
    Complex.conj_natCast, map_ofNat] at hg
  rw [hg, diskHalfTrace_antiholomorphicTest, map_smul,
    normalizedConormalPrincipal_single, smul_smul, inner_smul_right,
    conormal_inner_single, conormal_halfTrace_neg]
  have ha : |-(m : ℝ)| = (m : ℝ) := by
    simp
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [ha]
  have hs : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      (Real.sqrt (2 * π) : ℂ) = (diskHardyTraceScale m : ℂ) := by
    norm_cast
  rw [hs, conormal_scale_cancel m _ _ (diskHardyTraceScale_sq m)]

def h1GradientPairRight (Ω : Set ℂ) (w : NeumannH1 Ω) : NeumannH1 Ω →L[ℂ] ℂ :=
  (innerSL ℂ (h1GradientVector Ω w)).comp (h1GradientVector Ω)

theorem h1GradientPairRight_apply (Ω : Set ℂ) (w u : NeumannH1 Ω) :
    h1GradientPairRight Ω w u =
      ∑ i : Fin 2, ⟪h1Gradient Ω i w, h1Gradient Ω i u⟫_ℂ := by rfl

theorem diskHardyExtension_principal_conormal (b : L2Z)
    (w : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i w,
      h1Gradient (ball (0 : ℂ) 1) i (diskHardyExtension b)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  let A := h1GradientPairRight (ball (0 : ℂ) 1) w
  let B := (innerSL ℂ (diskHalfTrace w)).comp
    (normalizedConormalPrincipal.comp diskHalfTrace)
  have hm (m : ℕ) : A (diskAntiholomorphicH1Test m) =
      B (diskAntiholomorphicH1Test m) := by
    change h1GradientPairRight (ball (0 : ℂ) 1) w _ =
      ⟪diskHalfTrace w, normalizedConormalPrincipal (diskHalfTrace _)⟫_ℂ
    rw [h1GradientPairRight_apply]
    exact diskAntiholomorphicH1Test_principal_conormal m w
  have hA := A.hasSum (diskHardyExtension_hasSum b)
  have hB := B.hasSum (diskHardyExtension_hasSum b)
  have he : (fun m : ℕ => A ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m)) =
      (fun m : ℕ => B ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m)) := by
    simp_all
  rw [he] at hA
  have h := hA.unique hB
  change h1GradientPairRight (ball (0 : ℂ) 1) w (diskHardyExtension b) =
    ⟪diskHalfTrace w, normalizedConormalPrincipal (diskHalfTrace (diskHardyExtension b))⟫_ℂ at h
  simpa only [h1GradientPairRight_apply, diskHalfTrace_diskHardyExtension] using h

section PhysicalCoordinate

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

theorem localConformalHardyH1Extension_principal_conormal (b : L2Z)
    (w : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (F '' ball (0 : ℂ) 1) i w,
      h1Gradient (F '' ball (0 : ℂ) 1) i
        (localConformalHardyH1Extension coords b)⟫_ℂ) =
      ⟪coords.halfTrace w,
        normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  rw [← localConformalH1Pullback_gradient_inner coords,
    localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_principal_conormal b (coords.pullback w)

end PhysicalCoordinate

end PolyaNeumann

end
