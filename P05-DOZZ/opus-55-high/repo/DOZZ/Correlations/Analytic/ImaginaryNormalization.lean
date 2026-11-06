/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedIncrementTilt

/-! The deterministic factor in the complex tilt depends only on imaginary charges. -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)

/-- The real part of joint Wick normalization is the difference of the real and imaginary
coordinate variances. -/
theorem jointVertexPolynomial_re
    (z : Fin N → ℂ) (r : Fin N → ℝ)
    (hm : ∀ i, MemLp (fun ω => Xc ω (z i) (r i)) 2 P) (β : Fin N → ℂ) :
    (jointVertexPolynomial P Xc z r β).re =
      -gaussianVariance P (fun ω => ∑ i, (β i).re * Xc ω (z i) (r i)) / 2 +
        gaussianVariance P (fun ω => ∑ i, (β i).im * Xc ω (z i) (r i)) / 2 := by
  rw [vertex_variance_expansion P _ hm (fun i => (β i).re),
    vertex_variance_expansion P _ hm (fun i => (β i).im)]
  unfold jointVertexPolynomial
  simp
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- The real charge and real mass-power contributions cancel exactly in the norm tilt. -/
theorem normalized_imaginary_factor
    (hm : ∀ z r, MemLp (fun ω => Xc ω z r) 2 P)
    (γ : ℝ) (z : Fin N → ℂ) (r : ℝ) (β : Fin (N + 1) → ℂ) :
    (normalizedVertexPolynomial P Xc γ z r β).re +
        gaussianVariance P (fun ω => ∑ i, (β i).re *
          Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)) / 2 +
        (γ * ∑ i, (β i.castSucc).re * equatorCircleMean (z i) r) *
          (complexMomentPower γ β).re =
      gaussianVariance P (fun ω => ∑ i, (β i).im *
        Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)) / 2 +
        γ * (complexMomentPower γ β).im *
          ∑ i, (β i.castSucc).im * equatorCircleMean (z i) r := by
  unfold normalizedVertexPolynomial
  rw [Complex.sub_re, jointVertexPolynomial_re P Xc _ _ (fun i => hm ..) β]
  simp
  ring

end

end DOZZ.Proofs
