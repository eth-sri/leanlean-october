/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianTiltSigned
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Finite-dimensional Gaussian integration by parts from the signed Cameron--Martin identity. -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- Gaussian integration by parts for a smooth function of a finite centered Gaussian vector.
The local domination assumptions are those needed to differentiate both sides of the signed
finite Gaussian tilt identity under the integral. No nondegeneracy assumption on the covariance is
used. -/
theorem finite_gaussian_integration_by_parts
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (i : ι)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (D : (ι → ℝ) → ι → ℝ)
    (hDint : ∀ j, Integrable (fun ω => D (Z ω) j) P)
    (hShiftInt : ∀ t, Integrable
      (fun ω => F (fun j => Z ω j + t *
        gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) P)
    (ε : ℝ) (hε : 0 < ε)
    (hLmeas : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable
      (fun ω => Real.exp (t * Z ω i - t ^ 2 / 2 *
        gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) * F (Z ω)) P)
    (hLint : Integrable
      (fun ω => Real.exp (0 * Z ω i - 0 ^ 2 / 2 *
        gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) * F (Z ω)) P)
    (hLDmeas : AEStronglyMeasurable
      (fun ω => (Z ω i - 0 * gaussianCovariance P (fun ω => Z ω i)
        (fun ω => Z ω i)) * Real.exp (0 * Z ω i - 0 ^ 2 / 2 *
          gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) * F (Z ω)) P)
    (bL : Ω → ℝ) (hLb : Integrable bL P)
    (hLbound : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε,
      ‖(Z ω i - t * gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) *
        Real.exp (t * Z ω i - t ^ 2 / 2 *
          gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) * F (Z ω)‖ ≤ bL ω)
    (hLdiff : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε,
      HasDerivAt
        (fun s => Real.exp (s * Z ω i - s ^ 2 / 2 *
          gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) * F (Z ω))
        ((Z ω i - t * gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) *
          Real.exp (t * Z ω i - t ^ 2 / 2 *
            gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)) * F (Z ω)) t)
    (hRmeas : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable
      (fun ω => F (fun j => Z ω j + t *
        gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) P)
    (hRderivMeas : AEStronglyMeasurable
      (fun ω => ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        D (Z ω) j) P)
    (bR : Ω → ℝ) (hRb : Integrable bR P)
    (hRbound : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε,
      ‖∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
        D (fun j => Z ω j + t *
          gaussianCovariance P (fun ω' => Z ω' j) (fun ω' => Z ω' i)) j‖ ≤ bR ω)
    (hRdiff : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε,
      HasDerivAt
        (fun s => F (fun j => Z ω j + s *
          gaussianCovariance P (fun ω' => Z ω' j) (fun ω' => Z ω' i)))
        (∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
          D (fun j => Z ω j + t *
            gaussianCovariance P (fun ω' => Z ω' j) (fun ω' => Z ω' i)) j) t) :
    ∫ ω, Z ω i * F (Z ω) ∂P =
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        ∫ ω, D (Z ω) j ∂P := by
  classical
  let c : ℝ := gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)
  let L : ℝ → Ω → ℝ := fun t ω =>
    Real.exp (t * Z ω i - t ^ 2 / 2 * c) * F (Z ω)
  let L' : ℝ → Ω → ℝ := fun t ω =>
    (Z ω i - t * c) * Real.exp (t * Z ω i - t ^ 2 / 2 * c) * F (Z ω)
  let R : ℝ → Ω → ℝ := fun t ω =>
    F (fun j => Z ω j + t * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))
  let R' : ℝ → Ω → ℝ := fun t ω =>
    ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
      D (fun j => Z ω j + t * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i)) j
  have hLmeas' : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable (L t) P := hLmeas
  have hLint' : Integrable (L 0) P := hLint
  have hLDmeas' : AEStronglyMeasurable (L' 0) P := hLDmeas
  have hLbound' : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε, ‖L' t ω‖ ≤ bL ω := hLbound
  have hLdiff' : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε,
      HasDerivAt (L · ω) (L' t ω) t := hLdiff
  have hRmeas' : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable (R t) P := hRmeas
  have hRint' : Integrable (R 0) P := hShiftInt 0
  have hRderivMeas' : AEStronglyMeasurable (R' 0) P := by
    simpa [R', c] using hRderivMeas
  have hRbound' : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε, ‖R' t ω‖ ≤ bR ω := hRbound
  have hRdiff' : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 ε,
      HasDerivAt (R · ω) (R' t ω) t := hRdiff
  have hLderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds 0 hε) hLmeas' hLint' hLDmeas' hLbound' hLb hLdiff'
  have hRderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds 0 hε) hRmeas' hRint' hRderivMeas' hRbound' hRb hRdiff'
  have hTilt (t : ℝ) : ∫ ω, L t ω ∂P = ∫ ω, R t ω ∂P := by
    let a : ι → ℝ := fun j => if j = i then t else 0
    have hlin (ω : Ω) : (∑ j, a j * Z ω j) = t * Z ω i := by
      simp [a]
    have hvar : (∑ k, ∑ j, a k * gaussianCovariance P
        (fun ω => Z ω k) (fun ω => Z ω j) * a j) = t ^ 2 * c := by
      simp [a, c]
      ring
    have hshift (k : ι) : (∑ j, gaussianCovariance P
        (fun ω => Z ω k) (fun ω => Z ω j) * a j) =
          t * gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω i) := by
      simp [a]
      ring
    have hShiftInt' : Integrable (fun ω => F (fun k => Z ω k +
        ∑ j, gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω j) * a j)) P := by
      refine (hShiftInt t).congr ?_
      filter_upwards [] with ω
      congr 2
      funext k
      rw [hshift k]
    calc
      ∫ ω, L t ω ∂P = ∫ ω, Real.exp
          ((∑ j, a j * Z ω j) -
            (∑ k, ∑ j, a k * gaussianCovariance P
              (fun ω => Z ω k) (fun ω => Z ω j) * a j) / 2) * F (Z ω) ∂P := by
                grind
      _ = ∫ ω, F (fun k => Z ω k +
          ∑ j, gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω j) * a j) ∂P :=
            finite_gaussian_tilt_signed P Z hZ a F hF hShiftInt'
      _ = ∫ ω, R t ω ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            congr 2
            funext k
            rw [hshift k]
  have hLhas  := hLderiv.2
  have hRhas  := hRderiv.2
  have heq : (fun t => ∫ ω, L t ω ∂P) = fun t => ∫ ω, R t ω ∂P := by
    funext t
    exact hTilt t
  have hderivEq  := HasDerivAt.unique (heq ▸ hLhas) hRhas
  have hLvalue : (∫ ω, L' 0 ω ∂P) = ∫ ω, Z ω i * F (Z ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [L', c]
  have hRvalue : (∫ ω, R' 0 ω ∂P) =
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        ∫ ω, D (Z ω) j ∂P := by
    have hRzero : R' 0 = fun ω =>
        ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * D (Z ω) j := by
      funext ω
      simp [R']
    rw [hRzero]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    · intro j hj
      exact (hDint j).const_mul _
  grind

end DOZZ.Proofs
