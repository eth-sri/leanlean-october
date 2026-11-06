/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
public import DOZZ.GMC.GaussianTailBound

/-! Coarse-scale barrier tails for admissible logarithmic Gaussian regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The same-center coarse variance and mixed covariance bounds in an admissible logarithmic
regularization give a uniform one-root barrier tail under a fine-scale Wick tilt. -/
theorem admissible_coarse_barrier_tail_rate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ ε₀ → C < (k : ℝ) →
      ∀ x ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(k : ℝ)) →
      ∀ g a : ℝ, 0 < g → g < a → g * C ≤ (a - g) * (k : ℝ) / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * Y ω ε x - g ^ 2 / 2 * gaussianVariance P (fun ω => Y ω ε x))) *
        (Set.indicator {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x}
          (fun _ => (1 : ℝ≥0∞)) ω) ∂P ≤
        ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
  obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
  obtain ⟨Cm, hCm, hmix⟩ := hY.coarseMixedBound K hK hKU
  let C := max Cv Cm
  have hCnonneg : 0 ≤ C := by positivity
  refine ⟨C, hCnonneg, ?_⟩
  intro k hkcut hCk x hx ε hε hεk g a hg hga hgap
  let p : Fin 2 → ℝ × ℂ := fun i =>
    if i = 0 then (Real.exp (-k), x) else (ε, x)
  let Z : Ω → Fin 2 → ℝ := fun ω i => Y ω (p i).1 (p i).2
  have hZ : IsCenteredJointlyGaussian P Z := by
    apply hY.gaussian 2 p
    intro i
    fin_cases i <;> grind
  have hvarZ : |gaussianVariance P (fun ω => Z ω 0) - k| ≤ C := by
    have h' : |gaussianVariance P (fun ω => Z ω 0) - k| ≤ max Cv Cm := by
      simpa [Z, p] using (hvar k hkcut x hx).trans (le_max_left Cv Cm)
    simpa [C] using h'
  have hcovZ : |gaussianCovariance P (fun ω => Z ω 0)
      (fun ω => Z ω 1) - k| ≤ C := by
    have h' : |gaussianCovariance P (fun ω => Z ω 0)
        (fun ω => Z ω 1) - k| ≤ max Cv Cm := by
      simpa [Z, p] using (hmix k hkcut ε hε hεk x hx).trans (le_max_right Cv Cm)
    simpa [C] using h'
  have hbound := finite_gaussian_tilt_coarse_barrier_tail_rate P Z hZ
    1 0 k g a C hg hga (lt_of_le_of_lt hCnonneg hCk)
    hCk hvarZ hcovZ hgap
  simpa [Z, p] using hbound

end DOZZ.Proofs
