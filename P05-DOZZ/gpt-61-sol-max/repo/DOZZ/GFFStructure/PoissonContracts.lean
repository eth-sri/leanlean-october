/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonMixture
public import DOZZ.Statements.GFFStructure.ExteriorPinnedEvaluation
import Mathlib.Probability.Moments.Covariance
/-! Shared exact covariance and literal collar-convergence hypotheses for the Poisson family. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Metric Filter Topology
namespace DOZZ.Proofs.Contract

/-- The exact harmonic covariance kernel of a Poisson family. -/
abbrev poissonCovariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (R ρ : ℝ) (V : Ω → ℂ → ℝ) : Prop :=
  ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
    covariance (fun ω => V ω z) (fun ω => V ω w) P =
      Real.log R+Real.log ρ-Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖

/-- Convergence in random L² of the canonical literal Poisson collars. -/
abbrev poissonCollarLimit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (c : ℂ) (R ρ ε : ℝ) (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (V : Ω → ℂ → ℝ) : Prop :=
  ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
    (fun ω => exteriorPinnedEvaluation X Xc R hR ω
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)

end DOZZ.Proofs.Contract
