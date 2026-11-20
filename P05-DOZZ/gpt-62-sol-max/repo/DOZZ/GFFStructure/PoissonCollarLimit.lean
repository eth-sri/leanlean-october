/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.PoissonMixture
public import DOZZ.Statements.GFFStructure.ExteriorPinnedEvaluation
public import Mathlib.Probability.Moments.Covariance

/-! The common limit and covariance conditions for the harmonic field on a disk. -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology

namespace DOZZ.Proofs

/-- The pinned evaluations of the canonical collar tests converge in `L²` to the harmonic field. -/
abbrev IsPoissonCollarLimit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (c : ℂ) (R ρ ε : ℝ)
    (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (V : Ω → ℂ → ℝ) : Prop :=
  ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
    (fun ω => exteriorPinnedEvaluation X Xc R (zero_lt_one.trans hR) ω
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k) - V ω z) 2 P) atTop (𝓝 0)

/-- The harmonic part of the covariance kernel on the disk of center `c` and radius `ρ`. -/
noncomputable abbrev poissonDiskCovariance (c : ℂ) (R ρ : ℝ) (z w : ℂ) : ℝ :=
  Real.log R + Real.log ρ - Real.log ‖(ρ : ℂ)^2 - (z - c) * star (w - c)‖

/-- The pointwise covariance of the harmonic field on the disk. -/
abbrev HasPoissonCovariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℂ) (R ρ : ℝ) (V : Ω → ℂ → ℝ) : Prop :=
  ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
    covariance (fun ω => V ω z) (fun ω => V ω w) P = poissonDiskCovariance c R ρ z w

end DOZZ.Proofs
