/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionParameterDomain
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Successive one-variable continuation on the nonresonant Gauss parameter domain. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- The integer lattice excluded by the two connection exponents. -/
def gaussConnectionIntegerRange : Set ℂ := Set.range fun n : ℤ => (n : ℂ)

/-- Convert the product coordinates `(c, δ, a)` to the source parameter order `(a,b,c)`. -/
def gaussConnectionCoordinates (c δ a : ℂ) : ℂ × ℂ × ℂ :=
  (a, c - δ - a, c)

/-- Analyticity along each of the coordinates which straighten the nonresonant domain. -/
theorem analytic_gaussConnection_slices
    {k : ℂ × ℂ × ℂ → ℂ}
    (hk : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ k p)
    {S T V : Set ℂ} (hSo : IsOpen S) (hTo : IsOpen T) (hVo : IsOpen V)
    (hSI : S ⊆ gaussConnectionIntegerRangeᶜ) (hTI : T ⊆ gaussConnectionIntegerRangeᶜ) :
    (∀ δ a, δ ∈ T → AnalyticOnNhd ℂ (fun c => k (gaussConnectionCoordinates c δ a)) S) ∧
    (∀ c a, c ∈ S → AnalyticOnNhd ℂ (fun δ => k (gaussConnectionCoordinates c δ a)) T) ∧
    (∀ c δ, c ∈ S → δ ∈ T →
      AnalyticOnNhd ℂ (fun a => k (gaussConnectionCoordinates c δ a)) V) := by
  have hp (c δ a : ℂ) (hc : c ∈ S) (hδ : δ ∈ T) :
      gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
    simpa [gaussConnectionCoordinates, gaussConnectionParameterDomain,
      gaussConnectionIntegerRange, eq_comm] using And.intro (hSI hc) (hTI hδ)
  refine ⟨?_, ?_, ?_⟩
  · intro δ a hδ
    apply DifferentiableOn.analyticOnNhd _ hSo
    intro c hc
    exact ((hk _ (hp c δ a hc hδ)).comp c
      (by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
  · intro c a hc
    apply DifferentiableOn.analyticOnNhd _ hTo
    intro δ hδ
    exact ((hk _ (hp c δ a hc hδ)).comp δ
      (by dsimp [gaussConnectionCoordinates]; fun_prop)).differentiableWithinAt
  · intro c δ hc hδ
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro a _
    exact ((hk _ (hp c δ a hc hδ)).comp a
      (by change DifferentiableAt ℂ (fun x => (x, c - δ - x, c)) a;
          fun_prop)).differentiableWithinAt

end DOZZ.Proofs
