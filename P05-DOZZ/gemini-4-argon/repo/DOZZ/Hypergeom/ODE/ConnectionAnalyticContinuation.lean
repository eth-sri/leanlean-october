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

/-- Equality of two parameter-differentiable functions on one open Euler box propagates to the
whole nonresonant connection domain. The proof uses only one-variable identity theorems, in the
coordinates `(c, δ, a)` where the domain is `(ℂ \ ℤ) × (ℂ \ ℤ) × ℂ`. -/
theorem eq_of_eq_on_open_gaussConnection_box
    {f g : ℂ × ℂ × ℂ → ℂ}
    (hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p)
    (hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p)
    {S T V} {c₀ δ₀ a₀}
    (hSopen : IsOpen S) (hTopen : IsOpen T) (hVopen : IsOpen V)
    (hc₀ : c₀ ∈ S) (hδ₀ : δ₀ ∈ T) (ha₀ : a₀ ∈ V)
    (hS : S ⊆ gaussConnectionIntegerRangeᶜ)
    (hT : T ⊆ gaussConnectionIntegerRangeᶜ)
    (hEq : ∀ c ∈ S, ∀ δ ∈ T, ∀ a ∈ V,
      f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a))
    {a b c} (hp : (a, b, c) ∈ gaussConnectionParameterDomain) :
    f (a, b, c) = g (a, b, c) := by
  have gaussNonintegerDomain_isPreconnected : IsPreconnected gaussConnectionIntegerRangeᶜ := by
    have hcount : gaussConnectionIntegerRange.Countable :=
      Set.countable_range fun n : ℤ => (n : ℂ)
    have hpath : IsPathConnected gaussConnectionIntegerRangeᶜ :=
      Set.Countable.isPathConnected_compl_of_one_lt_rank
        (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) hcount
    exact hpath.isConnected.isPreconnected
  have gaussNonintegerDomain_isOpen := (show IsClosed gaussConnectionIntegerRange by exact Complex.isometry_intCast.isClosedEmbedding.isClosed_range).isOpen_compl
  let F : ℂ → ℂ → ℂ → ℂ := fun c δ a =>
    f (gaussConnectionCoordinates c δ a)
  let G : ℂ → ℂ → ℂ → ℂ := fun c δ a =>
    g (gaussConnectionCoordinates c δ a)
  have hFdiff c δ a (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => F x δ a) c := (hf _ (by simpa [F, gaussConnectionCoordinates, gaussConnectionParameterDomain] using (by simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ))).comp c (by dsimp [gaussConnectionCoordinates]; fun_prop)
  have hGdiff c δ a (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => G x δ a) c := (hg _ (by simpa [G, gaussConnectionCoordinates, gaussConnectionParameterDomain] using (by simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ))).comp c (by dsimp [gaussConnectionCoordinates]; fun_prop)
  have hFδdiff c δ a (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => F c x a) δ := (hf _ (by simpa [F, gaussConnectionCoordinates, gaussConnectionParameterDomain] using (by simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ))).comp δ (by dsimp [gaussConnectionCoordinates]; fun_prop)
  have hGδdiff c δ a (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => G c x a) δ := (hg _ (by simpa [G, gaussConnectionCoordinates, gaussConnectionParameterDomain] using (by simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ))).comp δ (by dsimp [gaussConnectionCoordinates]; fun_prop)
  have hFanalyticC δ a (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => F x δ a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hFdiff x δ a hx hδ).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hGanalyticC δ a (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => G x δ a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hGdiff x δ a hx hδ).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hFanalyticδ c a (hc : c ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => F c x a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hFδdiff c x a hc hx).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hGanalyticδ c a (hc : c ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => G c x a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hGδdiff c x a hc hx).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hC δ (hδ : δ ∈ T) a (ha : a ∈ V) :
      ∀ c ∈ gaussConnectionIntegerRangeᶜ, F c δ a = G c δ a := by
    intro c hc
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hFanalyticC δ a (hT hδ)) (hGanalyticC δ a (hT hδ)) gaussNonintegerDomain_isPreconnected (hS hc₀) (by filter_upwards [hSopen.mem_nhds hc₀] with x hx; exact hEq x hx δ hδ a ha)) hc
  have hDelta c (hc : c ∈ gaussConnectionIntegerRangeᶜ) :
      ∀ δ ∈ gaussConnectionIntegerRangeᶜ, ∀ a ∈ V, F c δ a = G c δ a := by
    intro δ hδ a ha
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hFanalyticδ c a hc) (hGanalyticδ c a hc) gaussNonintegerDomain_isPreconnected
      (hT hδ₀) (by filter_upwards [hTopen.mem_nhds hδ₀] with x hx; exact hC x hx a ha c hc)) hδ
  have hA c δ (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) : ∀ a, F c δ a = G c δ a := by
    have hFan : AnalyticOnNhd ℂ (fun x => F c δ x) Set.univ := by
      apply DifferentiableOn.analyticOnNhd
      · intro x _
        exact ((fun c δ a (hc : c ∈ gaussConnectionIntegerRangeᶜ) (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) => (hf _ (by simpa [F, gaussConnectionCoordinates, gaussConnectionParameterDomain] using (by simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ))).comp a (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a by dsimp [gaussConnectionCoordinates]; fun_prop)) c δ x hc hδ).differentiableWithinAt
      · exact isOpen_univ
    have hGan : AnalyticOnNhd ℂ (fun x => G c δ x) Set.univ := by
      apply DifferentiableOn.analyticOnNhd
      · intro x _
        exact ((fun c δ a (hc : c ∈ gaussConnectionIntegerRangeᶜ) (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) => (hg _ (by simpa [G, gaussConnectionCoordinates, gaussConnectionParameterDomain] using (by simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ))).comp a (show DifferentiableAt ℂ (fun x => gaussConnectionCoordinates c δ x) a by dsimp [gaussConnectionCoordinates]; fun_prop)) c δ x hc hδ).differentiableWithinAt
      · exact isOpen_univ
    intro a
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hFan hGan isPreconnected_univ (Set.mem_univ a₀) (by filter_upwards [hVopen.mem_nhds ha₀] with x hx; exact hDelta c hc δ hδ x hx)) (Set.mem_univ a)
  have hTarget : F c (c - a - b) a = G c (c - a - b) a := by
    have hc' : c ∈ gaussConnectionIntegerRangeᶜ := by
      have := hp.1
      simpa [gaussConnectionParameterDomain, gaussConnectionIntegerRange, eq_comm] using this
    have hδ' : c - a - b ∈ gaussConnectionIntegerRangeᶜ := by
      have := hp.2
      simpa [gaussConnectionParameterDomain, gaussConnectionIntegerRange, eq_comm] using this
    exact hA c (c - a - b) hc' hδ' a
  simpa [F, G, (show gaussConnectionCoordinates c (c - a - b) a = (a, b, c) by simp [gaussConnectionCoordinates]; ring)] using hTarget

end DOZZ.Proofs
