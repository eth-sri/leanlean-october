/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.SmoothSeries

/-! The parameter derivatives of successive Gauss-series terms obey a product recurrence. -/

@[expose] public section

open Nat Polynomial Filter
open scoped RightActions Topology

namespace DOZZ.Proofs

/-- The coefficient recurrence only needs the finitely many denominator factors occurring in the
two adjacent terms. -/
theorem ordinaryHypergeometricCoefficient_gauss_recurrence_of_finite_pole_free
    (a b c : ℂ) (n : ℕ)
    (hc : ∀ k ∈ Finset.range (n + 1), c ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ((n : ℂ) + c)) *
        ordinaryHypergeometricCoefficient a b c (n + 1) =
      ((n : ℂ) + a) * ((n : ℂ) + b) *
        ordinaryHypergeometricCoefficient a b c n := by
  have hcn : c + (n : ℂ) ≠ 0 := by
    grind
  have hcpn : Polynomial.eval c (ascPochhammer ℂ n) ≠ 0 := by
    intro h
    obtain ⟨k, hkn, hkc⟩ := (ascPochhammer_eval_eq_zero_iff n c).mp h
    grind
  have hfact : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ n
  have hfact0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval]
  rw [hfact]
  field_simp [hcpn, hcn, hfact0]
  ring

variable (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ)

include p z n in
/-- Successive parameterized terms obey their recurrence whenever the finite denominator prefix is
pole-free. -/
theorem gaussParameterSeriesTerm_recurrence_of_finite_pole_free
    
    (hc : ∀ k ∈ Finset.range (n + 1), p.2.2 ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
        gaussParameterSeriesTerm p z (n + 1) =
      ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
        gaussParameterSeriesTerm p z n := by
  rw [gaussParameterSeriesTerm, gaussParameterSeriesTerm, pow_succ]
  have hcoeff := ordinaryHypergeometricCoefficient_gauss_recurrence_of_finite_pole_free
    p.1 p.2.1 p.2.2 n hc
  grind

private def gaussParameterSeriesPrefixDomain (n : ℕ) : Set (ℂ × ℂ × ℂ) :=
  ⋂ k ∈ Finset.range (n + 1), {p | p.2.2 ≠ -(k : ℂ)}

private theorem gaussParameterSeriesPrefixDomain_isOpen (n : ℕ) :
    IsOpen (gaussParameterSeriesPrefixDomain n) := by
  apply isOpen_biInter_finset
  intro k hk
  exact isOpen_ne.preimage (continuous_snd.comp continuous_snd)

include p z n in
/-- The Fréchet derivatives of adjacent parameter-series terms satisfy the derivative of their
scalar term recurrence. -/
theorem gaussParameterSeriesTerm_fderiv_succ
    
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    fderiv ℂ (fun q => gaussParameterSeriesTerm q z (n + 1)) p =
      gaussParameterSeriesRatio p z n •
          fderiv ℂ (fun q => gaussParameterSeriesTerm q z n) p +
        gaussParameterSeriesTerm p z n •> gaussParameterSeriesRatioDeriv p z n := by
  have hfinite : ∀ k ∈ Finset.range (n + 1), p.2.2 ≠ -(k : ℂ) := by
    intro k hk
    exact hc k
  have hpU : p ∈ gaussParameterSeriesPrefixDomain n := by
    simpa [gaussParameterSeriesPrefixDomain] using hfinite
  have hUopen := gaussParameterSeriesPrefixDomain_isOpen n
  have hrec : ∀ q ∈ gaussParameterSeriesPrefixDomain n,
      gaussParameterSeriesTerm q z (n + 1) =
        gaussParameterSeriesRatio q z n * gaussParameterSeriesTerm q z n := by
    intro q hq
    have hqfinite : ∀ k ∈ Finset.range (n + 1), q.2.2 ≠ -(k : ℂ) := by
      simpa [gaussParameterSeriesPrefixDomain] using hq
    have hterm := gaussParameterSeriesTerm_recurrence_of_finite_pole_free q z n hqfinite
    have hden : (n + 1 : ℂ) * ((n : ℂ) + q.2.2) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero n
      grind
    dsimp [gaussParameterSeriesRatio]
    grind
  have hnear : (fun q => gaussParameterSeriesTerm q z (n + 1)) =ᶠ[𝓝 p]
      (fun q => gaussParameterSeriesRatio q z n * gaussParameterSeriesTerm q z n) := by
    filter_upwards [hUopen.mem_nhds hpU] with q hq
    exact hrec q hq
  have hratioPole : (n : ℂ) + p.2.2 ≠ 0 := by
    grind
  have hratio := gaussParameterSeriesRatio_hasFDerivAt p z n hratioPole
  have hterm := gaussParameterSeriesTerm_differentiableAt p z n hc |>.hasFDerivAt
  exact (hratio.mul hterm).congr_of_eventuallyEq hnear |>.fderiv

end DOZZ.Proofs
