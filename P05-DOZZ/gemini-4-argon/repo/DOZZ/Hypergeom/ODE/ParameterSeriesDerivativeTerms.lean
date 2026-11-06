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



private def gaussParameterSeriesPrefixDomain (n : ℕ) : Set (ℂ × ℂ × ℂ) :=
  ⋂ k ∈ Finset.range (n + 1), {p | p.2.2 ≠ -(k : ℂ)}


/-- The Fréchet derivatives of adjacent parameter-series terms satisfy the derivative of their
scalar term recurrence. -/
theorem gaussParameterSeriesTerm_fderiv_succ
    (p : ℂ × ℂ × ℂ) z n
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    fderiv ℂ (fun q => gaussParameterSeriesTerm q z (n + 1)) p =
      gaussParameterSeriesRatio p z n •
          fderiv ℂ (fun q => gaussParameterSeriesTerm q z n) p +
        gaussParameterSeriesTerm p z n •> gaussParameterSeriesRatioDeriv p z n := by
  have gaussParameterSeriesPrefixDomain_isOpen : IsOpen (gaussParameterSeriesPrefixDomain n) := by
    apply isOpen_biInter_finset
    intro k hk
    exact isOpen_ne.preimage (continuous_snd.comp continuous_snd)
  have gaussParameterSeriesTerm_recurrence_of_finite_pole_free (p : ℂ × ℂ × ℂ) z (n : ℕ) (hc : ∀ k ∈ Finset.range (n + 1), p.2.2 ≠ -(k : ℂ)) : ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) * gaussParameterSeriesTerm p z (n + 1) = ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z * gaussParameterSeriesTerm p z n := by
    have ordinaryHypergeometricCoefficient_gauss_recurrence_of_finite_pole_free a b c (n : ℕ) (hc : ∀ k ∈ Finset.range (n + 1), c ≠ -(k : ℂ)) : ((n + 1 : ℂ) * ((n : ℂ) + c)) * ordinaryHypergeometricCoefficient a b c (n + 1) = ((n : ℂ) + a) * ((n : ℂ) + b) * ordinaryHypergeometricCoefficient a b c n := by
      have hcpn : Polynomial.eval c (ascPochhammer ℂ n) ≠ 0 := by
        intro h
        obtain ⟨k, hkn, hkc⟩ := (ascPochhammer_eval_eq_zero_iff n c).mp h
        exact hc k (Finset.mem_range.mpr (by omega)) (by linear_combination hkc)
      simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval]
      rw [(show ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) by exact_mod_cast Nat.factorial_succ n)]
      field_simp [hcpn, (show c + (n : ℂ) ≠ 0 by intro h; exact hc n (Finset.mem_range.mpr (Nat.lt_succ_self n)) (by linear_combination h)), (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n)]
      ring
    rw [gaussParameterSeriesTerm, gaussParameterSeriesTerm, pow_succ]
    calc
      ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
          (ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 (n + 1) * (z ^ n * z))
          = (((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
              ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 (n + 1)) * z ^ n * z := by ring
      _ = (((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) *
            ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) * z ^ n * z := by
        rw [(ordinaryHypergeometricCoefficient_gauss_recurrence_of_finite_pole_free p.1 p.2.1 p.2.2 n hc)]
      _ = ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
            (ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n) := by ring
  have hrec : ∀ q ∈ gaussParameterSeriesPrefixDomain n,
      gaussParameterSeriesTerm q z (n + 1) =
        gaussParameterSeriesRatio q z n * gaussParameterSeriesTerm q z n := by
    intro q hq
    have hqfinite : ∀ k ∈ Finset.range (n + 1), q.2.2 ≠ -(k : ℂ) := by
      simpa [gaussParameterSeriesPrefixDomain] using hq
    have hden : (n + 1 : ℂ) * ((n : ℂ) + q.2.2) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero n
      · intro hzero
        exact hqfinite n (Finset.mem_range.mpr (Nat.lt_succ_self n)) (by linear_combination hzero)
    dsimp [gaussParameterSeriesRatio]
    rw [(show gaussParameterSeriesTerm q z (n + 1) = (((n : ℂ) + q.1) * ((n : ℂ) + q.2.1) * z * gaussParameterSeriesTerm q z n) / ((n + 1 : ℂ) * ((n : ℂ) + q.2.2)) by apply (eq_div_iff hden).2; simpa [mul_assoc, mul_left_comm, mul_comm] using (gaussParameterSeriesTerm_recurrence_of_finite_pole_free q z n hqfinite))]
    field_simp [hden]
  exact ((gaussParameterSeriesRatio_hasFDerivAt p z n (by intro hzero; exact hc n (by linear_combination hzero))).mul (gaussParameterSeriesTerm_differentiableAt p z n hc |>.hasFDerivAt)).congr_of_eventuallyEq (by filter_upwards [(gaussParameterSeriesPrefixDomain_isOpen).mem_nhds (by simpa [gaussParameterSeriesPrefixDomain] using (by intro k hk; exact hc k))] with q hq; exact hrec q hq) |>.fderiv

end DOZZ.Proofs
