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

/-- The Fréchet derivatives of adjacent parameter-series terms satisfy the derivative of their
scalar term recurrence. -/
theorem gaussParameterSeriesTerm_fderiv_succ
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    fderiv ℂ (fun q => gaussParameterSeriesTerm q z (n + 1)) p =
      gaussParameterSeriesRatio p z n •
          fderiv ℂ (fun q => gaussParameterSeriesTerm q z n) p +
        gaussParameterSeriesTerm p z n •> gaussParameterSeriesRatioDeriv p z n := by
  have hU : IsOpen {q : ℂ × ℂ × ℂ | q.2.2 ≠ -(n : ℂ)} :=
    isOpen_ne.preimage (continuous_snd.comp continuous_snd)
  have hnear : (fun q => gaussParameterSeriesTerm q z (n + 1)) =ᶠ[𝓝 p]
      (fun q => gaussParameterSeriesRatio q z n * gaussParameterSeriesTerm q z n) := by
    filter_upwards [hU.mem_nhds (hc n)] with q hq
    exact gaussParameterSeriesTerm_recurrence q z n hq
  have hratioPole : (n : ℂ) + p.2.2 ≠ 0 := by
    have := hc n
    grind
  have hratio := gaussParameterSeriesRatio_hasFDerivAt p z n hratioPole
  have hterm := gaussParameterSeriesTerm_differentiableAt p z n hc |>.hasFDerivAt
  exact (hratio.mul hterm).congr_of_eventuallyEq hnear |>.fderiv

end DOZZ.Proofs
