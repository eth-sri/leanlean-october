module
public import Mathlib

public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Identity theorem for real analytic functions

Two real analytic functions on a preconnected set agree everywhere if they agree on a nonempty
open subset.  This is the form used to continue the equality of eigenvalue branches in the source.
-/

public section

open Filter
open Set


namespace PottsDiscontinuity.AnalyticTools

/-- Identity theorem on a preconnected set: equality on a nonempty open subset propagates to the
whole set. -/
theorem analytic_eqOn_of_eqOn_open_preconnected
    {f g : ℝ → ℝ} {U V : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hg : AnalyticOnNhd ℝ g U)
    (hU : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    (hfg : EqOn f g V) : EqOn f g U := Exists.casesOn hVne fun x hx =>
                                         AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hU (hVU hx) (mp_mem (IsOpen.mem_nhds hV hx) (univ_mem' hfg))

end PottsDiscontinuity.AnalyticTools
