module

public import AnalyticESC.Basic

@[expose] public section

/-! Identity theorems for holomorphic maps on a neighbourhood of the interval. -/

namespace AnalyticESC

open Set Metric Filter Topology

/-- An interval of agreement determines two holomorphic maps on a preconnected set. -/
theorem eqOn_of_eqOn_Icc {U : Set ℂ} {g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U) (hU : IsPreconnected U) {a b : ℝ}
    (hab : a < b) (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ U)
    (heq : ∀ x ∈ Icc a b, g x = h x) : EqOn g h U := by
  have ha := left_mem_Icc.2 hab.le
  have h := (uniqueDiffWithinAt_iff_accPt.1 (uniqueDiffOn_Icc hab a ha)).map
    Complex.continuous_ofReal.continuousAt Complex.ofReal_injective
  rw [Filter.map_principal] at h
  exact hg.eqOn_of_preconnected_of_frequently_eq hh hU (hI a ha)
    ((accPt_iff_frequently_nhdsNE.1 h).mono (by grind))

/-- Identity theorem on the neighbourhood of `I`. -/
theorem eqOn_nbhd_of_eqOn_Icc {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ I) (heq : ∀ x ∈ Icc a b, g x = h x) : EqOn g h (nbhd ε) :=
  eqOn_of_eqOn_Icc (hg.analyticOnNhd (isOpen_nbhd _)) (hh.analyticOnNhd (isOpen_nbhd _))
    (isPreconnected_nbhd _) hab (fun _ hx => ofReal_mem_nbhd hε (hI hx)) heq

end AnalyticESC
