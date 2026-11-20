module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

namespace DedekindZetaZeroFree

theorem holomorphic_eqOn_of_open_agreement
    (U V : Set ℂ) (f g : ℂ → ℂ)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfg : Set.EqOn f g V) : Set.EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := hVne
  exact fun z hz => ((Complex.analyticOnNhd_iff_differentiableOn hU).mpr hf).eqOn_of_preconnected_of_eventuallyEq ((Complex.analyticOnNhd_iff_differentiableOn hU).mpr hg) hUc (hVU hz₀) (Filter.eventuallyEq_iff_exists_mem.mpr ⟨V, hV.mem_nhds hz₀, hfg⟩) hz

theorem puncturedPlane_isPreconnected (a : ℂ) :
    IsPreconnected ({a}ᶜ : Set ℂ) := by
  refine (isConnected_compl_singleton_of_one_lt_rank ?_ a).isPreconnected
  norm_num

theorem continuation_unique_off_one
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hg : DifferentiableOn ℂ g ({1}ᶜ : Set ℂ))
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) :
    Set.EqOn f g ({1}ᶜ : Set ℂ) := by
  refine holomorphic_eqOn_of_open_agreement ({1}ᶜ) {s : ℂ | 1 < s.re} f g
    isOpen_compl_singleton ?_ (isOpen_lt continuous_const Complex.continuous_re)
    ⟨2, by norm_num⟩ ?_ hf hg ?_
  · exact puncturedPlane_isPreconnected 1
  · norm_num
  assumption

end DedekindZetaZeroFree
