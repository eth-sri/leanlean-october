module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.ContinuationUniqueness

theorem meromorphic_germ_unique {f g : ℂ → ℂ} {O V : Set ℂ}
    (hf : MeromorphicOn f O) (hg : MeromorphicOn g O)
    (hO : IsPreconnected O) (hV : IsOpen V) (hVO : V ⊆ O)
    (hVne : V.Nonempty) (hfg : Set.EqOn f g V)
    {s : ℂ} (hs : s ∈ O) : f =ᶠ[𝓝[≠] s] g := by
  obtain ⟨a, ha⟩ := hVne
  have hzero : (fun z => f z - g z) =ᶠ[𝓝[≠] a] 0 := by
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds ha)] with z hz
    exact sub_eq_zero.mpr (hfg hz)
  filter_upwards [(meromorphicOrderAt_eq_top_iff.mp ((hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hO
    (hVO ha) hs (meromorphicOrderAt_eq_top_iff.mpr hzero)))] with z hz
  exact sub_eq_zero.mp hz

end DedekindZetaZeroFree.KPMsSameContinuationGreen.ContinuationUniqueness

end
