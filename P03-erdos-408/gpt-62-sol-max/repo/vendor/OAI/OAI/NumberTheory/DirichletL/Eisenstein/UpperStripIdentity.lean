module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace OAI.CubicEisenstein
open scoped Topology

lemma upperStrip_convex (a : ℝ) : Convex ℝ {s : ℂ | a < s.re ∧ 0 < s.im} :=
  ((convex_Ioi a).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)

/-- Continue an identity from the absolute-convergence region of the cusp
series to its connected upper strip. -/
theorem eqOn_of_upperStrip {f g : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticOnNhd ℂ f {s : ℂ | a < s.re ∧ 0 < s.im})
    (hg : AnalyticOnNhd ℂ g {s : ℂ | a < s.re ∧ 0 < s.im}) (ha : a < 5)
    (h : ∀ s : ℂ, 4 < s.re → 0 < s.im → f s = g s) :
    Set.EqOn f g {s : ℂ | a < s.re ∧ 0 < s.im} := by
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (upperStrip_convex a).isPreconnected
    (z₀ := 5 + Complex.I) (by simpa using ha) ?_
  have hz : (5 + Complex.I : ℂ) ∈ {s : ℂ | 4 < s.re ∧ 0 < s.im} := by norm_num
  exact Filter.Eventually.mono (hopen.mem_nhds hz) fun s hs => h s hs.1 hs.2

end OAI.CubicEisenstein
