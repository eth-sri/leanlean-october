module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Closing strict probability lower bounds after taking logarithms -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

/-- Strict lower approximations to a positive probability recover its full
logarithmic bound, including when the upper target is an extended real. -/
theorem log_probability_lower_closed (p : ℝ) (hp : 0 < p)
    (a d : ℝ) (L : EReal)
    (h : ∀ t : ℝ, 0 < t → t < p → ((a+Real.log t/d:ℝ):EReal) ≤ L) :
    ((a+Real.log p/d:ℝ):EReal) ≤ L := by
  have ht : Tendsto Real.log (𝓝[<] p) (𝓝 (Real.log p)) :=
    (Real.continuousAt_log hp.ne').tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto (EReal.tendsto_coe.mpr ((ht.div_const d).const_add a))
  filter_upwards [Ioo_mem_nhdsLT hp] with t ht
  exact h t ht.1 ht.2

end PottsDiscontinuity.TorusRC
