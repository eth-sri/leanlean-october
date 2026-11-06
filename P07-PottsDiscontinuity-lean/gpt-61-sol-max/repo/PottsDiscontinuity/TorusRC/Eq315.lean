module
public import Mathlib

public import PottsDiscontinuity.TorusRC.OuterLowerLimit
public import PottsDiscontinuity.TorusRC.CorrelationRate
public import PottsDiscontinuity.TorusRC.BlockLogRate

/-! # Lemma 3.15, equation (3.15), with h319 as the sole external premise -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC



/-- Equation (3.15) along widths divisible by eight and positive even heights.
The rate is the unique Fekete limit for the exact rotated free law (`CorrLength/`).
The torus topology premises are discharged (`TorusTopology/`); only the named crossing
estimate h319 is a premise here. It is proved by `TorusCrossing.h319_proved`
(`TorusCrossing/Final.lean`). -/
theorem eq315 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ((-inverseCorrelationLength q:ℝ):EReal) ≤ torusRCUOneIteratedLiminf q := by
  obtain ⟨c,hc,_,hbound⟩ := torusRCU_one_outer_liminf_of_h319 q hh319
  
  
  apply le_of_tendsto (by
                         apply EReal.tendsto_coe.mpr
                         simpa only [zero_add] using (tendsto_block_log_rate_zero c hc).add (by
                                                                                               simpa only [neg_div,neg_neg] using (tendsto_inverseCorrelationLength q).neg))
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact hbound n hn

end PottsDiscontinuity.TorusRC
