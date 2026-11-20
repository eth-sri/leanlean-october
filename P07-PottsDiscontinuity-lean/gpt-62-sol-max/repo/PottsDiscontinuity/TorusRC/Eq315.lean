module

public import PottsDiscontinuity.TorusRC.OuterLowerLimit
public import PottsDiscontinuity.TorusRC.CorrelationRate
public import PottsDiscontinuity.TorusRC.BlockLogRate

/-! # Lemma 3.15, equation (3.15), with h319 as the sole external premise -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open CorrLength

/-- Equation (3.15) along widths divisible by eight and positive even heights.
The rate is the unique Fekete limit for the exact rotated free law (`CorrLength/`).
The torus topology premises are discharged (`TorusTopology/`); only the named crossing
estimate h319 is a premise here. It is proved by `TorusCrossing.h319_proved`
(`TorusCrossing/Final.lean`). -/
theorem eq315 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ((-inverseCorrelationLength q:ℝ):EReal) ≤ torusRCUOneIteratedLiminf q := by
  obtain ⟨c, hc, hbound⟩ := torusRCU_one_outer_liminf_of_h319 q hh319
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have hrate := ((tendsto_inverseCorrelationLength q).neg).comp hshift
  simp only [neg_div, neg_neg] at hrate
  have hlim := EReal.tendsto_coe.mpr ((tendsto_block_log_rate_zero c hc).add hrate)
  simp only [zero_add] at hlim
  exact le_of_tendsto hlim ((eventually_gt_atTop 0).mono hbound)

end PottsDiscontinuity.TorusRC
