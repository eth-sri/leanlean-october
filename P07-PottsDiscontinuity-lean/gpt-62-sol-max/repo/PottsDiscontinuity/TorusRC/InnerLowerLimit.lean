module

public import PottsDiscontinuity.TorusRC.LowerEstimate
public import PottsDiscontinuity.TorusRC.BoxProbability
public import PottsDiscontinuity.TorusRC.LogRateLimits

/-! # The height limit in the lower bound of Lemma 3.15 -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

/-- Height-normalized log probability of U=1 along positive even heights.
The extended-real carrier permits an unbounded negative rate. -/
noncomputable def torusRCUOneRateE {N : ℕ} (hN : Even N)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) : EReal :=
  let p := torusRCUOneProbability hN (positiveEvenPeriod_even m) q (positiveEvenPeriod_pos m)
  if p = 0 then ⊥ else (Real.log p / (positiveEvenPeriod m : ℝ) : ℝ)

/-- The inner M→∞ passage; all finite-energy losses are independent of M. -/
theorem torusRCU_one_inner_liminf_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N n : ℕ) (hN : Even N)
      (_ : 8 ∣ N) (_ : 0 < n) (_ : 8*(n+1) ≤ N),
      ((Real.log (blockPenalty c n) / n +
        Real.log (nativeDiagonalProbability q (N/4) (n+1)) / ((2*(n+1):ℕ):ℝ) : ℝ) : EReal)
        ≤ liminf (torusRCUOneRateE hN q) atTop := by
  obtain ⟨c, hc, hfinite⟩ := torusRCU_one_lower_of_h319 q hh319
  refine ⟨c, hc, fun N n hN hdiv hn hwidth => ?_⟩
  have hheight : Tendsto positiveEvenPeriod atTop atTop :=
    tendsto_atTop_mono (fun m => by dsimp [positiveEvenPeriod]; omega) tendsto_id
  have hb : 0 < nativeDiagonalProbability q (N/4) (n+1) :=
    liftedBoxFreeDiagonalProbability_pos _ _ _ (by omega) (by omega)
  refine log_block_product_liminf positiveEvenPeriod hheight
    (fun m => torusRCUOneProbability hN (positiveEvenPeriod_even m) q (positiveEvenPeriod_pos m))
    _ _ _ (surgeryCost_pos q N n) (by unfold blockPenalty; positivity) hb n (2*(n+1)) hn (by omega) ?_
  filter_upwards [hheight.eventually (eventually_ge_atTop (4*(n+1))),
    hheight.eventually (eventually_gt_atTop (N/2))] with m hM hNM
  exact hfinite N _ n hN (positiveEvenPeriod_even m) hdiv hn hwidth hM hNM

end PottsDiscontinuity.TorusRC
