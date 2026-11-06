module
public import Mathlib

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
    (q : Set.Ici (1 : ℝ)) (m : ℕ)  :=
  ((Real.log (torusRCProbability hN (positiveEvenPeriod_even m) q
    {A | rcVerticalWinding hN (positiveEvenPeriod_even m)
      ⟨0,positiveEvenPeriod_pos m⟩ A = 1}) / (positiveEvenPeriod m:ℝ):ℝ):EReal)

/-- The inner M→∞ passage of (3.15), with actual native free-box
probabilities. All finite-energy losses are independent of M. -/
theorem torusRCU_one_inner_liminf_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (N n : ℕ) (hN : Even N)
      (_hN4 : 4 ≤ N) (_hNdiv : 8 ∣ N) (_hn : 2 ≤ n) (_h8nN : 8*n ≤ N),
      ((Real.log (c/(9*(n:ℝ)^2))/(n:ℝ) +
        Real.log (liftedBoxFreeConnectionProbability (torusRCBridgeParameters q)
          rotatedLatticeOrigin (N/4) rotatedLatticeOrigin (rotatedDiagonalSite n)) /
          ((2*n:ℕ):ℝ):ℝ):EReal) ≤ liminf (torusRCUOneRateE hN q) atTop := by
  obtain ⟨c,hc,hc1,hfinite⟩ := torusRCU_one_lower_of_h319 q hh319
  refine ⟨c,hc,hc1,?_⟩
  intro N n hN hN4 hNdiv hn h8nN
  let height := positiveEvenPeriod
  have hheight : Tendsto height atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with m hm
    dsimp [height,positiveEvenPeriod]
    omega
  let p  := fun m => torusRCProbability hN (positiveEvenPeriod_even m) q
    {A | rcVerticalWinding hN (positiveEvenPeriod_even m)
      ⟨0,positiveEvenPeriod_pos m⟩ A = 1}
  let b := liftedBoxFreeConnectionProbability (torusRCBridgeParameters q)
    rotatedLatticeOrigin (N/4) rotatedLatticeOrigin (rotatedDiagonalSite n)
  let C := fkOpenEnergy (torusRCBridgeParameters q) ^ (2*(N/4+2*n)) *
    torusRCSurgeryEnergy q ^ (2*n+N) / q.val^2
  
  
  
  exact log_block_product_liminf height hheight p C (c/(9*(n)^2)) b (div_pos
                                                                         (mul_pos (pow_pos (fkOpenEnergy_pos _) _) (pow_pos (torusRCSurgeryEnergy_pos q) _))
                                                                         (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _))
    (by positivity) (liftedBoxFreeDiagonalProbability_pos _ n (N/4) (by omega)
                       ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))) n (2*n) (by omega) (by omega) (by
                                                        filter_upwards [hheight.eventually (eventually_ge_atTop (max 4 (max (4*n) (N/2+1))))]
                                                          with m hm
                                                        
                                                        
                                                        
                                                        have h := hfinite N (height m) n hN (positiveEvenPeriod_even m) hN4 ((le_max_left _ _).trans hm) hNdiv hn h8nN ((le_max_left _ _).trans ((le_max_right _ _).trans hm)) (by
                                                                                                                                                      omega)
                                                        
                                                        convert h using 1;  ring)

end PottsDiscontinuity.TorusRC
