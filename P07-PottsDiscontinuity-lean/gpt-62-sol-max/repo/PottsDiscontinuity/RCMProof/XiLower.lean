module

public import PottsDiscontinuity.RCMProof.BetheAssembly
public import PottsDiscontinuity.RCMProof.SectorComparison
public import PottsDiscontinuity.TorusRC.Eq315
public import PottsDiscontinuity.TorusExploration.UpperRateLimits

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open TorusRC Torus SixVertex

private theorem exactOne_liminf_le_gap (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    {N : ℕ} (hN : Even N) (hNp : 0 < N) :
    liminf (torusRCUOneRateE hN q) atTop ≤
      (sectorLogGap (Real.sqrt (2 + Real.sqrt q.val)) N 1 : EReal) := by
  let c := Real.sqrt (2 + Real.sqrt q.val)
  have hc : 0 < c := by positivity
  have hr : 1 ≤ N / 2 := by grind
  let f (m : ℕ) := Real.log (q.val ^ 2) / (positiveEvenPeriod m : ℝ) +
    Real.log (Z6Vr c N (positiveEvenPeriod m) 1 / Z6V c N (positiveEvenPeriod m)) /
      (positiveEvenPeriod m : ℝ)
  have hM := TorusExploration.positiveEvenPeriod_tendsto
  have hlim : Tendsto f atTop (𝓝 (Real.log (Lambda c N 1) - Real.log (LambdaMax c N))) := by
    simpa only [f, Function.comp_apply, one_div, ← div_eq_inv_mul, zero_add] using
      ((tendsto_natCast_atTop_iff.2 hM).const_div_atTop (Real.log (q.val ^ 2))).add
        ((tendsto_log_Z6V_ratio hc hNp hr).comp hM)
  calc
    _ ≤ liminf (fun m => (f m : EReal)) atTop := by
      refine liminf_le_liminf (Eventually.of_forall fun m => ?_)
      let M := positiveEvenPeriod m
      have hMpos := positiveEvenPeriod_pos m
      let hm := positiveEvenPeriod_even m
      let p := torusRCProbability hN hm q {A | rcVerticalWinding hN hm ⟨0, hMpos⟩ A = 1}
      change (if p = 0 then ⊥ else ((Real.log p / (M : ℝ) : ℝ) : EReal)) ≤ _
      split_ifs with hp
      · exact bot_le
      have h := Real.log_le_log (lt_of_le_of_ne (torusRCProbability_nonneg hN hm q _) (Ne.symm hp))
        (exactOneProbability_le_sector_ratio hN hm hNp hMpos q hq)
      rw [Real.log_mul (by positivity) (div_pos (Z6Vr_pos hc hNp hMpos hr)
        (Z6V_pos hc hNp hMpos)).ne'] at h
      exact EReal.coe_le_coe_iff.2 (by simpa only [add_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg M))
    _ = ((Real.log (Lambda c N 1) - Real.log (LambdaMax c N)) : EReal) :=
      (continuous_coe_real_ereal.continuousAt.tendsto.comp hlim).liminf_eq
    _ ≤ _ := by
      apply EReal.coe_le_coe_iff.2
      change Real.log (Lambda c N 1) - Real.log (LambdaMax c N) ≤
        Real.log (Lambda c N 1) - Real.log (Lambda c N 0)
      gcongr
      · exact Lambda_pos hc (Nat.zero_le _)
      · exact pfRoot_transferBlock_le_LambdaMax (c := c) (n := N / 2) (by omega)

/-- The exact-one sector supplies the lower bound on the inverse length. -/
theorem xi_inverse_ge_critical_rate (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hh319 : h319 q)
    {S : ℝ} (hS : Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S)) :
    Real.arcosh (Real.sqrt q.val / 2) + 2 * S ≤ inverseCorrelationLength q := by
  have ht : Tendsto (fun k : ℕ => 2 * (k + 1)) atTop atTop := TorusExploration.positiveEvenPeriod_tendsto
  have hl := (sectorLogGap_tendsto q.val hq 1 hS).comp ht
  have hgap : Tendsto (fun k => sectorLogGap (Real.sqrt (2 + Real.sqrt q.val)) (eightfoldPeriod k) 1)
      atTop (𝓝 (-(Real.arcosh (Real.sqrt q.val / 2) + 2 * S))) := by
    simpa [eightfoldPeriod, Function.comp_def, ← Nat.mul_assoc] using hl
  have h := liminf_le_liminf (f := atTop) (Eventually.of_forall fun k =>
    exactOne_liminf_le_gap q hq (eightfoldPeriod_even k) (by simp [eightfoldPeriod]))
  change torusRCUOneIteratedLiminf q ≤ _ at h
  have hh := h.trans_eq (continuous_coe_real_ereal.continuousAt.tendsto.comp hgap).liminf_eq
  linarith [EReal.coe_le_coe_iff.1 ((eq315 q hh319).trans hh)]

end PottsDiscontinuity.RCMProof
