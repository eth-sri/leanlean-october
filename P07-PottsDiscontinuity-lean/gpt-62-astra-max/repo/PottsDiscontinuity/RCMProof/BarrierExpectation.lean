module
public import PottsDiscontinuity.RCMProof.XiLower
public import PottsDiscontinuity.TorusRC.BlockLogRate
public import PottsDiscontinuity.TorusTopology.StripPotential
public import PottsDiscontinuity.TorusExploration.UpperRateLimits

/-! On a strip barrier the horizontal winding cochain is exact. Thus every
essential boundary loop must meet a fixed row: there are at most `N` of them,
regardless of the height. Restricting the loop expectation to the barrier
costs only the block rate `log(c/(9n²))/n`, which can be arbitrarily small. -/
@[expose] public section
open Filter Topology Finset
namespace PottsDiscontinuity.RCMProof
open Torus TorusLoops TorusRC TorusTopology

variable {N M : ℕ}
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N)
    (hMp : 0 < M) (i : Fin N) (j : Fin M) {n : ℕ} (hn : 0 < n) (hw : 3*n < N)

include hn hw in
private lemma count_on_barrier {A : RCConfig N M}
    (hB : A ∈ torusRCBarrier (Fin.pos i) (Fin.pos j) n) : windingLoopCount hN hM i j A ≤ N := by
  classical
  let ω := checkerArrows N M
  let s := rcSmoothing A
  let h := checkerArrows_compatible hN hM s
  have hs : windingLoopSet hN hM i j A ⊆ (verticalCutDarts ω j).image (directedLoopOf h) := by
    intro t ht
    have hx := horizontal_displacement_zero_of_no_strip_crossing hN hM i.pos j.pos A n hn hw hB.1
      (loopBoundaryCycle t)
    rw [loopBoundaryCycle_displacement_x, loop_horizontal_displacement _ i] at hx
    have hv : loopVertical j t ≠ 0 := ((mem_filter.mp ht).2).resolve_right (by
      simpa [Nat.ne_of_gt i.pos, ω, s, h] using hx)
    obtain ⟨d,hd,hj⟩ := exists_dart_of_loopSum_ne_zero (f := verticalCross j) t hv
    exact mem_image.mpr ⟨d,by simp [verticalCutDarts,hj],hd⟩
  exact (card_le_card hs).trans (card_image_le.trans (verticalCutDarts_card_le ω j))

include hN hM q hNp hMp in
noncomputable def upperLoopExpectation :=
  ∑ A, torusRCMass hN hM q A * torusLoopWeightFactor hN hM q hNp hMp A

include hq hn hw in
private lemma expectation_bounds :
    torusRCProbability hN hM q (torusRCBarrier hNp hMp n) * ((2/Real.sqrt q.val)^N/q.val) ≤
      upperLoopExpectation hN hM q hNp hMp ∧ upperLoopExpectation hN hM q hNp hMp ≤ 1 := by
  classical
  have hq0 : 0 < q.val := by linarith
  rw [torusRCProbability_eq_sum, sum_mul, upperLoopExpectation]
  constructor
  · apply sum_le_sum; intro A _
    have hm := torusRCMass_pos hN hM q A
    by_cases h : A ∈ torusRCBarrier hNp hMp n
    · rw [Set.indicator_of_mem h]
      exact mul_le_mul_of_nonneg_left (loopWeightFactor_ge hN hM q hq hNp hMp A
        (count_on_barrier hN hM _ _ hn hw h)) hm.le
    · rw [Set.indicator_of_notMem h,zero_mul]; unfold torusLoopWeightFactor; positivity
  · rw [← sum_torusRCMass hN hM q]
    exact sum_le_sum fun A _ => mul_le_of_le_one_right (torusRCMass_pos hN hM q A).le
      (torusLoopWeightFactor_le_one hN hM q hq hNp hMp A)

include hq in
/-- Subexponential cost of replacing the standard RC law by its loop-weighted
version in the height-then-width limit, for the physical range `q > 4`. -/
theorem loop_rate_on_barriers (hcros : h319 q)
    (ε : ℝ) (hε : 0 < ε) : ∃ K : ℕ, ∀ {N} (hN : Even N) (hNp : 0 < N), K ≤ N →
      ∀ᶠ m in atTop, |Real.log (upperLoopExpectation hN (positiveEvenPeriod_even m) q hNp
        (positiveEvenPeriod_pos m)) / (positiveEvenPeriod m : ℝ)| ≤ ε := by
  obtain ⟨c,hc,_,hbar⟩ := barrier_source_lower_of_h319 q hcros
  obtain ⟨n,hsmall,hn⟩ := (((tendsto_block_log_rate_zero c hc).eventually
    (Ioi_mem_nhds (neg_lt_zero.mpr hε))).and (eventually_ge_atTop 2)).exists
  refine ⟨3*n+1, fun {N} hN hNp hw => ?_⟩
  have hq0 : 0 < q.val := by linarith
  let b := c/(9*(n:ℝ)^2)
  let C := torusRCSurgeryEnergy q ^ (2*n+N) / q.val^2 * ((2/Real.sqrt q.val)^N/q.val)
  let P := fun m => upperLoopExpectation hN (positiveEvenPeriod_even m) q hNp (positiveEvenPeriod_pos m)
  have hb : 0 < b := by dsimp [b]; positivity
  have hC : 0 < C := by dsimp [C]; have := torusRCSurgeryEnergy_pos q; positivity
  have H : ∀ᶠ m in atTop, C*b^((positiveEvenPeriod m:ℝ)/(n:ℝ)) ≤ P m ∧ P m ≤ 1 := by
    filter_upwards [TorusExploration.positiveEvenPeriod_tendsto.eventually (eventually_ge_atTop (4*n))] with m hm
    have h₁ := hbar N (positiveEvenPeriod m) n hN (positiveEvenPeriod_even m) (by omega) (by omega) hn (by omega) hm
    have h₂ := expectation_bounds hN (positiveEvenPeriod_even m) q hq hNp (positiveEvenPeriod_pos m) (n := n) (by omega) (by omega)
    exact ⟨(by convert (mul_le_mul_of_nonneg_right h₁ (show 0 ≤ (2/Real.sqrt q.val)^N/q.val by positivity)).trans h₂.1 using 1 <;> dsimp [C,b,P] <;> ring),h₂.2⟩
  have hl := log_block_product_liminf positiveEvenPeriod TorusExploration.positiveEvenPeriod_tendsto P C b 1 hC hb zero_lt_one n 1 (by omega) (by decide) (by simpa using H.mono fun m hm => hm.1)
  simp only [Real.log_one,zero_div,add_zero] at hl
  have hev := eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.mpr (show -ε < Real.log b/(n:ℝ) from hsmall)).trans_le hl)
  filter_upwards [H,hev] with m hm hgt
  have hpos : 0 < P m := lt_of_lt_of_le (mul_pos hC (Real.rpow_pos_of_pos hb _)) hm.1
  exact abs_le.mpr ⟨(EReal.coe_lt_coe_iff.mp hgt).le, (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hpos.le hm.2) (Nat.cast_nonneg _)).trans hε.le⟩

end PottsDiscontinuity.RCMProof
