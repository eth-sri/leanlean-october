module
public import PottsDiscontinuity.RCMProof.BarrierExpectation

/-! Compare any six-vertex sector `r ≥ s` to the same random-cluster tail
`U ≥ s`. Taking the height limit bounds all their logarithmic spectral gaps,
including when we do not yet know which sector realizes the largest root. -/
@[expose] public section
open Finset Filter Topology
namespace PottsDiscontinuity.RCMProof
open SixVertex Torus TorusRC TorusExploration

variable (h₁ : contract_cor313_i) (h₃ : contract_cor313_iii) (h₆ : contract_eq316) {N M : ℕ}
    (hN : Even N) (hM : Even M) (hp : 0 < N) (hm : 0 < M) (q : Set.Ici (1:ℝ)) (hq : 4 < q.val)
include h₁ h₃ hq

private lemma sector_ratio_le {r s : ℕ} (hrs : s ≤ r) (hr : 1 ≤ r) :
    let P := torusRCProbability hN hM q (torusRCVerticalTail hN hM ⟨0,hm⟩ s)
    let E := upperLoopExpectation hN hM q hp hm
    let c := criticalSixVertexParameter q
    0 < E ∧ Z6Vr c N M r / Z6V c N M ≤ P / E := by
  classical
  intro P E c
  let D := torusNormalization q N M
  let z := torusRCPartition hN hM q
  let w := torusRCWeight hN hM q
  let f := torusLoopWeightFactor hN hM q hp hm
  let S (k : ℕ) := Finset.univ.filter fun A => k ≤ rcVerticalWinding hN hM ⟨0,hm⟩ A
  have hz : 0 < z := torusRCPartition_pos ..
  have hZ : 0 < Z6V c N M := Z6V_pos (by dsimp [c, criticalSixVertexParameter]; positivity) hp hm
  have hE : E * z = D * Z6V c N M := by
    rw [← show (∑ A, w A*f A) = D * Z6V c N M from h₁ q hq N M hN hM hp hm]
    unfold E upperLoopExpectation; rw [sum_mul]; apply sum_congr rfl; intro A _
    change w A/z*f A*z = _; field_simp
  have hP : P * z = ∑ A ∈ S s, w A := by
    dsimp only [P]; rw [torusRCProbability_eq_sum,sum_mul]; rw [sum_filter]
    apply sum_congr rfl; intro A _
    by_cases h : s ≤ rcVerticalWinding hN hM ⟨0,hm⟩ A
    · rw [Set.indicator_of_mem (by assumption),if_pos h]; exact div_mul_cancel₀ _ hz.ne'
    · rw [Set.indicator_of_notMem (by assumption),if_neg h,zero_mul]
  have hle : D * Z6Vr c N M r ≤ P*z := by
    rw [hP]; refine (h₃ q hq r N M hr hN hM hp hm).trans ((sum_le_sum fun A _ => mul_le_of_le_one_right
      (torusRCWeight_pos hN hM q A).le (torusLoopWeightFactor_le_one hN hM q hq hp hm A)).trans ?_)
    exact sum_le_sum_of_subset_of_nonneg (by grind) (fun A _ _ => (torusRCWeight_pos hN hM q A).le)
  have he := (mul_pos_iff_of_pos_right hz).mp (hE ▸ mul_pos (torusNormalization_pos ..) hZ)
  refine ⟨he, (div_le_div_iff₀ hZ he).mpr ?_⟩
  apply (le_of_mul_le_mul_right (a := z) · hz)
  calc
    _ = D * Z6Vr c N M r * Z6V c N M := by rw [mul_assoc,hE]; ring
    _ ≤ P*z * Z6V c N M := mul_le_mul_of_nonneg_right hle hZ.le
    _ = _ := by ring

/-- The integrated comparison on a fixed cylinder. -/
private lemma sector_log_gap (n : ℕ) {s r : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r)
    (hr : r ≤ positiveEvenPeriod n / 2) {u v : ℝ}
    (htail : ∀ᶠ m in atTop, positiveEvenVerticalTailRate q s n m < u)
    (hloop : ∀ᶠ m in atTop, |Real.log (upperLoopExpectation (positiveEvenPeriod_even n)
      (positiveEvenPeriod_even m) q (positiveEvenPeriod_pos n) (positiveEvenPeriod_pos m)) /
        (positiveEvenPeriod m)| ≤ v) :
    let c := criticalSixVertexParameter q; let N := positiveEvenPeriod n
    Real.log (Lambda c N r) - Real.log (LambdaMax c N) ≤ u+v := by
  intro c N
  have hc : 0 < c := by dsimp [c,criticalSixVertexParameter]; positivity
  have hn := positiveEvenPeriod_pos n
  apply le_of_tendsto ((tendsto_log_Z6V_ratio hc hn hr).comp positiveEvenPeriod_tendsto)
  filter_upwards [htail,hloop] with m ht hl
  let M := positiveEvenPeriod m
  let P := torusRCProbability (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) q
    (torusRCVerticalTail (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) ⟨0,positiveEvenPeriod_pos m⟩ s)
  let E := upperLoopExpectation (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) q hn (positiveEvenPeriod_pos m)
  change Real.log P / M < u at ht
  obtain ⟨he,hp⟩ := sector_ratio_le h₁ h₃ _ (positiveEvenPeriod_even m) hn
    (positiveEvenPeriod_pos m) q hq hsr (hs.trans hsr)
  have hz := div_pos (Z6Vr_pos hc hn (positiveEvenPeriod_pos m) hr) (Z6V_pos hc hn (positiveEvenPeriod_pos m))
  have hp' := (div_pos_iff_of_pos_right he).mp (hz.trans_le hp)
  have h := div_le_div_of_nonneg_right (Real.log_le_log hz hp) (Nat.cast_nonneg M)
  rw [Real.log_div hp'.ne' he.ne',sub_div] at h
  change 1/(M:ℝ)*_ ≤ _; rw [one_div_mul_eq_div]; linarith [(abs_le.mp hl).1]

include h₆ in
/-- The height estimates hold simultaneously for every admissible sector above `s`,
for every sufficiently large even width. -/
theorem sector_gaps_eventually (hcros : h319 q)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit
      (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ) (ξ : ℝ)
    (hξ : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite n))) /
      n) atTop (𝓝 ξ)) (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ r, s ≤ r → r ≤ N/2 → Real.log (Lambda (criticalSixVertexParameter q) N r) -
      Real.log (LambdaMax (criticalSixVertexParameter q) N) ≤ -(s-1:ℕ)*ξ + ε := by
  let a := -(s-1:ℕ)*ξ
  have hb : a < (a+ε/2:EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨k,hk⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt ((h₆ q μ hμ ξ hξ s hs).trans_lt hb))
  obtain ⟨K,hK⟩ := loop_rate_on_barriers q hq hcros _ (half_pos hε)
  filter_upwards [eventually_ge_atTop (max K (2*(k+1)))] with N hN hEven r hsr hr
  obtain ⟨l,hl⟩ := hEven
  have hN' : positiveEvenPeriod (l-1) = N := by dsimp [positiveEvenPeriod]; omega
  obtain rfl := hN'.symm
  have ht := eventually_lt_of_limsup_lt (hk (l-1) (by omega))
  have hh := sector_log_gap h₁ h₃ q hq _ hs hsr hr (ht.mono fun m hm => EReal.coe_lt_coe_iff.mp hm)
    (hK (positiveEvenPeriod_even _) (positiveEvenPeriod_pos _) (by omega))
  linarith

end PottsDiscontinuity.RCMProof
