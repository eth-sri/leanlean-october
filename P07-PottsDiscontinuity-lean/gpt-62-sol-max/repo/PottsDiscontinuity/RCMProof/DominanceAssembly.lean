module

public import PottsDiscontinuity.RCMProof.BetheAssembly
public import PottsDiscontinuity.RCMProof.SectorComparison
public import PottsDiscontinuity.RCMProof.Lemma314Adapters
public import PottsDiscontinuity.SixVertex.Sec33Dominance
public import PottsDiscontinuity.TorusExploration.Contract

@[expose] public section

open Filter Topology MeasureTheory

namespace PottsDiscontinuity.RCMProof

open SixVertex TorusRC TorusLoops

variable (q : Set.Ici (1 : ℝ))
local notation "c₀" => Real.sqrt (2 + Real.sqrt q.val)
local notation "N₀" => positiveEvenPeriod

private theorem sector_maxGap_le (hq : 4 < q.val) {n k r : ℕ}
    (hr : r ≤ N₀ n / 2) (hkr : k ≤ r) {a b : ℝ}
    (hTail : ∀ᶠ m in atTop, positiveEvenVerticalTailRate q k n m < a)
    (hLoop : ∀ᶠ m in atTop, |windingLoopDensityLogRate (positiveEvenPeriod_even n)
      (positiveEvenPeriod_pos n) q m| ≤ b) :
    Real.log (Lambda c₀ (N₀ n) r) - Real.log (LambdaMax c₀ (N₀ n)) ≤ a + b := by
  have hc : 0 < c₀ := by positivity
  let hn := positiveEvenPeriod_even n
  let hp := positiveEvenPeriod_pos n
  refine le_of_tendsto ((tendsto_log_Z6V_ratio hc hp hr).comp
    TorusExploration.positiveEvenPeriod_tendsto) ?_
  filter_upwards [hTail, hLoop] with m ht he
  let M := N₀ m
  let hm := positiveEvenPeriod_even m
  let hM := positiveEvenPeriod_pos m
  let E := phi_T_windingLoopDensityExpectation hn hm hp hM q
  let p := torusRCProbability hn hm q (torusRCVerticalTail hn hm ⟨0, hM⟩ k)
  let z := Z6Vr c₀ (N₀ n) M r / Z6V c₀ (N₀ n) M
  have hz := div_pos (Z6Vr_pos hc hp hM hr) (Z6V_pos hc hp hM)
  have hE := phi_T_windingLoopDensityExpectation_pos hn hm hp hM q
  have hlog := Real.log_le_log (mul_pos hz hE)
    (sector_ratio_mul_expectation_le_tail hn hm hp hM q hq hkr)
  rw [Real.log_mul hz.ne' hE.ne'] at hlog
  have h := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
  rw [add_div] at h
  change Real.log z / (M : ℝ) + Real.log E / (M : ℝ) ≤ Real.log p / (M : ℝ) at h
  change Real.log p / (M : ℝ) < a at ht
  change |Real.log E / (M : ℝ)| ≤ b at he
  change (1 / (M : ℝ)) * Real.log z ≤ _
  rw [one_div, ← div_eq_inv_mul]
  linarith [(abs_le.mp he).1]

/-- Taking the height limit first and applying the winding-tail estimate
bounds all admissible sectors of index at least `k` at once. -/
private theorem eventually_sector_maxGap_le
    (hq : 4 < q.val) (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξ : ℝ) (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξ))
    (hno : μ (Duality.infiniteClusterAt (0, 0)) = 0) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ r, k ≤ r → r ≤ N₀ n / 2 →
      Real.log (Lambda c₀ (N₀ n) r) - Real.log (LambdaMax c₀ (N₀ n)) ≤
        -((k - 1 : ℕ) : ℝ) * ξ + δ := by
  let a := -((k - 1 : ℕ) : ℝ) * ξ
  have ht : (a : EReal) < ((a + δ / 2 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
  have htail := eventually_lt_of_limsup_lt
    ((TorusExploration.contract_eq316 q μ hμ ξ hRate k hk).trans_lt ht)
  have hloop := TorusExploration.positiveEvenPeriod_tendsto.eventually
    (loopDensityLogRate_eventually_small q
      (lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno) (δ / 2) (by positivity))
  filter_upwards [htail, hloop] with n hn hl r hkr hr
  have htail' := (eventually_lt_of_limsup_lt hn).mono fun _ hm => EReal.coe_lt_coe_iff.1 hm
  have h := sector_maxGap_le q hq hr hkr htail' (hl (positiveEvenPeriod_even n) (positiveEvenPeriod_pos n))
  linarith

/-- The upper bound follows by identifying the dominant eigenvalue and then
sending the fixed sector index to infinity. -/
theorem rc_xi_inverse_le_critical_rate (hq : 4 < q.val) (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξ : ℝ) (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξ))
    (hξ : 0 < ξ) (hno : μ (Duality.infiniteClusterAt (0, 0)) = 0)
    {S : ℝ} (hS : Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S))
    (hpos : 0 < Real.arcosh (Real.sqrt q.val / 2) + 2 * S) :
    ξ ≤ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  let W (n : ℕ) := 4 * (n + 1)
  let idx (n : ℕ) := 2 * n + 1
  have hi : Tendsto idx atTop atTop := tendsto_atTop_mono (fun n => by dsimp [idx]; omega) tendsto_id
  have hW (n : ℕ) : N₀ (idx n) = W n := by simp [idx, W, positiveEvenPeriod]; omega
  have hgap (r : ℕ) : Tendsto (fun n => sectorLogGap c₀ (W n) r) atTop (𝓝 (-(r : ℝ) * R)) :=
    (tendsto_add_atTop_iff_nat 1).2 (sectorLogGap_tendsto q.val hq r hS)
  have hlarge {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
      ∀ᶠ n in atTop, ∀ r, k ≤ r → r ≤ W n / 2 →
        Real.log (Lambda c₀ (W n) r) - Real.log (LambdaMax c₀ (W n)) ≤
          -((k - 1 : ℕ) : ℝ) * ξ + δ := by
    simpa only [hW] using hi.eventually (eventually_sector_maxGap_le q hq μ hμ ξ hRate hno hk hδ)
  have hc : 0 < c₀ := by positivity
  have hdom : ∀ᶠ n in atTop, LambdaMax c₀ (W n) = Lambda c₀ (W n) 0 := by
    filter_upwards [(hgap 1).eventually (Iio_mem_nhds (show -((1 : ℕ) : ℝ) * R < 0 by norm_num; linarith)),
      hlarge (k := 2) (by decide) (show 0 < ξ / 2 by positivity)] with n hfirst hbulk
    have hEven := positiveEvenPeriod_even (idx n)
    rw [hW] at hEven
    refine LambdaMax_eq_Lambda0_of_dominance hc hEven (by positivity)
      (show 0 < ξ / 2 by positivity) ?_ ?_
    · intro r hr₂ hr
      have h := hbulk r hr₂ hr
      have ht : Real.log (Lambda c₀ (W n) r) ≤ -(ξ / 2) + Real.log (LambdaMax c₀ (W n)) := by
        linarith
      simpa [Real.exp_add, Real.exp_log (Lambda_pos hc hr), Real.exp_log (LambdaMax_pos hc)] using
        Real.exp_le_exp.mpr ht
    · have ht := sub_neg.mp (show sectorLogGap c₀ (W n) 1 < 0 from hfirst)
      have hr : 1 ≤ W n / 2 := by dsimp [W]; omega
      simpa [Real.exp_log (Lambda_pos hc hr), Real.exp_log (Lambda_pos hc (Nat.zero_le _))] using
        Real.exp_lt_exp.mpr ht
  have hbound (r : ℕ) (hr : 2 ≤ r) : ((r - 1 : ℕ) : ℝ) * ξ ≤ (r : ℝ) * R := by
    have h := le_of_forall_pos_le_add (a := -(r : ℝ) * R) (b := -((r - 1 : ℕ) : ℝ) * ξ) fun δ hδ => by
      apply le_of_tendsto (hgap r)
      filter_upwards [hlarge (k := r) (by omega) hδ, hdom, eventually_ge_atTop r] with n hb hd hn
      have h := hb r le_rfl (by dsimp [W]; omega)
      simpa [hd, sectorLogGap] using h
    linarith
  by_contra hn
  have hdiff : 0 < ξ - R := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨n, h⟩ := exists_nat_gt (R / (ξ - R))
  have hh := (div_lt_iff₀ hdiff).1 h
  have hnn := hbound (n + 2) (by omega)
  rw [show n + 2 - 1 = n + 1 by omega] at hnn
  push_cast at hnn
  nlinarith

end PottsDiscontinuity.RCMProof
