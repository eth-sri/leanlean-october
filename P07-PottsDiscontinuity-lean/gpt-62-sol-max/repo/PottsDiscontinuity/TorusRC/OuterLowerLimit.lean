module

public import PottsDiscontinuity.TorusRC.InnerLowerLimit
public import PottsDiscontinuity.TorusRC.BoxLimitLower
public import PottsDiscontinuity.TorusRC.LogProbabilityClosure

/-! # The width limit in the lower bound of Lemma 3.15 -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

/-- Source-compatible widths, divisible by eight. -/
def eightfoldPeriod (k : ℕ) : ℕ := 8*(k+1)

theorem eightfoldPeriod_even (k : ℕ) : Even (eightfoldPeriod k) :=
  ⟨4*(k+1),by dsimp [eightfoldPeriod]; omega⟩

theorem eightfoldPeriod_dvd (k : ℕ) : 8 ∣ eightfoldPeriod k := ⟨k+1,rfl⟩

/-- The two iterated lower limits in (3.15), with the explicit parity
restriction N∈8ℕ and all positive even heights. -/
noncomputable def torusRCUOneIteratedLiminf (q : Set.Ici (1 : ℝ)) : EReal :=
  liminf (fun k => liminf (torusRCUOneRateE (eightfoldPeriod_even k) q) atTop) atTop

/-- The outer N→∞ passage uses the exact rotated free law and connection event of
`CorrLength/`;
no new infinite-volume law is introduced. -/
theorem torusRCU_one_outer_liminf_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ((Real.log (blockPenalty c n) / n +
        Real.log ((rotatedDiagonalConnectionProbability (torusRCBridgeParameters q) (n+1) : NNReal):ℝ) /
          ((2*(n+1):ℕ):ℝ) : ℝ) : EReal) ≤ torusRCUOneIteratedLiminf q := by
  obtain ⟨c, hc, hinner⟩ := torusRCU_one_inner_liminf_of_h319 q hh319
  refine ⟨c, hc, fun n hn => ?_⟩
  apply log_probability_lower_closed _ (rotatedDiagonalProbability_pos _ (n+1))
  intro t ht htp
  have hnative := liftedBoxFreeDiagonalProbability_eventually_gt
    (torusRCBridgeParameters q) (n+1) t ht.le htp
  have hR : Tendsto (fun k => eightfoldPeriod k/4) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp [eightfoldPeriod]; omega) tendsto_id
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards [hR.eventually hnative, eventually_ge_atTop n] with k hkt hkn
  have h8n : 8*(n+1) ≤ eightfoldPeriod k := by dsimp [eightfoldPeriod]; omega
  refine le_trans (EReal.coe_le_coe_iff.mpr (add_le_add le_rfl
    (div_le_div_of_nonneg_right (Real.log_le_log ht hkt.le) (Nat.cast_nonneg _))))
    (hinner (eightfoldPeriod k) n (eightfoldPeriod_even k) (eightfoldPeriod_dvd k) hn h8n)

end PottsDiscontinuity.TorusRC
