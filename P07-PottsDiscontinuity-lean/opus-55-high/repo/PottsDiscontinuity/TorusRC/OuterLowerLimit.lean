module

public import PottsDiscontinuity.TorusRC.InnerLowerLimit
public import PottsDiscontinuity.TorusRC.BoxLimitLower
public import PottsDiscontinuity.TorusRC.LogProbabilityClosure

/-! # The width limit in the lower bound of Lemma 3.15 -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

section
variable (k : ℕ)
/-- Source-compatible widths, divisible by eight. -/
def eightfoldPeriod  : ℕ := 8*(k+1)

theorem eightfoldPeriod_even  : Even (eightfoldPeriod k) :=
  ⟨4*(k+1),by grind [eightfoldPeriod]⟩

theorem eightfoldPeriod_four_le  : 4 ≤ eightfoldPeriod k := by
  grind [eightfoldPeriod]

theorem eightfoldPeriod_dvd  : 8 ∣ eightfoldPeriod k := ⟨k+1,rfl⟩
end

section
variable (q : Set.Ici (1 : ℝ))
/-- The two iterated lower limits in (3.15), with the explicit parity
restriction N∈8ℕ and all positive even heights. -/
noncomputable def torusRCUOneIteratedLiminf  : EReal :=
  liminf (fun k => liminf (torusRCUOneRateE (eightfoldPeriod_even k) q) atTop) atTop

/-- The outer N→∞ passage uses the exact rotated free law and connection event of
`CorrLength/`;
no new infinite-volume law is introduced. -/
theorem torusRCU_one_outer_liminf_of_h319 (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n : ℕ, 2 ≤ n →
      ((Real.log (c/(9*(n:ℝ)^2))/(n:ℝ) +
        Real.log ((rotatedDiagonalConnectionProbability (torusRCBridgeParameters q) n : NNReal):ℝ) /
          ((2*n:ℕ):ℝ):ℝ):EReal) ≤ torusRCUOneIteratedLiminf q := by
  obtain ⟨c,hc,hc1,hinner⟩ := torusRCU_one_inner_liminf_of_h319 q hh319
  refine ⟨c,hc,hc1,?_⟩
  intro n hn
  apply log_probability_lower_closed _ (rotatedDiagonalProbability_pos _ n)
    _ _
  intro t ht htp
  have hnative := liftedBoxFreeDiagonalProbability_eventually_gt
    (torusRCBridgeParameters q) n t ht.le htp
  have hR : Tendsto (fun k => eightfoldPeriod k/4) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [eventually_ge_atTop r] with k hk
    grind [eightfoldPeriod]
  have hbound : ∀ᶠ k in atTop,
      ((Real.log (c/(9*(n:ℝ)^2))/(n:ℝ) + Real.log t/((2*n:ℕ):ℝ):ℝ):EReal) ≤
        liminf (torusRCUOneRateE (eightfoldPeriod_even k) q) atTop := by
    filter_upwards [hR.eventually hnative,eventually_ge_atTop n] with k hkt hkn
    have h := hinner (eightfoldPeriod k) n (eightfoldPeriod_even k)
      (eightfoldPeriod_four_le k) (eightfoldPeriod_dvd k) hn (by grind [eightfoldPeriod])
    apply le_trans _ h
    apply EReal.coe_le_coe_iff.mpr
    exact add_le_add le_rfl
      (div_le_div_of_nonneg_right (Real.log_le_log ht hkt.le) (by positivity))
  exact le_liminf_of_le (by isBoundedDefault) hbound
end

end PottsDiscontinuity.TorusRC
