module

public import PottsDiscontinuity.SixVertex.Sec33Partition

/-!
# Growth rates of six-vertex sector ratios

The full partition function grows at the largest block Perron root.  This gives the ratio rate
with that root in the denominator; the centered-block comparison follows because its Perron root
is at most the largest block root.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ} {c : ℝ}

/-- A fixed winding sector is strictly positive at every positive height. -/
theorem Z6Vr_pos (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) {r : ℕ}
    (hr : r ≤ N / 2) : 0 < Z6Vr c N M r := by
  rw [Z6Vr_eq_Z6Vn c N M r hr]
  exact Z6Vn_pos hc hN hM (by omega)

/-- The full six-vertex partition function is positive at every positive height. -/
theorem Z6V_pos (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) : 0 < Z6V c N M := by
  have hsector := Z6Vn_pos (N := N) hc hN hM (n := N / 2) (by omega)
  exact lt_of_lt_of_le hsector (Z6Vn_le_Z6V (N := N) hc.le hM (by omega))

/-- For every fixed `N` and admissible `r`, the logarithmic ratio has a limit. -/
theorem tendsto_log_Z6V_ratio (hc : 0 < c) (hN : 0 < N) {r : ℕ} (hr : r ≤ N / 2) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) atTop
      (𝓝 (Real.log (Lambda c N r) - Real.log (LambdaMax c N))) := by
  have hnum : Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vr c N M r)) atTop
      (𝓝 (Real.log (Lambda c N r))) := by
    simpa only [Z6Vr_eq_Z6Vn c N _ r hr, Lambda] using
      tendsto_log_Z6Vn hc hN (n := N / 2 - r) (by omega)
  have hden := tendsto_log_Z6V (N := N) hc hN
  have hdiff := hnum.sub hden
  have hEq : (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) =ᶠ[atTop]
      (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vr c N M r) -
        (1 / (M : ℝ)) * Real.log (Z6V c N M)) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hnumpos := Z6Vr_pos (N := N) hc hN hM hr
    have hdenpos := Z6V_pos (N := N) hc hN hM
    rw [Real.log_div (ne_of_gt hnumpos) (ne_of_gt hdenpos)]
    ring
  exact hdiff.congr' hEq.symm

end PottsDiscontinuity.SixVertex
