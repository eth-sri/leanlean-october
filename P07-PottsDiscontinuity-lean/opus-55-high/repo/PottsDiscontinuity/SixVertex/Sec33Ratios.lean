module

public import PottsDiscontinuity.SixVertex.Sec33Partition

/-!
# Growth rates of six-vertex sector ratios

The full partition function grows at the largest block Perron root.  This gives the ratio rate
with that root in the denominator; the centered-block comparison follows because its Perron root
is at most the largest block root.
-/

public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ} {c : ℝ}

section
variable (hc : 0 < c) (hN : 0 < N)
include hc hN
/-- A fixed winding sector is strictly positive at every positive height. -/
theorem Z6Vr_pos (hM : 0 < M) {r : ℕ}
    (hr : r ≤ N / 2) : 0 < Z6Vr c N M r := by
  rw [Z6Vr_eq_trace_block hN hM c hr]
  let : Nonempty (State N (N / 2 - r)) := ⟨packed (by omega)⟩
  exact trace_pow_pos_of_nonneg_pos_diag (transferBlock_nonneg hc.le _)
    (fun x => by simp) M

/-- The full six-vertex partition function is positive at every positive height. -/
theorem Z6V_pos (hM : 0 < M) : 0 < Z6V c N M :=
  lt_of_lt_of_le (Z6Vn_pos (N := N) hc hN hM (n := N / 2) (by omega)) (Z6Vn_le_Z6V (N := N) hc.le hM (by omega))

/-- For every fixed `N` and admissible `r`, the logarithmic ratio has a limit. -/
theorem tendsto_log_Z6V_ratio {r : ℕ} (hr : r ≤ N / 2) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) atTop
      (𝓝 (Real.log (Lambda c N r) - Real.log (LambdaMax c N))) := by
  have hnum := tendsto_log_Z6Vr hc hN hr
  have hdiff := hnum.sub (tendsto_log_Z6V hc hN)
  have hEq : (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) =ᶠ[atTop]
      (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vr c N M r) -
        (1 / (M : ℝ)) * Real.log (Z6V c N M)) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [Real.log_div (ne_of_gt (Z6Vr_pos hc hN hM hr)) (ne_of_gt (Z6V_pos hc hN hM))]
    ring
  exact hdiff.congr' hEq.symm

/-- The centered-block limsup comparison follows from the exact ratio rate and
`Lambda c N 0 ≤ LambdaMax c N`. -/
theorem limsup_log_Z6V_ratio_le_center {r : ℕ}
    (hr : r ≤ N / 2) :
    Filter.limsup (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) atTop ≤
      Real.log (Lambda c N r) - Real.log (Lambda c N 0) := by
  rw [(tendsto_log_Z6V_ratio hc hN hr).limsup_eq]
  have hcenter : Lambda c N 0 ≤ LambdaMax c N :=
    pfRoot_transferBlock_le_LambdaMax (by omega)
  have hlog := Real.log_le_log (Lambda_pos hc (Nat.zero_le _)) hcenter
  linarith
end

end PottsDiscontinuity.SixVertex
