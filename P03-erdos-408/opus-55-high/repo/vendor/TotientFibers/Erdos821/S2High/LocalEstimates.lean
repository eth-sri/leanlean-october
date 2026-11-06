module

public import Erdos821.S2.HighRankTask

@[expose] public section

noncomputable section

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

theorem eta_bounds (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ eta F n i ∧ eta F n i ≤ 1 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt F.q := Real.sqrt_nonneg _
  have hsqrt_lt_one : Real.sqrt F.q < 1 := by
    have h := Real.sqrt_lt_sqrt F.q_pos.le F.q_lt
    simpa only [Real.sqrt_one] using h
  have hq_nonneg : 0 ≤ F.q := F.q_pos.le
  unfold eta visitQ
  split_ifs <;> constructor <;> nlinarith [F.q_lt]

end Erdos821.S2High
