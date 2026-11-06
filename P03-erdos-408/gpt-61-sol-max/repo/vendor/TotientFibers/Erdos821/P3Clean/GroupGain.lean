module

public import Erdos821.P3Clean.Conditioning

/-! Converting a constant per small group into the fixed logarithmic exponent. -/

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem smallGroup_card (P : PrimeGroups) :
    Fintype.card P.SmallGroup = P.smallGroups.card := by
  rw [Fintype.card_subtype]
  rfl

theorem small_group_gain (F : FixedData) (C : ℝ) (hC : 1 ≤ C)
    (x : ℝ) (P : PrimeGroups) (hP : P.Admissible F x) (hL : 0 < L x) :
    C ^ Fintype.card P.SmallGroup ≤ (L x) ^ (F.C₀ * Real.log C) := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hs : (Fintype.card P.SmallGroup : ℝ) ≤ F.C₀ * T x := by
    rw [smallGroup_card]
    exact hP.2.1
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCp, Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  simpa only [T, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hs hlog

end Erdos821.P3Clean
