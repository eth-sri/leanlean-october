module

public import ImprovedExponents.Optimum.NumLog

@[expose] public section

/-!
# Certified values of the constants at `c = 107/5`, `c = 108/5` and `c = 22`

The values are computed with the toolkit of `Optimum/NumLog.lean`: every statement becomes an
inequality between rational numbers.

* `c = 108/5` is admissible for the paper's encodings, `18 ln 4 ≤ baseFull (108/5)`
  (`baseFull_ge_18`), and `basePruned (109/5) < 18 ln 4` (`basePruned_lt_18`).
* At `c = 108/5` with the paper's encodings: `Γ = 0.074835…` (`Gam_108_5_mem`) and the saving is
  `F = 0.0020597… > 0.00205` (`savingF_full_gt`, `savingF_full_lt`).
* At `c = 107/5` with the paper's encodings, near the maximum of the saving: `Γ = 0.0741367…`
  (`Gam_107_5_mem`) and the saving is `F = 0.00205990… > 0.002059` (`savingF_full_107_5_gt`,
  `savingF_full_107_5_lt`).
* At `c = 22` with pruned encodings: `Γ = 0.076207…` (`Gam_22_mem`, `Gam_22_bounds`), the thinness
  bound is `R = 0.054988…` (`thinR_pruned_bounds`) and the saving is `F = 0.0020952…`
  (`savingF_pruned_gt`, `savingF_pruned_lt`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Set

/-! ### The thinness constants -/

/-- `basePruned 22 = 25.104839…`. -/
theorem basePruned_22_mem : basePruned 22 ∈ Icc (25.10483 : ℝ) 25.10485 :=
  ⟨le_basePruned 4, basePruned_le 4⟩

/-! ### `c = 108/5` with the paper's encodings -/

/-! ### `c = 107/5` with the paper's encodings -/

/-! ### `c = 22` with pruned encodings -/

/-- `Γ(22) = 0.0762079…`; the crossing is at `θ = 0.1160367…`. -/
theorem Gam_22_mem : Gam 22 ∈ Icc (0.076207 : ℝ) 0.076209 :=
  ⟨le_Gam (θ := 0.116036) (le_gammaX 4) (le_gammaQ (-3)),
    Gam_le (θ := 0.116037) (gammaX_le 4) (gammaQ_le (-3))⟩

/-- The saving at `c = 22` with pruned encodings is more than `0.002095`
(it is `0.00209529…`). -/
theorem savingF_pruned_gt : (0.002095 : ℝ) < savingF (basePruned 22) (Gam 22) :=
  lt_savingF (basePruned_pos (by norm_num)) basePruned_22_mem.2 Gam_22_mem.1

end ImprovedExponents
