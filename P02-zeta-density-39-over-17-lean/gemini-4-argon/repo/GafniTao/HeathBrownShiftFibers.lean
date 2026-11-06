module
public import GafniTao.HeathBrownShiftedDifference

@[expose] public section

/-!
# Positive-shift fibers of Heath-Brown's localized count

This is the exact `m = n + d` bridge in Section 3 of Heath-Brown's paper.
It connects membership in the concrete two-variable count `𝓝₂` to the
literal one-variable nearest-integer spacing set for `g_d`.
-/

open Finset

namespace GafniTao

noncomputable section

noncomputable def heathBrownPositiveShiftFiber
    (N k H K : ℕ) (f : ℝ → ℝ) (d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    (n + d, n) ∈ heathBrownPairCountTwo N k H K f

theorem mem_heathBrownPositiveShiftFiber
    {N k H K d n : ℕ} {f : ℝ → ℝ} :
    n ∈ heathBrownPositiveShiftFiber N k H K f d ↔
      1 ≤ n ∧ n + d ≤ N ∧
        (n + d, n) ∈ heathBrownPairCountTwo N k H K f := by
  simp only [heathBrownPositiveShiftFiber, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · intro hn
    have hp := mem_heathBrownPairCountTwo.mp hn.2
    exact ⟨hn.1.1, hp.2.1, hn.2⟩
  · intro hn
    exact ⟨⟨hn.1, le_trans (Nat.le_add_right n d) hn.2.1⟩, hn.2.2⟩

theorem heathBrownPositiveShiftFiber_subset_spacingSet
    {N k H K d : ℕ} {f : ℝ → ℝ} :
    heathBrownPositiveShiftFiber N k H K f d ⊆
      heathBrownSpacingSet (N - d)
        (heathBrownShiftedDifference f (k - 2) d)
        (4 * (((H : ℝ) ^ (k - 2))⁻¹)) := by
  intro n hn
  rw [mem_heathBrownPositiveShiftFiber] at hn
  simp only [heathBrownSpacingSet, Finset.mem_filter, Finset.mem_Icc]
  have hp := (mem_heathBrownPairCountTwo.mp hn.2.2)
  refine ⟨⟨hn.1, Nat.le_sub_of_add_le hn.2.1⟩, ?_⟩
  simpa only [heathBrownShiftedDifference_nat, Nat.cast_add] using
    hp.2.2.2.2.2.1

theorem heathBrownPositiveShiftFiber_card_le_spacingSet
    {N k H K d : ℕ} {f : ℝ → ℝ} :
    (heathBrownPositiveShiftFiber N k H K f d).card ≤
      (heathBrownSpacingSet (N - d)
        (heathBrownShiftedDifference f (k - 2) d)
        (4 * (((H : ℝ) ^ (k - 2))⁻¹))).card :=
  Finset.card_le_card heathBrownPositiveShiftFiber_subset_spacingSet


