module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval
public import GuthMaynard.NativeSource.GuthMaynard.Pigeonhole
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial
public import GuthMaynard.NativeSource.GuthMaynard.Separated
public import GuthMaynard.NativeSource.GuthMaynard.ZeroDetector

@[expose] public section

open Complex Finset Classical
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/--
A displacement by at most `H` turns one shifted unit bin into at most
`2 * ceil H + 1` original unit bins.  This is the finite covering step needed
to keep the analytic hypothesis about unshifted zero ordinates.
-/
theorem shifted_bin_weight_le_of_unit_bin_weight {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate shift : α → ℝ) (H : ℝ) (L : ℕ)
    (hShift : ∀ x ∈ S, |ordinate x - shift x| ≤ H)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L)
    (z : ℤ) :
    ∑ t ∈ (S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
        ∑ x ∈ S.filter (fun y => shift y = t), weight x ≤
      (2 * ⌈H⌉₊ + 1) * L := by
  let A := S.filter (fun x => (z : ℝ) ≤ shift x ∧ shift x < (z : ℝ) + 1)
  let k : ℕ := ⌈H⌉₊
  let J : Finset ℤ := Finset.Icc (z - (k : ℤ)) (z + (k : ℤ))
  have hShiftFiber :
      ∑ t ∈ (S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
          ∑ x ∈ S.filter (fun y => shift y = t), weight x =
        ∑ x ∈ A, weight x := by
    have hFiber := Finset.sum_fiberwise_eq_sum_filter S
      ((S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1)) shift weight
    have hFilter : S.filter (fun x =>
        shift x ∈ (S.image shift).filter (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1)) = A := by
      apply Finset.filter_congr
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · exact fun h => h.2
      · exact fun hz => ⟨⟨x, hx, rfl⟩, hz⟩
    rw [hFilter] at hFiber
    exact hFiber
  have hFloors : ∀ x ∈ A, ⌊ordinate x⌋ ∈ J := by
    intro x hx
    have hxData := Finset.mem_filter.mp hx
    have hDisp := hShift x hxData.1
    rw [abs_le] at hDisp
    have hk : H ≤ (k : ℝ) := by
      exact Nat.le_ceil H
    change ⌊ordinate x⌋ ∈ Finset.Icc (z - (k : ℤ)) (z + (k : ℤ))
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      have hCast : ((z - (k : ℤ) : ℤ) : ℝ) = (z : ℝ) - (k : ℝ) := by
        norm_num
      rw [hCast]
      linarith [hxData.2.1, hDisp.1]
    · have hFloorLt : ⌊ordinate x⌋ < z + (k : ℤ) + 1 := by
        rw [Int.floor_lt]
        have hCast : ((z + (k : ℤ) + 1 : ℤ) : ℝ) = (z : ℝ) + (k : ℝ) + 1 := by
          norm_num
        rw [hCast]
        linarith [hxData.2.2, hDisp.2]
      omega
  have hAll : A.filter (fun x => ⌊ordinate x⌋ ∈ J) = A :=
    Finset.filter_eq_self.mpr hFloors
  have hFloorFiber := Finset.sum_fiberwise_eq_sum_filter A J
    (fun x => ⌊ordinate x⌋) weight
  rw [hAll] at hFloorFiber
  rw [hShiftFiber, ← hFloorFiber]
  calc
    ∑ j ∈ J, ∑ x ∈ A.filter (fun y => ⌊ordinate y⌋ = j), weight x
        ≤ ∑ _j ∈ J, L := by
      apply Finset.sum_le_sum
      intro j hj
      apply le_trans (Finset.sum_le_sum_of_subset ?_) (hLocal j)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨(Finset.mem_filter.mp hx.1).1, ?_⟩
      exact Int.floor_eq_iff.mp hx.2
    _ = J.card * L := by simp
    _ = (2 * k + 1) * L := by
      congr 1
      change (Finset.Icc (z - (k : ℤ)) (z + (k : ℤ))).card = 2 * k + 1
      rw [Int.card_Icc]
      omega

/-- Exact weighted pigeonholing over a nonempty finite family of fibers. -/
theorem weighted_finite_pigeonhole {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (J : Finset κ) (weight : α → ℕ) (scale : α → κ)
    (hS : S.Nonempty) (hScale : ∀ x ∈ S, scale x ∈ J) :
    ∃ j ∈ J,
      ∑ x ∈ S, weight x ≤ J.card * ∑ x ∈ S.filter (fun y => scale y = j), weight x := by
  have hJ : J.Nonempty := by
    rcases hS with ⟨x, hx⟩
    exact ⟨scale x, hScale x hx⟩
  let fiberWeight (j : κ) : ℕ :=
    ∑ x ∈ S.filter (fun y => scale y = j), weight x
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J fiberWeight hJ
  refine ⟨j, hj, ?_⟩
  have hAll : S.filter (fun x => scale x ∈ J) = S :=
    Finset.filter_eq_self.mpr hScale
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S J scale weight
  rw [hAll] at hFiber
  rw [← hFiber]
  calc
    ∑ k ∈ J, fiberWeight k ≤ ∑ _k ∈ J, fiberWeight j := by
      apply Finset.sum_le_sum
      intro k hk
      exact hmax k hk
    _ = J.card * fiberWeight j := by simp

/--
The exact finite extraction step. It contains the real combinatorial deduction:
dyadic pigeonholing, aggregation of multiplicities over shifted ordinates, and
weighted one-dimensional separated selection.
-/
theorem finite_weighted_extract_separated {α κ : Type*}
    [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (J : Finset κ) (weight : α → ℕ) (scale : α → κ)
    (shift : κ → α → ℝ) (large : κ → ℝ → Prop) (inInterval : ℝ → Prop)
    (L : ℕ) (hS : S.Nonempty) (hScale : ∀ x ∈ S, scale x ∈ J)
    (hLocal : ∀ j ∈ J, ∀ z : ℤ,
      ∑ t ∈ (S.filter (fun x => scale x = j)).image (shift j) |>.filter
        (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
        ∑ x ∈ (S.filter (fun y => scale y = j)).filter (fun y => shift j y = t), weight x ≤ L)
    (hLarge : ∀ j ∈ J, ∀ x ∈ S, scale x = j → large j (shift j x))
    (hInterval : ∀ j ∈ J, ∀ x ∈ S, scale x = j → inInterval (shift j x)) :
    ∃ j ∈ J, ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W, large j t) ∧
      (∀ t ∈ W, inInterval t) ∧
      ∑ x ∈ S, weight x ≤ 2 * J.card * L * W.card := by
  obtain ⟨j, hj, hPigeon⟩ :=
    weighted_finite_pigeonhole S J weight scale hS hScale
  let A := S.filter (fun x => scale x = j)
  let shiftedWeight (t : ℝ) : ℕ :=
    ∑ x ∈ A.filter (fun y => shift j y = t), weight x
  have hSelectLocal : ∀ z : ℤ,
      ∑ t ∈ (A.image (shift j)).filter
        (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1), shiftedWeight t ≤ L := by
    intro z
    exact hLocal j hj z
  obtain ⟨W, hWA, hSeparated, hWeight⟩ :=
    weighted_separated_selection (A.image (shift j)) shiftedWeight L hSelectLocal
  refine ⟨j, hj, W, hSeparated, ?_, ?_, ?_⟩
  · intro t ht
    have htA := hWA ht
    rw [Finset.mem_image] at htA
    rcases htA with ⟨x, hx, rfl⟩
    exact hLarge j hj x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro t ht
    have htA := hWA ht
    rw [Finset.mem_image] at htA
    rcases htA with ⟨x, hx, rfl⟩
    exact hInterval j hj x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · have hFiber : ∑ t ∈ A.image (shift j), shiftedWeight t = ∑ x ∈ A, weight x := by
      have hAll : A.filter (fun x => shift j x ∈ A.image (shift j)) = A := by
        apply Finset.filter_eq_self.mpr
        intro x hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hFiberwise := Finset.sum_fiberwise_eq_sum_filter A (A.image (shift j)) (shift j) weight
      rw [hAll] at hFiberwise
      exact hFiberwise
    rw [hFiber] at hWeight
    calc
      ∑ x ∈ S, weight x ≤ J.card * ∑ x ∈ A, weight x := hPigeon
      _ ≤ J.card * (2 * L * W.card) := Nat.mul_le_mul_left _ hWeight
      _ = 2 * J.card * L * W.card := by ring

end GuthMaynard.NativeMoment
