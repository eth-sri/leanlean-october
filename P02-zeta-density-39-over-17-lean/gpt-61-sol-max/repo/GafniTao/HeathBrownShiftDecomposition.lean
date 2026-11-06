module
import Mathlib
public import GafniTao.HeathBrownShiftFibers
public import Mathlib.Data.Finset.Sigma

@[expose] public section

/-!
# Diagonal and fixed-shift decomposition of `𝓝₂`

The localized pair count is bounded by its diagonal together with two
copies of the positive-shift fibers.  The two copies retain orientation,
so no symmetry or multiplicity is silently discarded.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

section
variable (N k H K : ℕ) (f : ℝ → ℝ)
include N k H K f

def heathBrownPairCountTwoDiagonal
     : Finset (ℕ × ℕ) := by
  classical
  exact (heathBrownPairCountTwo N k H K f).filter fun p => p.1 = p.2

def heathBrownPairCountTwoPositive
     : Finset (ℕ × ℕ) := by
  classical
  exact (heathBrownPairCountTwo N k H K f).filter fun p => p.2 < p.1

def heathBrownPairCountTwoNegative
     : Finset (ℕ × ℕ) := by
  classical
  exact (heathBrownPairCountTwo N k H K f).filter fun p => p.1 < p.2

def heathBrownAllPositiveShiftFibers
     : Finset (Σ _d : ℕ, ℕ) :=
  (Finset.Icc 1 N).sigma fun d =>
    heathBrownPositiveShiftFiber N k H K f d
end


section
variable (q : Σ _d : ℕ, ℕ)
include q

def heathBrownPairOfPositiveShift  : ℕ × ℕ :=
  (q.2 + q.1, q.2)

def heathBrownPairOfNegativeShift  : ℕ × ℕ :=
  (q.2, q.2 + q.1)
end


theorem heathBrownDistanceToInteger_neg (x : ℝ) :
    heathBrownDistanceToInteger (-x) = heathBrownDistanceToInteger x := by
  rw [heathBrownDistanceToInteger_eq_unitAddCircle_norm,
    heathBrownDistanceToInteger_eq_unitAddCircle_norm]
  simp

section
variable {N k H K : ℕ} {f : ℝ → ℝ}
include N k H K f

theorem heathBrownPairCountTwo_subset_three_parts
     :
    heathBrownPairCountTwo N k H K f ⊆
      heathBrownPairCountTwoDiagonal N k H K f ∪
        (heathBrownPairCountTwoPositive N k H K f ∪
          heathBrownPairCountTwoNegative N k H K f) := by
  intro p hp
  rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
  · simp [heathBrownPairCountTwoNegative, hp, hlt]
  · simp [heathBrownPairCountTwoDiagonal, hp, heq]
  · simp [heathBrownPairCountTwoPositive, hp, hgt]

theorem heathBrownPairCountTwoDiagonal_card_le
     :
    (heathBrownPairCountTwoDiagonal N k H K f).card ≤ N := by
  classical
  let s := heathBrownPairCountTwoDiagonal N k H K f
  have hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpd : p.1 = p.2 := (Finset.mem_filter.mp hp).2
    have hqd : q.1 = q.2 := (Finset.mem_filter.mp hq).2
    grind
  have himage : s.image Prod.fst ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    have hpCount := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_Icc]
    exact ⟨(mem_heathBrownPairCountTwo.mp hpCount).1,
      (mem_heathBrownPairCountTwo.mp hpCount).2.1⟩
  calc
    s.card = (s.image Prod.fst).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card himage
    _ ≤ N := by simp [Nat.card_Icc]

theorem heathBrownPairCountTwoPositive_subset_shiftImage
     :
    heathBrownPairCountTwoPositive N k H K f ⊆
      (heathBrownAllPositiveShiftFibers N k H K f).image
        heathBrownPairOfPositiveShift := by
  classical
  intro p hp
  have hpCount := (Finset.mem_filter.mp hp).1
  have hlt := (Finset.mem_filter.mp hp).2
  let d := p.1 - p.2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdN : d ≤ N := by
    exact le_trans (Nat.sub_le _ _) (mem_heathBrownPairCountTwo.mp hpCount).2.1
  have hpFiber : p.2 ∈ heathBrownPositiveShiftFiber N k H K f d := by
    rw [mem_heathBrownPositiveShiftFiber]
    have hadd : p.2 + d = p.1 := by
      simp [d, Nat.add_sub_of_le hlt.le]
    exact ⟨(mem_heathBrownPairCountTwo.mp hpCount).2.2.1,
      hadd.symm ▸ (mem_heathBrownPairCountTwo.mp hpCount).2.1,
      by simpa [hadd] using hpCount⟩
  rw [Finset.mem_image]
  refine ⟨⟨d, p.2⟩, ?_, ?_⟩
  · simp [heathBrownAllPositiveShiftFibers, hd, hdN, hpFiber]
  · apply Prod.ext
    · simp [heathBrownPairOfPositiveShift, d, Nat.add_sub_of_le hlt.le]
    · rfl

theorem heathBrownPairCountTwoNegative_subset_shiftImage
     :
    heathBrownPairCountTwoNegative N k H K f ⊆
      (heathBrownAllPositiveShiftFibers N k H K f).image
        heathBrownPairOfNegativeShift := by
  classical
  intro p hp
  have hpCount := (Finset.mem_filter.mp hp).1
  have hlt := (Finset.mem_filter.mp hp).2
  let d := p.2 - p.1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdN : d ≤ N := by
    exact le_trans (Nat.sub_le _ _) (mem_heathBrownPairCountTwo.mp hpCount).2.2.2.1
  have hswap : (p.2, p.1) ∈ heathBrownPairCountTwo N k H K f := by
    rw [mem_heathBrownPairCountTwo] at hpCount ⊢
    refine ⟨hpCount.2.2.1, hpCount.2.2.2.1, hpCount.1, hpCount.2.1,
      ?_, ?_, ?_⟩
    · simpa [Nat.dist_comm] using hpCount.2.2.2.2.1
    · have heq :
          heathBrownDerivativeCoordinate f (k - 2) p.2 -
              heathBrownDerivativeCoordinate f (k - 2) p.1 =
            -(heathBrownDerivativeCoordinate f (k - 2) p.1 -
              heathBrownDerivativeCoordinate f (k - 2) p.2) := by ring
      rw [heq, heathBrownDistanceToInteger_neg]
      exact hpCount.2.2.2.2.2.1
    · have heq :
          heathBrownDerivativeCoordinate f (k - 1) p.2 -
              heathBrownDerivativeCoordinate f (k - 1) p.1 =
            -(heathBrownDerivativeCoordinate f (k - 1) p.1 -
              heathBrownDerivativeCoordinate f (k - 1) p.2) := by ring
      rw [heq, heathBrownDistanceToInteger_neg]
      exact hpCount.2.2.2.2.2.2
  have hpFiber : p.1 ∈ heathBrownPositiveShiftFiber N k H K f d := by
    rw [mem_heathBrownPositiveShiftFiber]
    have hadd : p.1 + d = p.2 := by
      simp [d, Nat.add_sub_of_le hlt.le]
    exact ⟨(mem_heathBrownPairCountTwo.mp hpCount).1,
      hadd.symm ▸ (mem_heathBrownPairCountTwo.mp hpCount).2.2.2.1,
      by simpa [hadd] using hswap⟩
  rw [Finset.mem_image]
  refine ⟨⟨d, p.1⟩, ?_, ?_⟩
  · simp [heathBrownAllPositiveShiftFibers, hd, hdN, hpFiber]
  · apply Prod.ext
    · rfl
    · simp [heathBrownPairOfNegativeShift, d, Nat.add_sub_of_le hlt.le]
end


section
variable (N k H K : ℕ) (f : ℝ → ℝ)
include N k H K f

theorem heathBrownAllPositiveShiftFibers_card
     :
    (heathBrownAllPositiveShiftFibers N k H K f).card =
      ∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H K f d).card := by
  simp [heathBrownAllPositiveShiftFibers]

theorem heathBrownPairCountTwo_card_le_shift_sum
     :
    (heathBrownPairCountTwo N k H K f).card ≤
      N + 2 * ∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H K f d).card := by
  classical
  let dset := heathBrownPairCountTwoDiagonal N k H K f
  let pset := heathBrownPairCountTwoPositive N k H K f
  let nset := heathBrownPairCountTwoNegative N k H K f
  let fibers := heathBrownAllPositiveShiftFibers N k H K f
  have hdiag : dset.card ≤ N := heathBrownPairCountTwoDiagonal_card_le
  have hpos : pset.card ≤ fibers.card := by
    calc
      pset.card ≤ (fibers.image heathBrownPairOfPositiveShift).card :=
        Finset.card_le_card heathBrownPairCountTwoPositive_subset_shiftImage
      _ ≤ fibers.card := Finset.card_image_le
  have hneg : nset.card ≤ fibers.card := by
    calc
      nset.card ≤ (fibers.image heathBrownPairOfNegativeShift).card :=
        Finset.card_le_card heathBrownPairCountTwoNegative_subset_shiftImage
      _ ≤ fibers.card := Finset.card_image_le
  calc
    (heathBrownPairCountTwo N k H K f).card ≤
        (dset ∪ (pset ∪ nset)).card :=
      Finset.card_le_card heathBrownPairCountTwo_subset_three_parts
    _ ≤ dset.card + (pset.card + nset.card) := by grind
    _ ≤ N + (fibers.card + fibers.card) := by omega
    _ = N + 2 * ∑ d ∈ Finset.Icc 1 N,
        (heathBrownPositiveShiftFiber N k H K f d).card := by
      rw [heathBrownAllPositiveShiftFibers_card]
      omega
end






