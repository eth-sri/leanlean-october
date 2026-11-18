module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

public section

@[expose] section

namespace OAI

/-!
# Interval weights for the three-sector convolution degeneration

Section 5.2 assigns weights to the second and third coordinates of
`C(a, 3 * h + a - 1)`. The total weight is nonnegative on convolution support,
and its zero set consists exactly of the three matching sector blocks.
The middle block is a convolution with the last two legs exchanged and the
first coordinate reversed.
-/

namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Number of second-leg coordinates in the original convolution. -/
def sourceWidth (a h : ℕ) : ℕ := 3 * h + a - 1

/-- Beginning of the right sector on both the second and third legs. -/
def rightStart (a h : ℕ) : ℕ := 2 * h + a - 1

/-- A coefficient-one term of the original convolution tensor. -/
def Support (a h i j k : ℕ) : Prop :=
  i < a ∧ j < sourceWidth a h ∧ k = i + j

/-- The middle interval on the second tensor leg. -/
def MiddleY (a h j : ℕ) : Prop := h ≤ j ∧ j < rightStart a h

/-- The middle interval on the third tensor leg. -/
def MiddleZ (a h k : ℕ) : Prop := h + a - 1 ≤ k ∧ k < rightStart a h

instance (a h j : ℕ) : Decidable (MiddleY a h j) := inferInstanceAs
  (Decidable (h ≤ j ∧ j < rightStart a h))

instance (a h k : ℕ) : Decidable (MiddleZ a h k) := inferInstanceAs
  (Decidable (h + a - 1 ≤ k ∧ k < rightStart a h))

/-- No weight is assigned to the common first leg. -/
def firstWeight (_i : ℕ) : ℤ := 0

/-- Weight one on the middle second-leg interval, zero elsewhere. -/
def secondWeight (a h j : ℕ) : ℤ := if MiddleY a h j then 1 else 0

/-- Weight minus one on the middle third-leg interval, zero elsewhere. -/
def thirdWeight (a h k : ℕ) : ℤ := if MiddleZ a h k then -1 else 0

/-- Exponent of the degeneration parameter on one term. -/
def totalWeight (a h i j k : ℕ) : ℤ :=
  firstWeight i + secondWeight a h j + thirdWeight a h k

/-- The three retained blocks have matching sector labels. -/
def MatchingSectors (a h j k : ℕ) : Prop :=
  (j < h ∧ k < h + a - 1) ∨
  (MiddleY a h j ∧ MiddleZ a h k) ∨
  (rightStart a h ≤ j ∧ rightStart a h ≤ k)

/-- A middle third-leg coordinate can only be reached from the middle second leg. -/
theorem middleY_of_middleZ {a h i j k : ℕ}
    (hs : Support a h i j k) (hz : MiddleZ a h k) : MiddleY a h j := by
  unfold Support at hs
  unfold MiddleY MiddleZ rightStart at *
  omega

/-- The constant coefficient consists exactly of the three matching blocks. -/
theorem totalWeight_eq_zero_iff {a h i j k : ℕ}
    (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔ MatchingSectors a h j k := by
  unfold Support sourceWidth at hs
  unfold MatchingSectors MiddleY MiddleZ rightStart
  unfold totalWeight firstWeight secondWeight thirdWeight MiddleY MiddleZ rightStart
  split_ifs <;> omega

/-- Parametrization of the left copy of `C(a,h)`. -/
def LeftBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧ j = r ∧ k = u + r

/-- Parametrization of the middle copy with the second and third legs exchanged. -/
def MiddleBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = a - 1 - u ∧
    j = h + u + r ∧ k = h + a - 1 + r

/-- Parametrization of the right translated copy of `C(a,h)`. -/
def RightBranch (a h i j k : ℕ) : Prop :=
  ∃ u r, u < a ∧ r < h ∧ i = u ∧
    j = rightStart a h + r ∧ k = rightStart a h + u + r

/-- The left block preserves the actual first coordinate. -/
theorem leftBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    LeftBranch a h i j k ↔ j < h ∧ k < h + a - 1 := by
  rcases hs with ⟨hi, hj, hk⟩
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hleft, _⟩
    exact ⟨i, j, hi, hleft, rfl, rfl, hk⟩

/-- The middle support equation becomes convolution after reversing the first
coordinate and exchanging the second and third legs. -/
theorem middleBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    MiddleBranch a h i j k ↔ MiddleY a h j ∧ MiddleZ a h k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold MiddleY MiddleZ rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hy, hz⟩
    refine ⟨a - 1 - i, k - (h + a - 1), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The right block is the same convolution after translating the two outer
coordinates. -/
theorem rightBranch_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    RightBranch a h i j k ↔ rightStart a h ≤ j ∧ rightStart a h ≤ k := by
  rcases hs with ⟨hi, hj, hk⟩
  unfold sourceWidth at hj
  unfold RightBranch rightStart
  constructor
  · rintro ⟨u, r, hu, hr, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hjr, hkr⟩
    refine ⟨i, j - (2 * h + a - 1), hi, ?_, rfl, ?_, ?_⟩ <;> omega

/-- Exact retained support of the three-sector degeneration. -/
theorem retained_support_iff {a h i j k : ℕ} (hs : Support a h i j k) :
    totalWeight a h i j k = 0 ↔
      LeftBranch a h i j k ∨ MiddleBranch a h i j k ∨ RightBranch a h i j k := by
  rw [totalWeight_eq_zero_iff hs, leftBranch_iff hs, middleBranch_iff hs,
    rightBranch_iff hs]
  rfl

/-- Every displayed left-branch term belongs to the original convolution. -/
theorem LeftBranch.support {a h i j k : ℕ} (hb : LeftBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed middle-branch term belongs to the original convolution. -/
theorem MiddleBranch.support {a h i j k : ℕ} (hb : MiddleBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth
  omega

/-- Every displayed right-branch term belongs to the original convolution. -/
theorem RightBranch.support {a h i j k : ℕ} (hb : RightBranch a h i j k) :
    Support a h i j k := by
  rcases hb with ⟨u, r, hu, hr, rfl, rfl, rfl⟩
  unfold Support sourceWidth rightStart
  omega

/-- The left and middle branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_middleBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ MiddleBranch a h i j k := by
  intro hm
  have hl' := (leftBranch_iff hl.support).mp hl
  have hm' := (middleBranch_iff hm.support).mp hm
  unfold MiddleY at hm'
  omega

/-- The left and right branches use disjoint second-leg coordinates. -/
theorem leftBranch_not_rightBranch {a h i j k : ℕ}
    (hl : LeftBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hl' := (leftBranch_iff hl.support).mp hl
  have hr' := (rightBranch_iff hr.support).mp hr
  have hi := hr.support.1
  unfold rightStart at hr'
  omega

/-- The middle and right branches use disjoint second-leg coordinates. -/
theorem middleBranch_not_rightBranch {a h i j k : ℕ}
    (hm : MiddleBranch a h i j k) : ¬ RightBranch a h i j k := by
  intro hr
  have hm' := (middleBranch_iff hm.support).mp hm
  have hr' := (rightBranch_iff hr.support).mp hr
  unfold MiddleY at hm'
  omega

end MatrixMultiplication.AuxiliarySeparation.Sector

end OAI
