module

public import Chazelle.Core.SweepPrimKer
public import Chazelle.UnfoldTactics

/-!
# Sweep RAM primitives (WP-D2), part 3: the left sector at a walk vertex

The left sector of the walk `W` at a vertex `v` with neighbours `a` (before) and `b` (after) is
`sideLeftOf a v b`, i.e. `sideCcw (b - v) (x - v) (a - v)` (`Chazelle.Chain.sideCcw`).  For a
horizontal direction `x - v = (s, 0)` (`s = ±1`) its truth value is a Boolean function of sign
bits (`sideCcw_horiz_iff`):

* the orientation of `a, v, b` (`0 < det`, `det = 0`: kernel tests `2`, `3`),
* the height and abscissa comparisons of `b` and of `a` with `v` (kernel tests `1`, `0`),
* the direction bit `s = 1`.

The dot products of the definition of `sideCcw` only matter for collinear `a, v, b`; then the two
products `B.1 A.1` and `B.2 A.2` have the same weak sign (`dot_neg_iff_of_cross_zero`), so their
signs, hence the dot product's, are read off the comparison bits.

The machine part (`cmp4`, `cmp4_exec`) computes the four comparison bits of a point with `v`.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf)

@[expose] public section

/-! ## The sector test as a Boolean function of sign bits -/

/-- **The sector formula**: `sideCcw B (s, 0) A` in terms of the direction bit `sp` (`s = 1`), the
orientation bits `oP` (`0 < cross B A`), `oZ` (`cross B A = 0`) and the sign bits of the
coordinates of `B` and `A`. -/
def SecProp (sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : Prop) : Prop :=
  (oP ∧ ((sp ∧ b2n) ∨ (¬ sp ∧ b2p)) ∧ ((sp ∧ a2p) ∨ (¬ sp ∧ a2n))) ∨
  (¬ oP ∧ ¬ oZ ∧ (((sp ∧ b2n) ∨ (¬ sp ∧ b2p)) ∨ ((sp ∧ a2p) ∨ (¬ sp ∧ a2n)))) ∨
  (oZ ∧ ((b2p ∧ a2n) ∨ (b2n ∧ a2p) ∨ (b1p ∧ a1n) ∨ (b1n ∧ a1p)) ∧ ((sp ∧ b2n) ∨ (¬ sp ∧ b2p))) ∨
  (oZ ∧ ((b2p ∧ a2p) ∨ (b2n ∧ a2n) ∨ (b1p ∧ a1p) ∨ (b1n ∧ a1n)) ∧
    ((b2p ∨ b2n) ∨ ((sp ∧ b1n) ∨ (¬ sp ∧ b1p))))

/-- For parallel vectors the two coordinate products have the same weak sign. -/
theorem prod_nonneg_of_cross_zero {B A : Point} (h : sideCross B A = 0) :
    0 ≤ (B.1 * A.1) * (B.2 * A.2) := by
  unfold sideCross at h
  have : (B.1 * A.1) * (B.2 * A.2) = (B.1 * A.2) * (B.1 * A.2) := by
    have e : B.2 * A.1 = B.1 * A.2 := by linarith
    calc (B.1 * A.1) * (B.2 * A.2) = (B.1 * A.2) * (B.2 * A.1) := by ring
      _ = (B.1 * A.2) * (B.1 * A.2) := by rw [e]
  rw [this]; exact mul_self_nonneg _

/-- The sign of the dot product of parallel vectors, negative case. -/
theorem dot_neg_iff_of_cross_zero {B A : Point} (h : sideCross B A = 0) :
    sideDot B A < 0 ↔ ((0 < B.2 ∧ A.2 < 0) ∨ (B.2 < 0 ∧ 0 < A.2) ∨ (0 < B.1 ∧ A.1 < 0) ∨
      (B.1 < 0 ∧ 0 < A.1)) := by
  have hp := prod_nonneg_of_cross_zero h
  unfold sideDot
  rw [show ((0 < B.2 ∧ A.2 < 0) ∨ (B.2 < 0 ∧ 0 < A.2) ∨ (0 < B.1 ∧ A.1 < 0) ∨
      (B.1 < 0 ∧ 0 < A.1)) ↔ (B.2 * A.2 < 0 ∨ B.1 * A.1 < 0) by
    rw [mul_neg_iff, mul_neg_iff]; tauto]
  constructor
  · intro hs
    by_contra hc
    push Not at hc
    linarith [hc.1, hc.2]
  · rintro (h2 | h2)
    · have : B.1 * A.1 ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      linarith
    · have : B.2 * A.2 ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      linarith

/-- The sign of the dot product of parallel vectors, positive case. -/
theorem dot_pos_iff_of_cross_zero {B A : Point} (h : sideCross B A = 0) :
    0 < sideDot B A ↔ ((0 < B.2 ∧ 0 < A.2) ∨ (B.2 < 0 ∧ A.2 < 0) ∨ (0 < B.1 ∧ 0 < A.1) ∨
      (B.1 < 0 ∧ A.1 < 0)) := by
  have hp := prod_nonneg_of_cross_zero h
  unfold sideDot
  rw [show ((0 < B.2 ∧ 0 < A.2) ∨ (B.2 < 0 ∧ A.2 < 0) ∨ (0 < B.1 ∧ 0 < A.1) ∨
      (B.1 < 0 ∧ A.1 < 0)) ↔ (0 < B.2 * A.2 ∨ 0 < B.1 * A.1) by
    rw [mul_pos_iff, mul_pos_iff]; tauto]
  constructor
  · intro hs
    by_contra hc
    push Not at hc
    linarith [hc.1, hc.2]
  · rintro (h1 | h1)
    · have : 0 ≤ B.1 * A.1 := by
        by_contra hc; push Not at hc; nlinarith
      linarith
    · have : 0 ≤ B.2 * A.2 := by
        by_contra hc; push Not at hc; nlinarith
      linarith

/-- **The left sector test for a horizontal direction** as a Boolean function of sign bits. -/
theorem sideCcw_horiz_iff (B A : Point) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    sideCcw B ((s, 0) : Point) A ↔
      SecProp (s = 1) (0 < sideCross B A) (sideCross B A = 0) (0 < B.2) (B.2 < 0) (0 < B.1)
        (B.1 < 0) (0 < A.2) (A.2 < 0) (0 < A.1) (A.1 < 0) := by
  have hneg : sideCross B A < 0 ↔ ¬ 0 < sideCross B A ∧ ¬ sideCross B A = 0 := by
    constructor
    · intro h; exact ⟨not_lt.2 h.le, h.ne⟩
    · rintro ⟨h1, h2⟩; push Not at h1; exact lt_of_le_of_ne h1 h2
  have hBXne : sideCross B ((s, 0) : Point) ≠ 0 ↔ (0 < B.2 ∨ B.2 < 0) := by
    have e : sideCross B ((s, 0) : Point) = -(s * B.2) := by ufring sideCross
    rw [e, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    constructor
    · rintro ⟨-, h⟩
      rcases lt_or_gt_of_ne h with h | h
      exacts [Or.inr h, Or.inl h]
    · rintro (h | h)
      exacts [⟨hs0, h.ne'⟩, ⟨hs0, h.ne⟩]
  unfold sideCcw SecProp
  rw [hneg, hBXne]
  rcases hs with rfl | rfl
  · have hBX : 0 < sideCross B ((1, 0) : Point) ↔ B.2 < 0 := by
      unfold sideCross; constructor <;> intro h <;> simp at h ⊢ <;> linarith
    have hXA : 0 < sideCross ((1, 0) : Point) A ↔ 0 < A.2 := by
      unfold sideCross; constructor <;> intro h <;> simp at h ⊢ <;> linarith
    have hdBX : sideDot B ((1, 0) : Point) < 0 ↔ B.1 < 0 := by
      unfold sideDot; constructor <;> intro h <;> simp at h ⊢ <;> linarith
    rw [hBX, hXA, hdBX]
    simp [true_and, not_true_eq_false, false_and, or_false]
    by_cases hz : sideCross B A = 0
    · rw [dot_neg_iff_of_cross_zero hz, dot_pos_iff_of_cross_zero hz]
      simp [hz, lt_irrefl, not_false_eq_true, true_and, false_and, not_true_eq_false,
        false_or]
    · simp [hz, false_and, or_false, not_false_eq_true, true_and, and_true]
  · have hBX : 0 < sideCross B ((-1, 0) : Point) ↔ 0 < B.2 := by
      unfold sideCross; constructor <;> intro h <;> simp at h ⊢ <;> linarith
    have hXA : 0 < sideCross ((-1, 0) : Point) A ↔ A.2 < 0 := by
      unfold sideCross; constructor <;> intro h <;> simp at h ⊢ <;> linarith
    have hdBX : sideDot B ((-1, 0) : Point) < 0 ↔ 0 < B.1 := by
      unfold sideDot; constructor <;> intro h <;> simp at h ⊢ <;> linarith
    rw [hBX, hXA, hdBX]
    have hn : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp [hn, false_and, false_or, not_false_eq_true, true_and]
    by_cases hz : sideCross B A = 0
    · rw [dot_neg_iff_of_cross_zero hz, dot_pos_iff_of_cross_zero hz]
      simp [hz, lt_irrefl, not_false_eq_true, true_and, false_and, not_true_eq_false,
        false_or]
    · simp [hz, false_and, or_false, not_false_eq_true, true_and, and_true]


/-- **The left sector of a corner for a horizontal direction** in terms of the comparisons of
the neighbours `a`, `b` with the corner `v` and the orientation of `a, v, b`. -/
theorem sideLeftOf_horiz_iff (a v b : Point) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    sideLeftOf a v b (Visibility.rayPt v s 1) ↔
      SecProp (s = 1) (0 < det a v b) (det a v b = 0) (v.2 < b.2) (b.2 < v.2) (v.1 < b.1)
        (b.1 < v.1) (v.2 < a.2) (a.2 < v.2) (v.1 < a.1) (a.1 < v.1) := by
  unfold sideLeftOf
  have hx : Visibility.rayPt v s 1 - v = ((s, 0) : Point) := by
    refine Prod.ext ?_ ?_ <;> simp [Visibility.rayPt]
  rw [hx, sideCcw_horiz_iff _ _ hs, Chazelle.Chain.sideCross_corner]
  simp [Prod.fst_sub, Prod.snd_sub, sub_pos, sub_neg]

/-- The sector formula as a Boolean formula over bit registers `r₀ … r₁₀` (in the order of the
arguments of `SecProp`). -/
def secBF (sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : ℕ) : BF :=
  let v := BF.var
  let bx := BF.or (.and (v sp) (v b2n)) (.and (.not (v sp)) (v b2p))
  let xa := BF.or (.and (v sp) (v a2p)) (.and (.not (v sp)) (v a2n))
  let dn := BF.or (.or (.and (v b2p) (v a2n)) (.and (v b2n) (v a2p)))
    (.or (.and (v b1p) (v a1n)) (.and (v b1n) (v a1p)))
  let dp := BF.or (.or (.and (v b2p) (v a2p)) (.and (v b2n) (v a2n)))
    (.or (.and (v b1p) (v a1p)) (.and (v b1n) (v a1n)))
  let nz := BF.or (v b2p) (v b2n)
  let dbxn := BF.or (.and (v sp) (v b1n)) (.and (.not (v sp)) (v b1p))
  .or (.or (.and (v oP) (.and bx xa)) (.and (.not (v oP)) (.and (.not (v oZ)) (.or bx xa))))
    (.or (.and (v oZ) (.and dn bx)) (.and (v oZ) (.and dp (.or nz dbxn))))

/-- The Boolean formula evaluates to the sector formula. -/
theorem secBF_eval (v : ℕ → Bool) (sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : ℕ) :
    (secBF sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n).eval v = true ↔
      SecProp (v sp) (v oP) (v oZ) (v b2p) (v b2n) (v b1p) (v b1n) (v a2p) (v a2n) (v a1p)
        (v a1n) := by
  simp [secBF, BF.eval, SecProp, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.not_eq_true]
  cases v sp <;> cases v oP <;> cases v oZ <;> simp [or_assoc]

/-- The variables of the sector formula. -/
theorem secBF_vars {p : ℕ → Prop} {sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n : ℕ}
    (h : ∀ r ∈ [sp, oP, oZ, b2p, b2n, b1p, b1n, a2p, a2n, a1p, a1n], p r) :
    (secBF sp oP oZ b2p b2n b1p b1n a2p a2n a1p a1n).VarsOK p := by
  simp [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp [secBF, BF.VarsOK, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, and_self]

end

end SweepPrim

end Chazelle.Core
