module

public import Chazelle.Core.SweepIoRec

/-!
# The sweep RAM (WP-D), answers: walk positions of the shared vertex and of the top

The walk positions of a chain vertex `k` are the tour vertices `6 + i` with `sideIdx i = k`
(`vtx_pos_iff`).  For an end vertex of the chain (`k = 0`, the shared vertex of `C₂`, or `k = m`,
the shared vertex of `C₁`) these are `6 + tpos C k` and, when `tpos C k = 0`, also `2m + 6`
(`endIdx`); for the top vertex `T` they are `0`, `2m` and `midT` (`topIdx_iff`).  With a
normalised height code (`0` iff the parameter is `0`) these are index tests on the RAM.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc sideE)

@[expose] public section

/-- **The walk positions of a chain vertex.** -/
theorem vtx_pos_iff (C : Chain) (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {p : ℕ}
    (hp : p < (chainModel C).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    sidePt (chainModel C).W p t = C.vertex k ↔
      t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx C.sideBeta i = k := by
  constructor
  · exact SweepPrim.vertex_positions C hP hk hp ht0 ht1
  · rintro ⟨rfl, i, hi, rfl, hidx⟩
    rw [Chazelle.Chain.sidePt_zero]
    show (C.sideWalk C.sideBeta).vtx (i + 6) = _
    rw [C.sideWalk_vtx_tour _ hi]
    unfold Chain.sideTour; rw [hidx]

/-- A residue of a number below `3 n`. -/
theorem mod_three {a n : ℕ} (_hn : 0 < n) (ha : a < 3 * n) :
    a % n = if a < n then a else if a < 2 * n then a - n else a - 2 * n := by
  split_ifs with h1 h2
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The tour positions of an end vertex.** -/
theorem endIdx (C : Chain) {k : ℕ} (hk : k = 0 ∨ k = C.m) {i : ℕ} (hi : i ≤ 2 * C.m) :
    C.sideIdx C.sideBeta i = k ↔ i = tpos C k ∨ (i = 2 * C.m ∧ tpos C k = 0) := by
  have hS := C.sideS_lt C.sideBeta
  have hm := C.one_le
  have h2m : 0 < 2 * C.m := by omega
  rw [Chain.sideIdx_eq]
  unfold tpos bS sideE
  set S := C.sideS C.sideBeta
  rw [mod_three h2m (show S + i < 3 * (2 * C.m) by omega),
    mod_three h2m (show k + 2 * C.m - S < 3 * (2 * C.m) by omega)]
  rcases hk with rfl | rfl <;> split_ifs <;> omega

/-- The middle visit of the top in the tour. -/
noncomputable def midT (C : Chain) : ℕ :=
  if C.sideBeta then 2 * C.m - 2 * C.topIdx else if C.topIdx < C.m then 2 * C.topIdx else 0

/-- **The tour positions of the top vertex.** -/
theorem topIdx_iff (C : Chain) {i : ℕ} (hi : i ≤ 2 * C.m) :
    C.sideIdx C.sideBeta i = C.topIdx ↔ i = 0 ∨ i = 2 * C.m ∨ i = midT C := by
  have hT := C.topIdx_le
  have hm := C.one_le
  have h2m : 0 < 2 * C.m := by omega
  rw [Chain.sideIdx_eq]
  unfold midT sideE Chain.sideS
  cases hβ : C.sideBeta
  · simp only [Bool.false_eq_true, ite_false]
    rw [mod_three h2m (show 2 * C.m - C.topIdx + i < 3 * (2 * C.m) by omega)]
    split_ifs <;> omega
  · simp only [ite_true]
    rw [mod_three h2m (show C.topIdx + i < 3 * (2 * C.m) by omega)]
    split_ifs <;> omega

/-! ## Positions -/

/-- The normalised height code is `0` iff the parameter is `0` (proper positions). -/
theorem nhgt_eq_zero_iff (M : Model) (Q : Polygon) (u : WPos) :
    nhgt M Q u = 0 ↔ M.param Q u = 0 := by
  unfold nhgt Restore.normOf
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    intro h0
    apply h
    obtain ⟨e, hh⟩ := u
    simp only at h0
    subst h0
    rfl

/-- **A position is at an end vertex** (`k = 0` or `k = m`) iff its parameter is `0` and its edge
is `6 + tpos C k`, or `2m + 6` when `tpos C k = 0`. -/
theorem atEnd_iff (C : Chain) (hP : C.P.Simple) {k : ℕ} (hk : k = 0 ∨ k = C.m) (Q : Polygon)
    {x : WPos} (hx : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x = C.vertex k ↔ (chainModel C).param Q x = 0 ∧
      (x.edge = 6 + tpos C k ∨ (x.edge = 2 * C.m + 6 ∧ tpos C k = 0)) := by
  have hkm : k ≤ C.m := by rcases hk with rfl | rfl <;> omega
  rw [pos_eq_sidePt' C Q x, vtx_pos_iff C hP hkm hx h0 h1]
  have hn := cm_n C
  constructor
  · rintro ⟨ht, i, hi, hp, hidx⟩
    refine ⟨ht, ?_⟩
    rcases (endIdx C hk hi).1 hidx with h | ⟨h, h'⟩
    · left; omega
    · right; omega
  · rintro ⟨ht, h | ⟨h, h'⟩⟩
    · have hτ := tpos_lt C k
      refine ⟨ht, tpos C k, by omega, by omega, (endIdx C hk (by omega)).2 (Or.inl rfl)⟩
    · refine ⟨ht, 2 * C.m, le_rfl, by omega, (endIdx C hk le_rfl).2 (Or.inr ⟨rfl, h'⟩)⟩

/-- **A position is at the top** iff its parameter is `0` and its edge is `6`, `2m + 6` or
`6 + midT`. -/
theorem atTop_iff (C : Chain) (hP : C.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x = C.top ↔ (chainModel C).param Q x = 0 ∧
      (x.edge = 6 ∨ x.edge = 2 * C.m + 6 ∨ x.edge = 6 + midT C) := by
  have hn := cm_n C
  have hmid : midT C ≤ 2 * C.m := by
    unfold midT; have := C.topIdx_le; split_ifs <;> omega
  show _ = C.vertex C.topIdx ↔ _
  rw [pos_eq_sidePt' C Q x, vtx_pos_iff C hP C.topIdx_le hx h0 h1]
  constructor
  · rintro ⟨ht, i, hi, hp, hidx⟩
    refine ⟨ht, ?_⟩
    rcases (topIdx_iff C hi).1 hidx with h | h | h <;> omega
  · rintro ⟨ht, h | h | h⟩
    · exact ⟨ht, 0, by omega, by omega, (topIdx_iff C (by omega)).2 (Or.inl rfl)⟩
    · exact ⟨ht, 2 * C.m, le_rfl, by omega, (topIdx_iff C le_rfl).2 (Or.inr (Or.inl rfl))⟩
    · exact ⟨ht, midT C, hmid, by omega, (topIdx_iff C hmid).2 (Or.inr (Or.inr rfl))⟩

end

end SweepIo

end Chazelle.Core
