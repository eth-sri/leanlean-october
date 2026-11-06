module

public import Chazelle.Golf

public import Chazelle.Core.SpecNF

/-!
# WP-C (BuildNF): the weight of an arc in closed form

`Model.arcWt a b` counts the counted walk edges met by the open cyclic key interval `(a, b)`.  In
both good models the counted edges form an interval of walk edges (`[6, 2m + 6)` in the chain
model, all `n` edges in the interior model), so the weight of an arc is O(1) arithmetic on the
edges of its two ends and one bit per end (whether the end lies strictly inside its edge).

## Results

* `Model.mem_arcEdges_iff`: the walk edge `p` meets `(a, b)` iff `p < b ∧ a < p + 1` (for
  `a < b`) or `p < b ∨ a < p + 1` (for `a ≥ b`, the wrapping interval).
* `Model.arcWt_closed`: for keys `a = ea + fa`, `b = eb + fb` with fractional parts in `[0, 1)` and
  counted edges `[lo, hi)`, `hi ≤ n`:
  `arcWt a b = min (ceil b) hi - max ea lo` if `a < b`, and
  `(hi - lo) - (min ea hi - max (ceil b) lo)` otherwise, where `ceil b = eb + [fb ≠ 0]`.
* `Model.arcWt_key`: the same for the keys of two walk positions of the walk proper.
* `chainModel_counted_iff`, `chainModel_n`, `interiorModel_counted_iff`, `interiorModel_n`: the
  counted intervals of the two good models.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)

/-- The ceiling of a key `e + f` with `0 ≤ f < 1`: `e` if `f = 0`, `e + 1` otherwise. -/
noncomputable def keyCeil (e : ℕ) (f : ℝ) : ℕ := if f = 0 then e else e + 1

/-- The closed form of the weight of the arc from `ea + fa` to `eb + fb` over the counted edges
`[lo, hi)`. -/
noncomputable def arcWtNat (lo hi ea : ℕ) (fa : ℝ) (eb : ℕ) (fb : ℝ) : ℕ :=
  if (ea : ℝ) + fa < eb + fb then min (keyCeil eb fb) hi - max ea lo
  else (hi - lo) - (min ea hi - max (keyCeil eb fb) lo)

namespace Model

variable (M : Model)

/-- **The walk edges met by an open cyclic key interval.** -/
theorem mem_arcEdges_iff (a b : ℝ) (p : ℕ) :
    (∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)) ↔
      (if a < b then (p : ℝ) < b ∧ a < p + 1 else ((p : ℝ) < b ∨ a < p + 1)) := by
  unfold sideInArc
  split_ifs with h
  · constructor
    · rintro ⟨t, ht0, ht1, h1, h2⟩
      exact ⟨⟡, ⟡⟩
    · rintro ⟨h1, h2⟩
      -- a point of `(max a p, min b (p + 1))`
      refine ⟨(max a p + min b (p + 1)) / 2 - p, ?_, ?_, ?_, ?_⟩
      · have : max a p < min b (p + 1) := max_lt (lt_min h h2) (lt_min h1 (⟡))
        have : (p : ℝ) ≤ max a p := le_max_right _ _
        linarith
      · have : min b (p + 1) ≤ (p : ℝ) + 1 := min_le_right _ _
        have : max a p < min b (p + 1) := max_lt (lt_min h h2) (lt_min h1 (⟡))
        linarith
      · have : max a p < min b (p + 1) := max_lt (lt_min h h2) (lt_min h1 (⟡))
        have : a ≤ max a p := le_max_left _ _
        linarith
      · have : max a p < min b (p + 1) := max_lt (lt_min h h2) (lt_min h1 (⟡))
        have : min b (p + 1) ≤ b := min_le_left _ _
        linarith
  · constructor
    · rintro ⟨t, ht0, ht1, h1 | h1⟩
      · right; linarith
      · left; linarith
    · rintro (h1 | h1)
      · refine ⟨(min b (p + 1) - p) / 2, ?_, ?_, Or.inr ?_⟩
        · have : (p : ℝ) < min b (p + 1) := lt_min h1 (⟡)
          linarith
        · have : min b (p + 1) ≤ (p : ℝ) + 1 := min_le_right _ _
          linarith
        · have : (p : ℝ) < min b (p + 1) := lt_min h1 (⟡)
          have : min b (p + 1) ≤ b := min_le_left _ _
          linarith
      · refine ⟨(max a p + (p + 1)) / 2 - p, ?_, ?_, Or.inl ?_⟩
        · have : max a p < (p : ℝ) + 1 := max_lt h1 (⟡)
          have : (p : ℝ) ≤ max a p := le_max_right _ _
          linarith
        · have : max a p < (p : ℝ) + 1 := max_lt h1 (⟡)
          have : (p : ℝ) ≤ max a p := le_max_right _ _
          linarith
        · have : max a p < (p : ℝ) + 1 := max_lt h1 (⟡)
          have : a ≤ max a p := le_max_left _ _
          linarith

/-- For a key `e + f` with `0 ≤ f < 1`: `p < e + f ↔ p < ceil`. -/
theorem lt_key_iff {p e : ℕ} {f : ℝ} (hf : 0 ≤ f ∧ f < 1) :
    (p : ℝ) < e + f ↔ p < keyCeil e f := by
  unfold keyCeil
  split_ifs with h
  · rw [h, add_zero]; exact Nat.cast_lt
  · have hf0 : 0 < f := lt_of_le_of_ne hf.1 (Ne.symm h)
    constructor
    · intro h1
      have : (p : ℝ) < e + 1 := by linarith [hf.2]
      exact_mod_cast this
    · intro h1
      have : p ≤ e := ⋄
      have : (p : ℝ) ≤ e := by exact_mod_cast this
      linarith

/-- For a key `e + f` with `0 ≤ f < 1`: `e + f < p + 1 ↔ e ≤ p`. -/
theorem key_lt_succ_iff {p e : ℕ} {f : ℝ} (hf : 0 ≤ f ∧ f < 1) :
    (e : ℝ) + f < p + 1 ↔ e ≤ p := by
  constructor
  · intro h
    have : (e : ℝ) < p + 1 := by linarith [hf.1]
    have : e < p + 1 := by exact_mod_cast this
    omega
  · intro h
    have : (e : ℝ) ≤ p := by exact_mod_cast h
    linarith [hf.2]

/-- **The weight of an arc in closed form.**  If the counted walk edges are exactly `[lo, hi)`
with `hi ≤ n`, the weight of the open cyclic key interval from `ea + fa` to `eb + fb` (fractional
parts in `[0, 1)`) is `arcWtNat lo hi ea fa eb fb`. -/
theorem arcWt_closed {lo hi : ℕ} (hc : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < hi)) (hhi : hi ≤ M.W.n)
    {ea eb : ℕ} {fa fb : ℝ} (hfa : 0 ≤ fa ∧ fa < 1) (hfb : 0 ≤ fb ∧ fb < 1) :
    M.arcWt (ea + fa) (eb + fb) = arcWtNat lo hi ea fa eb fb := by
  unfold arcWt arcWtNat
  split_ifs with h
  · have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        sideInArc (ea + fa) (eb + fb) (p + t)} =
        ↑(Finset.Ico (max ea lo) (min (keyCeil eb fb) hi)) := by
      ext p
      simp only [mem_ofPred_eq, Finset.coe_Ico, mem_Ico, mem_arcEdges_iff, ite_eq_left h,
        lt_key_iff hfb, key_lt_succ_iff hfa, max_le_iff, lt_min_iff]
      constructor
      · rintro ⟨hp, hcp, h3, h4⟩
        obtain ⟨h1, h2⟩ := (hc p hp).1 hcp
        exact ⟨⟨h4, h1⟩, h3, h2⟩
      · rintro ⟨⟨h4, h1⟩, h3, h2⟩
        exact ⟨⋄, (hc p (⋄)).2 ⟨h1, h2⟩, h3, h4⟩
    Ξ hset, ncard_coe_finset, Nat.card_Ico
  · have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        sideInArc (ea + fa) (eb + fb) (p + t)} =
        ↑(Finset.Ico lo hi \ Finset.Ico (max (keyCeil eb fb) lo) (min ea hi)) := by
      ext p
      simp only [mem_ofPred_eq, Finset.coe_sdiff, Finset.coe_Ico, mem_sdiff, mem_Ico,
        mem_arcEdges_iff, ite_eq_right h, lt_key_iff hfb, key_lt_succ_iff hfa, max_le_iff,
        lt_min_iff]
      constructor
      · rintro ⟨hp, hcp, h3⟩
        obtain ⟨h1, h2⟩ := (hc p hp).1 hcp
        refine ⟨⟨h1, h2⟩, ?_⟩; omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⋄, (hc p (⋄)).2 ⟨h1, h2⟩, ?_⟩; omega
    Ξ hset, ncard_coe_finset, Finset.card_sdiff_of_subset, Nat.card_Ico, Nat.card_Ico
    intro p
    ϴ Finset.mem_Ico, max_le_iff, lt_min_iff
    omega

/-- **The weight of an arc between two walk positions** of the walk proper (parameters in
`[0, 1)`), over counted edges `[lo, hi)`: the closed form of `arcWt_closed` with the edges and
parameters of the two positions. -/
theorem arcWt_key {lo hi : ℕ} (hc : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < hi)) (hhi : hi ≤ M.W.n)
    (Q : Polygon) {x y : WPos} (hx : 0 ≤ M.param Q x ∧ M.param Q x < 1)
    (hy : 0 ≤ M.param Q y ∧ M.param Q y < 1) :
    M.arcWt (M.key Q x) (M.key Q y) =
      arcWtNat lo hi x.edge (M.param Q x) y.edge (M.param Q y) :=
  M.arcWt_closed hc hhi hx hy

end Model

/-! ## The counted edges of the good models -/

/-- The chain model counts the walk edges `[6, 2m + 6)` (the double boundary). -/
theorem chainModel_counted_iff (C : Chain) (p : ℕ) (_hp : p < (chainModel C).W.n) :
    (chainModel C).counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6 := Iff.rfl

/-- The walk of the chain model has `2m + 7` edges. -/
theorem chainModel_n (C : Chain) : (chainModel C).W.n = 2 * C.m + 7 :=
  C.sideWalk_n _

/-- The walk of the interior model has `n` edges. -/
theorem interiorModel_n (Q : Polygon) : (interiorModel Q).W.n = Q.n := by
  ϴ interiorModel, interiorWalk
  split_ifs <;> simp [Polygon.n]

/-- The interior model counts every walk edge. -/
theorem interiorModel_counted_iff (Q : Polygon) (p : ℕ) (hp : p < (interiorModel Q).W.n) :
    (interiorModel Q).counted p ↔ 0 ≤ p ∧ p < Q.n := by
  rw [interiorModel_n] at hp
  exact ⟨fun _ => ⟨Nat.zero_le _, hp⟩, fun _ => trivial⟩

end

end Chazelle.Core
