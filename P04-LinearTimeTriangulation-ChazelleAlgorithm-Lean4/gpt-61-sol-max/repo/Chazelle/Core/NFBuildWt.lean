module

public meta import Chazelle.Arithmetic

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
    · ram_grind
    · rintro ⟨h1, h2⟩
      -- a point of `(max a p, min b (p + 1))`
      refine ⟨(max a p + min b (p + 1)) / 2 - p, ?_, ?_, ?_, ?_⟩
      · grind
      · grind
      all_goals grind
  · constructor
    · ram_grind
    · rintro (h1 | h1)
      · refine ⟨(min b (p + 1) - p) / 2, ?_, ?_, Or.inr ?_⟩
        all_goals grind
      · refine ⟨(max a p + (p + 1)) / 2 - p, ?_, ?_, Or.inl ?_⟩
        all_goals grind

section
variable {p e : ℕ} {f : ℝ} (hf : 0 ≤ f ∧ f < 1)
include hf
/-- For a key `e + f` with `0 ≤ f < 1`: `p < e + f ↔ p < ceil`. -/
theorem lt_key_iff :
    (p : ℝ) < e + f ↔ p < keyCeil e f := by
  unfold keyCeil
  split_ifs with h
  · simp_all
  · have hf0 : 0 < f := lt_of_le_of_ne hf.1 (Ne.symm h)
    constructor
    · intro h1
      have : (p : ℝ) < e + 1 := by linarith
      exact_mod_cast this
    · intro h1
      have : p ≤ e := by omega
      have : (p : ℝ) ≤ e := by simp_all
      linarith

/-- For a key `e + f` with `0 ≤ f < 1`: `e + f < p + 1 ↔ e ≤ p`. -/
theorem key_lt_succ_iff :
    (e : ℝ) + f < p + 1 ↔ e ≤ p := by
  constructor
  · intro h
    have : (e : ℝ) < p + 1 := by linarith
    have : e < p + 1 := by exact_mod_cast this
    omega
  · intro h
    have : (e : ℝ) ≤ p := by simp_all
    linarith


end

section
variable {lo hi : ℕ} (hc : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < hi)) (hhi : hi ≤ M.W.n)
include hc hhi
/-- **The weight of an arc in closed form.**  If the counted walk edges are exactly `[lo, hi)`
with `hi ≤ n`, the weight of the open cyclic key interval from `ea + fa` to `eb + fb` (fractional
parts in `[0, 1)`) is `arcWtNat lo hi ea fa eb fb`. -/
theorem arcWt_closed
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
      grind
    grind [ncard_coe_finset, Nat.card_Ico]
  · have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        sideInArc (ea + fa) (eb + fb) (p + t)} =
        ↑(Finset.Ico lo hi \ Finset.Ico (max (keyCeil eb fb) lo) (min ea hi)) := by
      ext p
      simp only [mem_ofPred_eq, Finset.coe_sdiff, Finset.coe_Ico, mem_sdiff, mem_Ico,
        mem_arcEdges_iff, ite_eq_right h, lt_key_iff hfb, key_lt_succ_iff hfa, max_le_iff,
        lt_min_iff]
      grind
    rw [hset, ncard_coe_finset, Finset.card_sdiff_of_subset, Nat.card_Ico, Nat.card_Ico]
    grind

/-- **The weight of an arc between two walk positions** of the walk proper (parameters in
`[0, 1)`), over counted edges `[lo, hi)`: the closed form of `arcWt_closed` with the edges and
parameters of the two positions. -/
theorem arcWt_key
    (Q : Polygon) {x y : WPos} (hx : 0 ≤ M.param Q x ∧ M.param Q x < 1)
    (hy : 0 ≤ M.param Q y ∧ M.param Q y < 1) :
    M.arcWt (M.key Q x) (M.key Q y) =
      arcWtNat lo hi x.edge (M.param Q x) y.edge (M.param Q y) :=
  M.arcWt_closed hc hhi hx hy


end

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
  grind [interiorModel, interiorWalk, Polygon.n]

/-- The interior model counts every walk edge. -/
theorem interiorModel_counted_iff (Q : Polygon) (p : ℕ) (hp : p < (interiorModel Q).W.n) :
    (interiorModel Q).counted p ↔ 0 ≤ p ∧ p < Q.n := by
  rw [interiorModel_n] at hp
  exact ⟨fun _ => ⟨Nat.zero_le _, hp⟩, fun _ => trivial⟩

end

end Chazelle.Core
