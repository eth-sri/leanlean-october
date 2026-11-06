module

public import Chazelle.Core.DownPhaseMathRec2

/-!
# Down phase, math (H-R1): the walk-order point list of the driver's host

`DrvR.regHost li n N r` lists its items in increasing index of `Q`; read in walk order (runs
reversed when `¬ LeftInside Q`) the points are `wpts`.  This file has the list tools:

* `RepFrom li Q S R L i`: the list `L` represents the host keys of `R` from index `i` on;
  `repFrom_append`, `repFrom_flatMap` (groups of lengths `grpLen` at offsets `grpOff`),
  `repFrom_rotate`;
* `regHost_pts`: the points of `regHost` are the walk-order points (reversed if `¬ li`);
* `runCnt_eq`, `runPts`: the run items of an arc list the walk vertices `s.edge + 1, …` in walk
  order.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open DownHost
open DrvR (ivB qE atVtx partner ptI runCnt runItems arcItems walkItems regHost)

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-! ## Representing lists -/

/-- **The list `L` represents the host keys of `R` from index `i` on.** -/
def RepFrom (li : Bool) (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (L : List SymPt)
    (i : ℕ) : Prop :=
  ∀ j, j < L.length → RepPt li Q S R ((i + j) % nk (interiorModel Q) S R) (L.getD j (.vtx 0))

theorem repFrom_nil (li : Bool) (i : ℕ) : RepFrom li Q S R [] i := fun j hj => by simp at hj

theorem repFrom_single {li : Bool} {s : SymPt} {i : ℕ}
    (h : RepPt li Q S R (i % nk (interiorModel Q) S R) s) : RepFrom li Q S R [s] i := by
  intro j hj
  simp only [List.length_singleton] at hj
  obtain rfl : j = 0 := by omega
  simpa using h

theorem repFrom_append {li : Bool} {L L' : List SymPt} {i : ℕ} (h : RepFrom li Q S R L i)
    (h' : RepFrom li Q S R L' (i + L.length)) : RepFrom li Q S R (L ++ L') i := by
  intro j hj
  rw [List.length_append] at hj
  rcases Nat.lt_or_ge j L.length with hjL | hjL
  · rw [List.getD_append _ _ _ _ hjL]; exact h j hjL
  · rw [List.getD_append_right _ _ _ _ hjL]
    have := h' (j - L.length) (by omega)
    rwa [show i + L.length + (j - L.length) = i + j by omega] at this

/-- The length of the group of host keys of arc `t`: its `d t + 1` keys from the start to the
key before the next group, plus the junction. -/
theorem repFrom_flatMap {li : Bool} (G : ℕ → List SymPt) (d J : ℕ → ℕ) (i : ℕ) (k : ℕ)
    (hG : ∀ t, t < k → RepFrom li Q S R (G t) (i + grpOff d J t) ∧ (G t).length = grpLen d J t) :
    RepFrom li Q S R ((List.range k).flatMap G) i ∧
      ((List.range k).flatMap G).length = grpOff d J k := by
  induction k with
  | zero => exact ⟨repFrom_nil li i, by simp [grpOff]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih fun t ht => hG t (by omega)
    obtain ⟨h3, h4⟩ := hG k (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨repFrom_append h1 (by rwa [h2]), ?_⟩
    rw [List.length_append, h2, h4, grpOff_succ]

theorem repFrom_rotate {li : Bool} {L : List SymPt} {i : ℕ}
    (hL : L.length = nk (interiorModel Q) S R) (h : RepFrom li Q S R L i) (m : ℕ) :
    RepFrom li Q S R (L.rotate m) (i + m) := by
  intro j hj
  rw [List.length_rotate] at hj
  have hpos : 0 < L.length := by omega
  have hjm := h ((j + m) % L.length) (Nat.mod_lt _ hpos)
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_rotate]), List.getElem_rotate,
    ← List.getD_eq_getElem _ (.vtx 0) (Nat.mod_lt _ hpos)]
  have e : (i + (j + m) % L.length) % nk (interiorModel Q) S R =
      (i + m + j) % nk (interiorModel Q) S R := by
    rw [hL, Nat.add_mod_mod]; congr 1; ring
  rwa [e] at hjm

/-! ## The points of the driver's host in walk order -/

/-- The points of a host item in walk order. -/
def wpts (li : Bool) (n : ℕ) (it : HostItem) : List SymPt :=
  if li then it.pts n else (it.pts n).reverse

/-- **The points of `regHost`**: the walk-order points of the walk items, reversed if `¬ li`. -/
theorem regHost_pts (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    (regHost li n N r).pts n =
      if li then (walkItems li n N r).flatMap (wpts li n)
      else ((walkItems li n N r).flatMap (wpts li n)).reverse := by
  unfold regHost Host.pts
  cases li
  · simp only [Bool.false_eq_true, ite_false]
    rw [List.reverse_flatMap]
    congr 1
    funext it
    simp [wpts]
  · simp only [ite_true]
    congr 1

theorem wpts_pt (li : Bool) (n : ℕ) (x : SymPt) : wpts li n (.pt x) = [x] := by
  unfold wpts; cases li <;> simp [HostItem.pts]

/-! ## Runs -/

/-- `(y + n - 1 - x) mod n` for `y ≡ x + c (mod n)`: the arithmetic of `runCnt`. -/
theorem runCnt_arith {n x c y : ℕ} (hx : x < n) (hc : 1 ≤ c) (hcn : c ≤ n)
    (hy : y = (x + c) % n) : (y + n - 1 - x) % n = c - 1 := by
  subst hy
  by_cases h : x + c < n
  · rw [Nat.mod_eq_of_lt h, show x + c + n - 1 - x = (c - 1) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · have e : (x + c) % n = x + c - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e, show x + c - n + n - 1 - x = c - 1 by omega, Nat.mod_eq_of_lt (by omega)]

/-- The points of a run of `c` walk vertices from `x + 1` on, in walk order. -/
theorem run_wpts {li : Bool} {n x c : ℕ} (_hn : 0 < n) (hx : x < n) (hc : c < n) (hc0 : 0 < c) :
    let items : List HostItem := if li then [.run ((x + 1) % n) (c - 1)]
      else [.run (n - 1 - (x + c) % n) (c - 1)]
    (items.flatMap (wpts li n)).length = c ∧
      ∀ m, m < c → (items.flatMap (wpts li n)).getD m (.vtx 0) =
        .vtx (ivB li n ((x + (m + 1)) % n)) := by
  intro items
  cases li
  · -- clockwise: the run is reversed
    simp only [items, Bool.false_eq_true, ite_false, List.flatMap_singleton, wpts, HostItem.pts]
    refine ⟨by simp; omega, fun m hm => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1
    unfold ivB
    simp only [Bool.false_eq_true, ite_false]
    rw [show c - 1 + 1 - 1 - m = c - 1 - m by omega]
    -- `(n - 1 - (x + c) % n + (c - 1 - m)) % n = n - 1 - (x + (m + 1)) % n`
    by_cases h1 : x + c < n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (show x + (m + 1) < n by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · have e1 : (x + c) % n = x + c - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e1]
      by_cases h2 : x + (m + 1) < n
      · rw [Nat.mod_eq_of_lt h2, show n - 1 - (x + c - n) + (c - 1 - m) = (n - 2 - x - m) + n
          by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · have e2 : (x + (m + 1)) % n = x + (m + 1) - n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [e2, Nat.mod_eq_of_lt (by omega)]
        omega
  · simp only [items, ite_true, List.flatMap_singleton, wpts, HostItem.pts]
    refine ⟨by simp; omega, fun m hm => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1
    unfold ivB
    simp only [ite_true]
    rw [Nat.mod_add_mod, show x + 1 + m = x + (m + 1) by ring]

end

end DownMath

end Chazelle.Core
