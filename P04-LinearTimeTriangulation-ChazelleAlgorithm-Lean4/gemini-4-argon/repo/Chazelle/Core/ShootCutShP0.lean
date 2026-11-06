module

public import Chazelle.Core.ShootCutShMerge

/-!
# WP-G, part 47: the segments of a kind-0 piece

For a kind-0 piece from `x` to `y` (`D = pcD n x.edge y.edge` further edges), the `d`-th
segment runs from `pcU x d` to `pcV y D d` on the walk edge `pcEdge n x.edge d`
(`pc0_geo`, `pc0_seg`), and the last edge is the edge of `y` (`pcEdge_D`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)

namespace ShootCut

/-- The start of the `d`-th segment. -/
def pcU (n : ℕ) (x : WPos) (d : ℕ) : WPos := if d = 0 then x else ⟨pcEdge n x.edge d, 0⟩

/-- The end of the `d`-th segment. -/
def pcV (n : ℕ) (x y : WPos) (D d : ℕ) : WPos :=
  if d = D then y else ⟨pcEdge n x.edge (d + 1), 0⟩

theorem pcEdge_D {n sE eE : ℕ} (hs : sE < n) (he : eE < n) : pcEdge n sE (pcD n sE eE) = eE := by
  unfold pcEdge pcD
  rcases Nat.lt_or_ge eE sE with h | h
  · rw [Nat.mod_eq_of_lt (show eE + n - sE < n by omega),
      show sE + (eE + n - sE) = eE + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  · rw [show eE + n - sE = (eE - sE) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show eE - sE < n by omega), show sE + (eE - sE) = eE by omega,
      Nat.mod_eq_of_lt he]

theorem pcEdge_lt {n sE : ℕ} (hn : 0 < n) (d : ℕ) : pcEdge n sE d < n := Nat.mod_lt _ hn

theorem pcEdge_succ (n sE d : ℕ) : pcEdge n sE (d + 1) = (pcEdge n sE d + 1) % n := by
  unfold pcEdge; rw [Nat.add_comm ((sE + d) % n) 1, Nat.add_mod_mod, ← Nat.add_assoc,
    Nat.add_comm 1]

variable {C : Chain} {Q : Polygon}

/-- **The ends of the `d`-th segment** as points of the walk edge. -/
theorem pc0_pts {x y : WPos} (hxn : x.edge < 2 * C.m + 7) (hyn : y.edge < 2 * C.m + 7) {d : ℕ}
    (hd : d ≤ pcD (2 * C.m + 7) x.edge y.edge) :
    (chainModel C).pos Q (pcU (2 * C.m + 7) x d) =
        lerp ((chainModel C).wa (pcEdge (2 * C.m + 7) x.edge d))
          ((chainModel C).wb (pcEdge (2 * C.m + 7) x.edge d)) (pcA ((chainModel C).param Q x) d) ∧
      (chainModel C).pos Q (pcV (2 * C.m + 7) x y (pcD (2 * C.m + 7) x.edge y.edge) d) =
        lerp ((chainModel C).wa (pcEdge (2 * C.m + 7) x.edge d))
          ((chainModel C).wb (pcEdge (2 * C.m + 7) x.edge d))
          (pcB (pcD (2 * C.m + 7) x.edge y.edge) ((chainModel C).param Q y) d) := by
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  set n := 2 * C.m + 7
  set D := pcD n x.edge y.edge
  constructor
  · unfold pcU pcA
    by_cases h0 : d = 0
    · subst h0
      simp only [↓reduceIte]
      rw [show pcEdge n x.edge 0 = x.edge by unfold pcEdge; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn]]
      rfl
    · simp only [h0, ↓reduceIte]; rfl
  · unfold pcV pcB
    by_cases hD : d = D
    · subst hD
      simp only [↓reduceIte]
      rw [pcEdge_D hxn hyn]; rfl
    · simp only [hD, ↓reduceIte]
      rw [lerp_one']
      show lerp ((chainModel C).wa _) ((chainModel C).wb _) 0 = _
      rw [lerp_zero']
      unfold Model.wa Model.wb
      rw [hnW, pcEdge_succ]

theorem pc0_ab {x y : WPos} {N : ℕ} (hx : ProperPos (chainModel C) Q N x)
    (hy : ProperPos (chainModel C) Q N y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1) (d : ℕ) :
    0 ≤ pcA ((chainModel C).param Q x) d ∧
      pcA ((chainModel C).param Q x) d ≤ pcB (pcD (2 * C.m + 7) x.edge y.edge)
        ((chainModel C).param Q y) d ∧
      pcB (pcD (2 * C.m + 7) x.edge y.edge) ((chainModel C).param Q y) d ≤ 1 := by
  have hx0 := hx.1
  have hx1 := hx.2.1
  have hy0 := hy.1
  have hy1 := hy.2.1
  unfold pcA pcB
  by_cases h0 : d = 0 <;> by_cases hD : d = pcD (2 * C.m + 7) x.edge y.edge
  · -- one edge
    rw [ite_eq_left h0, ite_eq_left hD]
    have hxy : x.edge = y.edge := by
      have := pcEdge_D (n := 2 * C.m + 7) hxn hyn
      rw [← hD, h0] at this
      unfold pcEdge at this; rwa [Nat.add_zero, Nat.mod_eq_of_lt hxn] at this
    exact ⟨hx0, (piece0_nowrap hx hy hxy hxn hwt).le, hy1.le⟩
  · rw [ite_eq_left h0, ite_eq_right hD]; exact ⟨hx0, hx1.le, le_rfl⟩
  · rw [ite_eq_right h0, ite_eq_left hD]; exact ⟨le_rfl, hy0, hy1.le⟩
  · rw [ite_eq_right h0, ite_eq_right hD]; exact ⟨le_rfl, zero_le_one, le_rfl⟩


/-- The segments `0 … d' - 1` of a kind-0 piece. -/
def segSet (C : Chain) (Q : Polygon) (x y : WPos) (d' : ℕ) : Set Point :=
  ⋃ d ∈ List.range d', seg ((chainModel C).pos Q (pcU (2 * C.m + 7) x d))
    ((chainModel C).pos Q (pcV (2 * C.m + 7) x y (pcD (2 * C.m + 7) x.edge y.edge) d))

theorem segSet_zero (x y : WPos) : segSet C Q x y 0 = ∅ := by
  unfold segSet; simp

theorem segSet_succ (x y : WPos) (d : ℕ) : segSet C Q x y (d + 1) = segSet C Q x y d ∪
    seg ((chainModel C).pos Q (pcU (2 * C.m + 7) x d))
      ((chainModel C).pos Q (pcV (2 * C.m + 7) x y (pcD (2 * C.m + 7) x.edge y.edge) d)) := by
  unfold segSet
  rw [List.range_succ]
  ext p; simp [or_comm]

/-- **The segments of a kind-0 piece cover it.** -/
theorem segSet_full {N : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q N x)
    (hy : ProperPos (chainModel C) Q N y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1) :
    segSet C Q x y (pcD (2 * C.m + 7) x.edge y.edge + 1) =
      (chainModel C).arcSet ((chainModel C).key Q x) ((chainModel C).key Q y) := by
  rw [piece0_union hx hy hxn hyn hwt]
  unfold segSet pcSet
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  ext p
  simp only [mem_iUnion, List.mem_range, exists_prop]
  constructor
  · rintro ⟨d, hd, hp⟩
    refine ⟨d, hd, ?_⟩
    obtain ⟨hU, hV⟩ := pc0_pts (Q := Q) hxn hyn (d := d) (by omega)
    obtain ⟨a0, ab, b1⟩ := pc0_ab hx hy hxn hyn hwt d
    rwa [hnW, subSeg_eq_seg _ _ ab, ← hU, ← hV]
  · rintro ⟨d, hd, hp⟩
    refine ⟨d, hd, ?_⟩
    obtain ⟨hU, hV⟩ := pc0_pts (Q := Q) hxn hyn (d := d) (by omega)
    obtain ⟨a0, ab, b1⟩ := pc0_ab hx hy hxn hyn hwt d
    rwa [hnW, subSeg_eq_seg _ _ ab, ← hU, ← hV] at hp

end ShootCut

end

end Chazelle.Core
