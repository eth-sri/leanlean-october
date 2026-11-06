module

public import Chazelle.Golf

public import Chazelle.Core.ShootCutShSeg

/-!
# WP-G, part 39: a kind-0 piece, walk edge by walk edge

A kind-0 piece from `s'` to `e'` (walk positions of the walk proper, weight at most `1`) of the
chain model of `C` (`n = 2m + 7` walk edges) is answered edge by edge: with
`D = (e'.edge + n - s'.edge) mod n` it meets the walk edges `(s'.edge + d) mod n`, `d ≤ D`, and
on each of them it is the segment from `U_d` to `V_d`:
`U_0 = s'`, `U_d = ⟨(s'.edge + d) mod n, 0⟩` for `d > 0`, `V_D = e'`, `V_d = U_{d+1}` for `d < D`.

* `piece0_nowrap`: if `s'` and `e'` are on one edge, `s'` comes first;
* `piece0_D_le`: `D ≤ 9` (at most seven uncounted edges and one counted edge lie strictly inside);
* `wset_decomp`, `piece0_union`: the point set of the piece is the union of the segments.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp lerp_fst lerp_snd)

namespace ShootCut

/-! ## The edges of a piece -/

/-- The `d`-th walk edge of a piece starting on the edge `sE`. -/
def pcEdge (n sE d : ℕ) : ℕ := (sE + d) % n

/-- The start parameter on the `d`-th edge. -/
noncomputable def pcA (a : ℝ) (d : ℕ) : ℝ := if d = 0 then a else 0

/-- The end parameter on the `d`-th edge. -/
noncomputable def pcB (D : ℕ) (b : ℝ) (d : ℕ) : ℝ := if d = D then b else 1

/-- The union of the sub-segments of the edges `0 … j` of a piece. -/
def pcSet (M : Model) (sE : ℕ) (a : ℝ) (D : ℕ) (b : ℝ) (j : ℕ) : Set Point :=
  ⋃ d ∈ List.range (j + 1), subSeg M (pcEdge M.W.n sE d) (pcA a d) (pcB D b d)

theorem pcSet_succ (M : Model) (sE : ℕ) (a : ℝ) (D : ℕ) (b : ℝ) (j : ℕ) :
    pcSet M sE a D b (j + 1) = pcSet M sE a D b j ∪
      subSeg M (pcEdge M.W.n sE (j + 1)) (pcA a (j + 1)) (pcB D b (j + 1)) := by
  unfold pcSet
  Ξ List.range_succ
  ext x; simp [or_comm]

theorem pcSet_zero (M : Model) (sE : ℕ) (a : ℝ) (D : ℕ) (b : ℝ) :
    pcSet M sE a D b 0 = subSeg M (pcEdge M.W.n sE 0) (pcA a 0) (pcB D b 0) := by
  unfold pcSet; ext x; simp

/-- The sub-segments up to `j < D` do not depend on the end parameter. -/
theorem pcSet_congr (M : Model) (sE : ℕ) (a : ℝ) {D D' : ℕ} {b b' : ℝ} {j : ℕ}
    (h : ∀ d, d ≤ j → pcB D b d = pcB D' b' d) : pcSet M sE a D b j = pcSet M sE a D' b' j := by
  unfold pcSet
  ext x
  ϴ mem_iUnion, List.mem_range, exists_prop
  constructor
  · rintro ⟨d, hd, hx⟩; exact ⟨d, hd, by rw [← h d (⋄)]; exact hx⟩
  · rintro ⟨d, hd, hx⟩; exact ⟨d, hd, by rw [h d (⋄)]; exact hx⟩

theorem nat_split (k n : ℕ) : (k : ℝ) = ((k % n : ℕ) : ℝ) + ((k / n : ℕ) : ℤ) * (n : ℝ) := by
  rw [Int.cast_natCast]; exact_mod_cast (Nat.mod_add_div' k n).symm

/-- **An unwrapped key range from `sE + a` over `D` more edges to `+ b`** is the union of the
sub-segments of its edges. -/
theorem wset_decomp (M : Model) {sE : ℕ} (hn : 0 < M.W.n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ (D : ℕ) {b : ℝ}, 0 ≤ b → b ≤ 1 → (D = 0 → a ≤ b) →
      wset M ((sE : ℝ) + a) ((sE : ℝ) + D + b) = pcSet M sE a D b D
  | 0, b, hb0, hb1, hab => by
    rw [pcSet_zero]
    unfold pcEdge pcA pcB
    simp only [ite_true, Nat.cast_zero, add_zero]
    have hsE := nat_split sE M.W.n
    rw [hsE, show ((sE % M.W.n : ℕ) : ℝ) + ((sE / M.W.n : ℕ) : ℤ) * M.W.n + a =
        ((sE % M.W.n : ℕ) : ℝ) + a + ((sE / M.W.n : ℕ) : ℤ) * M.W.n by ring,
      show ((sE % M.W.n : ℕ) : ℝ) + ((sE / M.W.n : ℕ) : ℤ) * M.W.n + b =
        ((sE % M.W.n : ℕ) : ℝ) + b + ((sE / M.W.n : ℕ) : ℤ) * M.W.n by ring]
    exact wset_edge M (Nat.mod_lt _ hn) ha0 (hab rfl) hb1 _
  | D + 1, b, hb0, hb1, _ => by
    have ih := wset_decomp M (sE := sE) hn ha0 ha1 D (b := 1) zero_le_one le_rfl (fun _ => ha1)
    rw [pcSet_succ, ← pcSet_congr M sE a (D := D) (b := 1) (fun d hd => by
      unfold pcB; split_ifs <;> first | rfl | omega), ← ih]
    have hlast : wset M ((sE : ℝ) + D + 1) ((sE : ℝ) + ↑(D + 1) + b) =
        subSeg M (pcEdge M.W.n sE (D + 1)) (pcA a (D + 1)) (pcB (D + 1) b (D + 1)) := by
      unfold pcEdge pcA pcB
      simp only [Nat.add_one_ne_zero, ite_false, ite_true]
      set q := sE + (D + 1)
      have hq := nat_split q M.W.n
      have e1 : (sE : ℝ) + D + 1 = ((q % M.W.n : ℕ) : ℝ) + 0 + ((q / M.W.n : ℕ) : ℤ) * M.W.n := by
        rw [show ((q % M.W.n : ℕ) : ℝ) + 0 + ((q / M.W.n : ℕ) : ℤ) * (M.W.n : ℝ) = (q : ℝ) by
          rw [hq]; ring]
        simp only [q]; push_cast; ring
      have e2 : (sE : ℝ) + ↑(D + 1) + b =
          ((q % M.W.n : ℕ) : ℝ) + b + ((q / M.W.n : ℕ) : ℤ) * M.W.n := by
        rw [show ((q % M.W.n : ℕ) : ℝ) + b + ((q / M.W.n : ℕ) : ℤ) * (M.W.n : ℝ) = (q : ℝ) + b by
          rw [hq]; ring]
        simp only [q]; push_cast; ring
      rw [e1, e2]
      exact wset_edge M (Nat.mod_lt _ hn) le_rfl hb0 hb1 _
    rw [← hlast, wset_union M (by linarith) (by push_cast; linarith)]

/-! ## The number of edges -/

variable {C : Chain} {Q : Polygon}

/-- **A kind-0 piece within one edge does not wrap around.** -/
theorem piece0_nowrap {n : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hy : ProperPos (chainModel C) Q n y) (hxy : x.edge = y.edge) (hxn : x.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1) :
    (chainModel C).param Q x < (chainModel C).param Q y := by
  rw [arcWt_chain C Q hx hy] at hwt
  by_contra hle
  push Not at hle
  have hm := C.one_le
  have hc := le_keyCeil y.edge ((chainModel C).param Q y)
  have hc' := keyCeil_le y.edge ((chainModel C).param Q y)
  unfold arcWtNat at hwt
  rw [ite_eq_right (by rw [hxy]; push Not; linarith)] at hwt
  omega

/-- The count of a kind-0 piece. -/
def pcD (n sE eE : ℕ) : ℕ := (eE + n - sE) % n

/-- **At most ten edges.** -/
theorem piece0_D_le {n : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hy : ProperPos (chainModel C) Q n y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1) :
    pcD (2 * C.m + 7) x.edge y.edge ≤ 9 := by
  have hnw := piece0_nowrap hx hy
  rw [arcWt_chain C Q hx hy] at hwt
  have hm := C.one_le
  have hc := le_keyCeil y.edge ((chainModel C).param Q y)
  have hc' := keyCeil_le y.edge ((chainModel C).param Q y)
  have hx0 := hx.1
  have hx1 := hx.2.1
  have hy0 := hy.1
  have hy1 := hy.2.1
  unfold pcD
  unfold arcWtNat at hwt
  split_ifs at hwt with hlt
  · -- no wrap in keys: `x.edge ≤ y.edge`
    have hle : x.edge ≤ y.edge := by
      by_contra h
      push Not at h
      have : (y.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h
      linarith
    rw [show y.edge + (2 * C.m + 7) - x.edge = (y.edge - x.edge) + (2 * C.m + 7) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · -- wrap in keys: `y.edge ≤ x.edge`
    have hle : y.edge ≤ x.edge := by
      by_contra h
      push Not at h
      have : (x.edge : ℝ) + 1 ≤ y.edge := by exact_mod_cast h
      exact hlt (by linarith)
    rcases hle.lt_or_eq with hlt' | heq
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [heq, Nat.add_sub_cancel_left, Nat.mod_self]; omega

/-- **The unwrapped end** of a kind-0 piece. -/
theorem piece0_end {n : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hy : ProperPos (chainModel C) Q n y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1) :
    (chainModel C).key Q x + len ((2 * C.m + 7 : ℕ) : ℝ) ((chainModel C).key Q x)
        ((chainModel C).key Q y) =
      (x.edge : ℝ) + (pcD (2 * C.m + 7) x.edge y.edge : ℕ) + (chainModel C).param Q y := by
  have hnw := piece0_nowrap hx hy
  have hx0 := hx.1
  have hx1 := hx.2.1
  have hy0 := hy.1
  have hy1 := hy.2.1
  unfold len pcD Model.key
  split_ifs with hlt
  · have hle : x.edge ≤ y.edge := by
      by_contra h
      push Not at h
      have : (y.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h
      linarith
    rw [show y.edge + (2 * C.m + 7) - x.edge = (y.edge - x.edge) + (2 * C.m + 7) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.cast_sub hle]
    ring
  · have hle : y.edge ≤ x.edge := by
      by_contra h
      push Not at h
      have : (x.edge : ℝ) + 1 ≤ y.edge := by exact_mod_cast h
      exact hlt (by linarith)
    rcases hle.lt_or_eq with hlt' | heq
    · rw [Nat.mod_eq_of_lt (by omega)]
      push_cast [show x.edge ≤ y.edge + (2 * C.m + 7) by omega]
      ring
    · exfalso
      have := hnw heq.symm hxn hwt
      exact hlt (by rw [heq]; linarith)

/-- **A kind-0 piece is the union of its edge segments.** -/
theorem piece0_union {n : ℕ} {x y : WPos} (hx : ProperPos (chainModel C) Q n x)
    (hy : ProperPos (chainModel C) Q n y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) ≤ 1) :
    (chainModel C).arcSet ((chainModel C).key Q x) ((chainModel C).key Q y) =
      pcSet (chainModel C) x.edge ((chainModel C).param Q x) (pcD (2 * C.m + 7) x.edge y.edge)
        ((chainModel C).param Q y) (pcD (2 * C.m + 7) x.edge y.edge) := by
  set M := chainModel C
  have hnW : M.W.n = 2 * C.m + 7 := chainModel_n C
  have hn : 0 < M.W.n := by omega
  have kx := key_range hx hxn
  have ky := key_range hy hyn
  rw [← hnW] at kx ky
  have hL := len_le (M.W.n : ℝ) (M.key Q x) (M.key Q y) kx.1 ky.2
  have hend := piece0_end hx hy hxn hyn hwt
  have hstep := arcSet_step M kx.1 kx.2 ky.1 ky.2 0
  simp only [Int.cast_zero, zero_mul, add_zero] at hstep
  rw [hnW] at hstep
  rw [hstep, hend, show M.key Q x = (x.edge : ℝ) + M.param Q x from rfl]
  refine wset_decomp M (sE := x.edge) hn hx.1 hx.2.1.le (pcD (2 * C.m + 7) x.edge y.edge) hy.1
    hy.2.1.le (fun hD => ?_)
  -- one edge: the start comes first
  have hxy : x.edge = y.edge := by
    unfold pcD at hD
    rcases Nat.lt_or_ge y.edge x.edge with h | h
    · rw [Nat.mod_eq_of_lt (by omega)] at hD; omega
    · rw [show y.edge + (2 * C.m + 7) - x.edge = (y.edge - x.edge) + (2 * C.m + 7) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hD
      omega
  exact (piece0_nowrap hx hy hxy hxn hwt).le

end ShootCut

end

end Chazelle.Core
