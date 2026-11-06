module

public import Chazelle.Ears.Basic
public import Chazelle.Existence.Diagonal

/-!
# The arithmetic ear test

For a simple polygon `P` with `n ≥ 4` and a vertex `i < n`, with `a = vtx (prev i)`,
`v = vtx i`, `b = vtx (next i)`, vertex `i` is the apex of an ear exactly when

* the triangle `a v b` is nondegenerate (`det a v b ≠ 0`),
* no vertex of `P` other than `a, v, b` lies in the closed triangle `convexHull {a, v, b}`, and
* the midpoint of the chord `a b` has odd parity (it is inside the polygon).

`isEar_iff` proves both directions.

* (⇒) `not_mem_earHull_of_isEar`: the ear arc is a simple triangle whose filled region is the
  closed triangle (`filled_eq_triangle`); a vertex of `P` in it is a vertex of the ear arc
  (`exists_arc_vertex_of_mem_filled`, using that the filled regions of the two arcs meet only on
  the chord).  `parity_mid_of_isEar`: the midpoint is on the open chord, off the boundary and in
  the filled region.
* (⇐) `isDiagonal_of_test`: the no-crossing lemma `chord_base_not_mem_boundary`, stated at vertex
  `0` of `P.rotate i`, shows the open chord avoids the boundary; `chord_subset_filled_of_test`:
  the open chord is connected, off the boundary, and its midpoint is filled
  (`segment_subset_filled_of_open`).
-/

namespace Chazelle.Ears

@[expose] public section

open Chazelle.Jordan
open Chazelle.Existence
open Chazelle.Geometry (lerp lerp_zero lerp_one lerp_mem_segment)

variable (P : Polygon) (i : ℕ)

/-- The closed ear triangle at vertex `i`. -/
def earHull (P : Polygon) (i : ℕ) : Set Point :=
  convexHull ℝ ({P.vtx (prevIdx P i), P.vtx i, P.vtx ((i + 1) % P.n)} : Set Point)

/-- The two endpoints of the ear chord are distinct. -/
theorem vtx_prev_ne_vtx_succ (hP : P.Simple) (hi : i < P.n) :
    P.vtx (prevIdx P i) ≠ P.vtx ((i + 1) % P.n) :=
  simple_vtx_ne hP (prevIdx_lt P hi) (Nat.mod_lt _ (by omega))
    (prevIdx_ne_succIdx P hP.1 hi)

/-- The open ear chord avoids the boundary (the chord condition of `IsEar`, unfolded). -/
theorem open_chord_not_mem_boundary_of_isEar (hi : i < P.n) (he : IsEar P i) :
    ∀ p ∈ Chazelle.segment (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)),
      p ≠ P.vtx (prevIdx P i) → p ≠ P.vtx ((i + 1) % P.n) → p ∉ P.boundary := by
  have h := he.1.2.2
  rw [prevIdx_mod P hi, prevIdx_add_two_mod P hi] at h
  exact h

/-! ### The forward direction -/

section
variable (hP : P.Simple) (hi : i < P.n) (he : IsEar P i)
include hP hi he
/-- The filled region of the ear arc is the closed ear triangle. -/
theorem filled_earArc :
    (P.arc (prevIdx P i) 2).filled = earHull P i := by
  rw [filled_eq_triangle _ (simple_earArc P i hP he) (n_arc P _ _)]
  obtain ⟨h0, h1, h2⟩ := vtx_earArc P i hi
  aesop

/-- **No other vertex in an ear.**  If `i` is the apex of an ear, no vertex of `P` other than
`prev i`, `i`, `next i` lies in the closed ear triangle. -/
theorem not_mem_earHull_of_isEar
    {j : ℕ} (hj : j < P.n) (h1 : j ≠ prevIdx P i) (h2 : j ≠ i) (h3 : j ≠ (i + 1) % P.n) :
    P.vtx j ∉ earHull P i := by
  intro hmem
  rw [← filled_earArc P i hP hi he] at hmem
  obtain ⟨k, hk, hkj⟩ := exists_arc_vertex_of_mem_filled P (prevIdx P i) 2 he.1
    (filled_arcs_meet_on_chord P _ 2 hP he.1 (chord_ear_subset_filled P i hi he)) hj hmem
  obtain ⟨e0, e1, e2⟩ := vtx_earArc P i hi
  interval_cases k
  · rw [e0] at hkj
    exact h1 (simple_vtx_inj hP hj (prevIdx_lt P hi) hkj.symm)
  · rw [e1] at hkj
    exact h2 (simple_vtx_inj hP hj hi hkj.symm)
  · rw [e2] at hkj
    exact h3 (simple_vtx_inj hP hj (Nat.mod_lt _ (by omega)) hkj.symm)

/-- **The midpoint of an ear chord is inside.** -/
theorem parity_mid_of_isEar :
    parity P (lerp (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) (1 / 2)) = true := by
  have hab := vtx_prev_ne_vtx_succ P i hP hi
  have hmB : lerp (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) (1 / 2) ∉ P.boundary :=
    open_chord_not_mem_boundary_of_isEar P i hi he _
      (lerp_mem_segment _ _ (by norm_num) (by norm_num)) (lerp_ne_left hab (by norm_num))
      (lerp_ne_right hab (by norm_num))
  rw [← mem_filled_iff hP hmB]
  exact he.2 (lerp_mem_segment _ _ (by norm_num) (by norm_num))

/-! ### The backward direction -/


end

/-- The three fan vertices of `P.rotate i` are `prev i`, `i`, `next i`. -/
theorem vtx_rotate_fan (hn : 2 ≤ P.n) (hi : i < P.n) :
    (P.rotate i).vtx ((P.rotate i).n - 1) = P.vtx (prevIdx P i) ∧
    (P.rotate i).vtx 0 = P.vtx i ∧
    (P.rotate i).vtx 1 = P.vtx ((i + 1) % P.n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [n_rotate, vtx_rotate P i (by omega)]
    grind [prevIdx]
  · rw [vtx_rotate P i (by omega), Nat.add_zero, Nat.mod_eq_of_lt hi]
  · rw [vtx_rotate P i (by omega)]

section
variable (hP : P.Simple) (h4 : 4 ≤ P.n) (hi : i < P.n) (hdet : det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) ≠ 0) (hnone : ∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ (i + 1) % P.n →
      P.vtx j ∉ earHull P i)
include hP h4 hi hdet hnone
/-- **No crossing, at an arbitrary vertex.**  If the ear triangle at `i` is nondegenerate and
contains no vertex other than its corners, the open chord from `prev i` to `next i` avoids the
boundary. -/
theorem open_chord_not_mem_boundary_of_test :
    ∀ p ∈ Chazelle.segment (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)),
      p ≠ P.vtx (prevIdx P i) → p ≠ P.vtx ((i + 1) % P.n) → p ∉ P.boundary := by
  have hn : 0 < P.n := by omega
  set Q := P.rotate i with hQdef
  have hQ : Q.Simple := simple_rotate P i hP
  have hQn : Q.n = P.n := n_rotate P i
  obtain ⟨ea, ev, eb⟩ := vtx_rotate_fan P i (by omega) hi
  have hQ4 : 4 ≤ Q.n := by omega
  have hdetQ : det (Q.vtx (Q.n - 1)) (Q.vtx 0) (Q.vtx 1) ≠ 0 := by
    grind
  have hnoneQ : ∀ j, j < Q.n →
      Q.vtx j ∈ convexHull ℝ ({Q.vtx (Q.n - 1), Q.vtx 0, Q.vtx 1} : Set Point) →
        j = 0 ∨ j = 1 ∨ j = Q.n - 1 := by
    intro j hj hmem
    rw [ea, ev, eb] at hmem
    rw [hQn] at hj ⊢
    have hQj : Q.vtx j = P.vtx ((i + j) % P.n) := vtx_rotate P i hj
    rw [hQj] at hmem
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hj0, hj1, hjn⟩ := hcon
    refine hnone ((i + j) % P.n) (Nat.mod_lt _ hn) ?_ ?_ ?_ hmem
    · intro h
      unfold prevIdx at h
      rw [show i + P.n - 1 = i + (P.n - 1) by omega] at h
      exact hjn (rot_index_inj hj (by omega) h)
    · intro h
      exact hj0 (rot_index_inj hj hn (by rw [h, Nat.add_zero, Nat.mod_eq_of_lt hi]))
    · intro h
      exact hj1 (rot_index_inj hj (by omega) h)
  have hchord := chord_base_not_mem_boundary hQ hQ4 hdetQ hnoneQ
  rw [ea, eb, boundary_rotate] at hchord
  intro p hp hp1 hp2
  rw [segment_comm] at hp
  exact hchord p hp hp2 hp1

/-- **The ear chord is a diagonal** under the arithmetic test. -/
theorem isDiagonal_of_test :
    IsDiagonal P (prevIdx P i) 2 := by
  refine ⟨le_rfl, h4, ?_⟩
  rw [chord_ear_eq P i hi, prevIdx_mod P hi, prevIdx_add_two_mod P hi]
  exact open_chord_not_mem_boundary_of_test P i hP h4 hi hdet hnone


end

/-- **The ear chord is inside** under the arithmetic test: its open part avoids the boundary
and its midpoint has odd parity. -/
theorem chord_subset_filled_of_test (hP : P.Simple) (hi : i < P.n)
    (hoff : ∀ p ∈ Chazelle.segment (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)),
      p ≠ P.vtx (prevIdx P i) → p ≠ P.vtx ((i + 1) % P.n) → p ∉ P.boundary)
    (hpar : parity P (lerp (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) (1 / 2)) = true) :
    Chazelle.segment (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) ⊆ P.filled := by
  have hab := vtx_prev_ne_vtx_succ P i hP hi
  have hoff' : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      lerp (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) t ∉ P.boundary :=
    fun t ht => hoff _ (lerp_mem_segment _ _ ht.1.le ht.2.le) (lerp_ne_left hab ht.1)
      (lerp_ne_right hab ht.2)
  have hmid : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact segment_subset_filled_of_open hP
    (Jordan.boundary_subset_filled P (vtx_mem_boundary P (prevIdx_lt P hi)))
    (Jordan.boundary_subset_filled P (vtx_mem_boundary P (Nat.mod_lt _ (by omega))))
    hoff' hmid ((mem_filled_iff hP (hoff' _ hmid)).2 hpar)

/-! ### The ear test -/

/-- **The arithmetic ear test.**  For a simple polygon with `n ≥ 4` and `i < n`, with
`a = vtx (prev i)`, `v = vtx i`, `b = vtx (next i)`: vertex `i` is the apex of an ear if and
only if `det a v b ≠ 0`, no vertex of `P` other than `prev i`, `i`, `next i` lies in the closed
triangle `convexHull {a, v, b}`, and the midpoint of `a b` has odd parity. -/
theorem isEar_iff (hP : P.Simple) (h4 : 4 ≤ P.n) (hi : i < P.n) :
    IsEar P i ↔
      det (P.vtx (prevIdx P i)) (P.vtx i) (P.vtx ((i + 1) % P.n)) ≠ 0 ∧
      (∀ j, j < P.n → j ≠ prevIdx P i → j ≠ i → j ≠ (i + 1) % P.n →
        P.vtx j ∉ convexHull ℝ
          ({P.vtx (prevIdx P i), P.vtx i, P.vtx ((i + 1) % P.n)} : Set Point)) ∧
      parity P (lerp (P.vtx (prevIdx P i)) (P.vtx ((i + 1) % P.n)) (1 / 2)) = true := by
  constructor
  · intro he
    exact ⟨det_ear_ne_zero P i hP hi he,
      fun j hj h1 h2 h3 => not_mem_earHull_of_isEar P i hP hi he hj h1 h2 h3,
      parity_mid_of_isEar P i hP hi he⟩
  · rintro ⟨hdet, hnone, hpar⟩
    have hd := isDiagonal_of_test P i hP h4 hi hdet hnone
    exact ⟨hd, chord_subset_filled_of_test P i hP hi
      (open_chord_not_mem_boundary_of_test P i hP h4 hi hdet hnone) hpar⟩

end

end Chazelle.Ears
