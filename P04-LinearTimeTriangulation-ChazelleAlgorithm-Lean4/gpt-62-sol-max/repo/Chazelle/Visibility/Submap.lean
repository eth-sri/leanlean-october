module

public import Chazelle.Visibility.Map
public import Chazelle.Chain.Submap

/-! The interior of a simple polygon is an instance of the chord-system theory.
The polygon-specific ingredient is the walk made of a chord and one boundary arc;
its crossing parity flips across the chord. -/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan

/-! ### The closed walk made of a chord and a boundary arc -/

/-- The closed walk with vertices `P.vtx i, P.vtx (i+1), …, P.vtx (i+m-1)` (indices mod `n`)
followed by the point `e`. -/
def arcPoly (P : Polygon) (i m : ℕ) (e : Point) : Polygon :=
  ⟨(List.range m).map (fun k => P.vtx ((i + k) % P.n)) ++ [e]⟩

@[simp] theorem arcPoly_n (P : Polygon) (i m : ℕ) (e : Point) : (arcPoly P i m e).n = m + 1 := by
  simp [arcPoly, Polygon.n]

theorem arcPoly_vtx_of_lt (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) {k : ℕ} (hk : k < m) :
    (arcPoly P i m e).vtx k = P.vtx ((i + k) % P.n) := by
  simp only [arcPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hk), List.getElem?_map, List.getElem?_range hk]
  rfl

theorem arcPoly_vtx_last (P : Polygon) (i m : ℕ) (e : Point) : (arcPoly P i m e).vtx m = e := by
  simp [arcPoly, Polygon.vtx, List.getD_eq_getElem?_getD]

theorem arcPoly_edge_of_lt (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) {k : ℕ} (hk : k + 1 < m) :
    (arcPoly P i m e).edge k = P.edge ((i + k) % P.n) := by
  ram_finish [Polygon.edge, arcPoly_n, Nat.mod_eq_of_lt, arcPoly_vtx_of_lt, arcPoly_vtx_of_lt P i e hk, Existence.mod_add_one_mod]

theorem arcPoly_edge_pen (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) (hm : 0 < m) :
    (arcPoly P i m e).edge (m - 1) = Chazelle.segment (P.vtx ((i + (m - 1)) % P.n)) e := by
  ram_finish [Polygon.edge, arcPoly_n, show m - 1 + 1 = m by omega, Nat.mod_eq_of_lt, arcPoly_vtx_of_lt, arcPoly_vtx_last]

theorem arcPoly_edge_last (P : Polygon) (i : ℕ) {m : ℕ} (e : Point) (hm : 0 < m) :
    (arcPoly P i m e).edge m = Chazelle.segment e (P.vtx (i % P.n)) := by
  unfold Polygon.edge
  rw [arcPoly_n, Nat.mod_self, arcPoly_vtx_of_lt P i e hm, arcPoly_vtx_last, Nat.add_zero]

/-- Every edge of the walk other than the last lies in the boundary of `P`, provided the
penultimate edge does. -/
theorem arcPoly_edge_subset_boundary (P : Polygon) (hn : 0 < P.n) (i : ℕ) {m : ℕ} (e : Point)
    (hm : 0 < m) (hpen : Chazelle.segment (P.vtx ((i + (m - 1)) % P.n)) e ⊆ P.boundary) {k : ℕ}
    (hk : k < m) : (arcPoly P i m e).edge k ⊆ P.boundary := by
  rcases Nat.lt_or_ge (k + 1) m with h | h
  · rw [arcPoly_edge_of_lt P i e h]
    exact Existence.edge_subset_boundary P (Nat.mod_lt _ hn)
  · have : k = m - 1 := by omega
    subst this
    rwa [arcPoly_edge_pen P i e hm]

/-- The boundary of the walk lies in the boundary of `P` together with the closing segment. -/
theorem arcPoly_boundary_subset (P : Polygon) (hn : 0 < P.n) (i : ℕ) {m : ℕ} (e : Point)
    (hm : 0 < m) (hpen : Chazelle.segment (P.vtx ((i + (m - 1)) % P.n)) e ⊆ P.boundary) :
    (arcPoly P i m e).boundary ⊆ P.boundary ∪ Chazelle.segment e (P.vtx (i % P.n)) := by
  rintro p ⟨k, hk, hp⟩
  rw [arcPoly_n] at hk
  rcases Nat.lt_or_ge k m with h | h
  · exact Or.inl (arcPoly_edge_subset_boundary P hn i e hm hpen h hp)
  · have : k = m := by omega
    subst this
    rw [arcPoly_edge_last P i e hm] at hp
    exact Or.inr hp

/-! ### Chord separation -/

/-- **The parity flip across a chord.**  For an interior point `z` of the chord of vertex `i`
in direction `σ`, there is a closed walk `Γ` whose boundary lies in `P.boundary ∪ chord`, such
that the points `z ± (0, ε)` (small `ε > 0`) are off the boundary of `Γ` and have different
crossing parities with respect to `Γ`. -/
theorem exists_walk_parity_flip {P : Polygon} (hP : P.Simple) {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) {z : Point} (hz : z ∈ chordSet P i σ)
    (hzb : z ∉ P.boundary) :
    ∃ Γ : Polygon, Γ.boundary ⊆ P.boundary ∪ chordSet P i σ ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        (z.1, z.2 + ε) ∉ Γ.boundary ∧ (z.1, z.2 - ε) ∉ Γ.boundary ∧
          parity Γ (z.1, z.2 + ε) ≠ parity Γ (z.1, z.2 - ε) := by
  have hn : 0 < P.n := by have := simple_three_le hP; omega
  obtain ⟨j, hj, hej⟩ := chordEnd_mem_boundary hP hi h
  set e := chordEnd P i σ with he
  set m := (j + P.n - i) % P.n + 1 with hm
  have hm0 : 0 < m := by omega
  have hidx : (i + (m - 1)) % P.n = j := by
    rw [hm, Nat.add_sub_cancel, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show i + (j + P.n - i) = j + P.n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have hpen : Chazelle.segment (P.vtx ((i + (m - 1)) % P.n)) e ⊆ P.boundary := by
    rw [hidx]
    refine Subset.trans ?_ (Existence.edge_subset_boundary P hj)
    exact Geometry.segment_subset_of_convex (Geometry.segment_convex _ _)
      (Geometry.left_mem_segment _ _) hej
  have hii := Nat.mod_eq_of_lt hi
  refine ⟨arcPoly P i m e, ?_, ?_⟩
  · refine (arcPoly_boundary_subset P hn i e hm0 hpen).trans ?_
    rw [hii, Geometry.segment_comm]
    exact le_rfl
  · have hzΓ : z ∈ (arcPoly P i m e).edge m := by
      rwa [arcPoly_edge_last P i e hm0, hii, Geometry.segment_comm]
    have hmn : m < (arcPoly P i m e).n := by rw [arcPoly_n]; omega
    have hsucc : (m + 1) % (arcPoly P i m e).n = 0 := by simp
    have hv0 : (arcPoly P i m e).vtx 0 = P.vtx i := by
      rw [arcPoly_vtx_of_lt P i e hm0, Nat.add_zero, hii]
    have hne : ((arcPoly P i m e).vtx m).1 ≠ ((arcPoly P i m e).vtx ((m + 1) % (arcPoly P i m e).n)).1 := by
      rw [hsucc, hv0, arcPoly_vtx_last, he, chordEnd_fst]
      intro heq
      have hσ0 := h.ne_zero hi
      have hpos := chordParam_pos hP hi h
      have : σ * chordParam P i σ = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact hσ0 h'
      · exact hpos.ne' h'
    have hzu : z ≠ (arcPoly P i m e).vtx m := by
      rw [arcPoly_vtx_last]
      rintro rfl
      exact hzb (chordEnd_mem_boundary hP hi h)
    have hzv : z ≠ (arcPoly P i m e).vtx ((m + 1) % (arcPoly P i m e).n) := by
      rw [hsucc, hv0]
      rintro rfl
      exact hzb (Existence.vtx_mem_boundary P hi)
    have hother : ∀ k, k < (arcPoly P i m e).n → k ≠ m → z ∉ (arcPoly P i m e).edge k := by
      intro k hk hkm hzk
      rw [arcPoly_n] at hk
      exact hzb (arcPoly_edge_subset_boundary P hn i e hm0 hpen (by omega) hzk)
    exact parity_flip (arcPoly P i m e) hmn hzΓ hne hzu hzv hother

/-- The interior and the vertex chords of a simple polygon form a chord system. -/
theorem chordSystem {P : Polygon} (hP : P.Simple) :
    Chain.ChordSystem (P.filled \ P.boundary) (chords P) where
  isOpen := isOpen_filled_sdiff_boundary hP
  finite := chords_finite P
  hchord := by
    rintro c ⟨i, σ, hi, hσ, h, rfl⟩
    exact ⟨_, _, _, (isHChord_chord hP hi hσ h).toIn, chordSet_eq_hseg P i σ⟩
  walk := by
    rintro c ⟨i, σ, hi, hσ, h, rfl⟩ z hz hzD
    obtain ⟨Γ, hΓ, hflip⟩ := exists_walk_parity_flip hP hi h hz hzD.2
    exact ⟨Γ, hΓ.trans (union_subset_union (fun _ hp hD => hD.2 hp) Subset.rfl), hflip⟩

private theorem region_count {P : Polygon} (hP : P.Simple) :
    (regions P).Finite ∧ (regions P).ncard = (chords P).ncard + 1 :=
  (chordSystem hP).regionsIn_finite_ncard (filled_sdiff_boundary_connected hP)
    (filled_sdiff_boundary_nonempty hP) Subset.rfl

/-- The full horizontal visibility map has one more region than chord. -/
theorem regions_ncard {P : Polygon} (hP : P.Simple) :
    (regions P).ncard = (chords P).ncard + 1 := (region_count hP).2

theorem regions_ncard_le {P : Polygon} (hP : P.Simple) : (regions P).ncard ≤ 2 * P.n + 1 := by
  rw [regions_ncard hP]
  exact Nat.add_le_add_right (chords_ncard_le P) 1

theorem regions_finite {P : Polygon} (hP : P.Simple) : (regions P).Finite := (region_count hP).1

end

end Chazelle.Visibility
