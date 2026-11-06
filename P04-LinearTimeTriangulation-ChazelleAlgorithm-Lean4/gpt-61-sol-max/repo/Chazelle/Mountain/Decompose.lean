module

public import Chazelle.Mountain.TrapDiagonal
public import Chazelle.Visibility.Submap

/-!
# The diagonals inserted from the trapezoidal decomposition

For a simple polygon `P`, every region of the horizontal visibility map is an open trapezoid
described by some data `D : TrapData P` (`regions_eq_trapSet`); `D.top`, `D.bot` are its top
and bottom vertices (`Chazelle.Mountain.TrapDiagonal`), and `D.diag = (D.top, D.bot)`.

* `trapDiagonals P`: the pairs `(D.top, D.bot)` over all trapezoids whose top and bottom
  vertices are not adjacent in `P`.  They are interior diagonals (`trapDiagonals_isDiagonal`),
  there are at most `2 n + 1` of them (`trapDiagonals_ncard_le`), and two distinct ones meet at
  most in common endpoints (`trapDiagonals_inter`): each open diagonal lies in its own region
  (`TrapData.openDiagSeg_subset_region`) and regions are pairwise disjoint.
* `vtxChords P`: the pairs `(k, m)` such that the chord of vertex `k` (in some locally interior
  horizontal direction) ends at vertex `m`.  They are interior diagonals as well
  (`vtxChords_isDiagonal`), at most `2 n` of them (`vtxChords_ncard_le`), and they meet the
  trapezoid diagonals and each other only in common endpoints (`vtxChords_inter_trapDiagonals`,
  `vtxChords_inter`).
* `allDiagonals P = trapDiagonals P ∪ vtxChords P`, with the combined statements.
* `TrapData.vtx_mem_closure_region`: every vertex of `P` in the closure of a region lies on
  the closed top or bottom side of the trapezoid.

See the final section of this file for the precise statement of the mountain decomposition
theorem that remains to be proved, the proof plan, and the reason why the vertex-to-vertex
chords must be inserted together with the top–bottom diagonals.
-/

namespace Chazelle.Mountain

@[expose] public section

open Set
open Chazelle.Jordan
open Chazelle.Visibility
open Chazelle.Existence (IsDiagonal vtx_mem_boundary)
open Chazelle.Geometry (lerp lerp_mem_segment)

/-! ### Segments named by index pairs -/

/-- The closed segment named by a pair of vertex indices. -/
def diagSeg (P : Polygon) (d : ℕ × ℕ) : Set Point := Chazelle.segment (P.vtx d.1) (P.vtx d.2)

/-! ### Trapezoid data of a region -/

/-- The data of a region of the visibility map: a free point `q` and its trapezoid data. -/
structure TrapData (P : Polygon) where
  /-- A free point of the region. -/
  q : Point
  /-- The left side edge. -/
  i : ℕ
  /-- The right side edge. -/
  j : ℕ
  /-- The bottom height. -/
  y₁ : ℝ
  /-- The top height. -/
  y₂ : ℝ
  free : q ∈ freeRegion P
  isTrap : IsTrap P q i j y₁ y₂

namespace TrapData

variable {P : Polygon}

section
variable (D : TrapData P)
include D
/-- The region (open trapezoid) described by the data. -/
def region : Set Point := trapSet P D.i D.j D.y₁ D.y₂

/-- The top vertex of the trapezoid (leftmost vertex of the closed top side). -/
noncomputable def top : ℕ := topVtx P D.i D.j D.y₂

/-- The bottom vertex of the trapezoid (rightmost vertex of the closed bottom side). -/
noncomputable def bot : ℕ := botVtx P D.i D.j D.y₁

/-- The index pair of the diagonal of the trapezoid. -/
noncomputable def diag : ℕ × ℕ := (D.top, D.bot)

/-- The top and bottom vertices are not adjacent in `P`. -/
def NonAdj : Prop := D.bot ≠ (D.top + 1) % P.n ∧ D.top ≠ (D.bot + 1) % P.n


end

section
variable (hP : P.Simple) (D : TrapData P)
include hP
theorem region_mem_regions : D.region ∈ regions P :=
  ⟨D.q, D.free, (D.isTrap.region_eq hP D.free).symm⟩

theorem region_subset_freeRegion : D.region ⊆ freeRegion P :=
  D.isTrap.trapSet_subset_freeRegion hP D.free

theorem region_subset_interior :
    D.region ⊆ P.filled \ P.boundary :=
  D.isTrap.trapSet_subset_interior hP D.free

theorem top_lt : D.top < P.n := D.isTrap.topVtx_lt hP D.free

theorem bot_lt : D.bot < P.n := D.isTrap.botVtx_lt hP D.free

theorem top_ne_bot : D.top ≠ D.bot :=
  D.isTrap.topVtx_ne_botVtx hP D.free

theorem top_snd : (P.vtx D.top).2 = D.y₂ :=
  D.isTrap.topVtx_snd hP D.free

theorem bot_snd : (P.vtx D.bot).2 = D.y₁ :=
  D.isTrap.botVtx_snd hP D.free

theorem bot_snd_lt_top_snd :
    (P.vtx D.bot).2 < (P.vtx D.top).2 :=
  D.isTrap.botVtx_snd_lt hP D.free

/-- No vertex lies in a region. -/
theorem not_mem_region_of_vtx {k : ℕ} (hk : k < P.n) :
    P.vtx k ∉ D.region :=
  fun h => (D.region_subset_interior hP h).2 (vtx_mem_boundary P hk)


end

/-- **The diagonal depends only on the region.** -/
theorem diag_eq_of_region_eq (hP : P.Simple) (D D' : TrapData P) (h : D.region = D'.region) :
    D.diag = D'.diag := by
  obtain ⟨h1, h2⟩ := D.isTrap.topVtx_eq_of_trapSet_eq hP D.free D'.free D'.isTrap h
  aesop

section
variable (hP : P.Simple) (D : TrapData P) (hD : D.NonAdj)
include hP hD
/-- A point of the closed diagonal (non-adjacent case) is an endpoint or lies in the region. -/
theorem segment_cases {p : Point}
    (hp : p ∈ diagSeg P D.diag) : p = P.vtx D.top ∨ p = P.vtx D.bot ∨ p ∈ D.region :=
  D.isTrap.diag_segment_cases hP D.free hD.1 hD.2 hp

/-- **The diagonal is an interior diagonal** (non-adjacent case). -/
theorem exists_isDiagonal :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = D.top ∧ (s + L) % P.n = D.bot ∧
      diagSeg P D.diag ⊆ P.filled :=
  D.isTrap.exists_isDiagonal hP D.free hD.1 hD.2

theorem eq_endpoint_of_mem_diagSeg {p : Point}
    (hp : p ∈ diagSeg P D.diag) (hnot : p ∉ D.region) : p = P.vtx D.top ∨ p = P.vtx D.bot := by
  rcases D.segment_cases hP hD hp with e | e | e
  all_goals simp_all


end

/-- **Every vertex of `P` in the closure of a region lies on the closed top or bottom side of
the trapezoid.** -/
theorem vtx_mem_closure_region (D : TrapData P) {k : ℕ} (hk : k < P.n)
    (h : P.vtx k ∈ closure D.region) :
    k ∈ sideVtxSet P D.i D.j D.y₁ ∨ k ∈ sideVtxSet P D.i D.j D.y₂ :=
  D.isTrap.vtx_mem_closure_trapSet hk h

end TrapData

/-- Every region of the visibility map has trapezoid data. -/
theorem exists_trapData {P : Polygon} (hP : P.Simple) {C : Set Point} (hC : C ∈ regions P) :
    ∃ D : TrapData P, D.region = C := by
  obtain ⟨q, i, j, y₁, y₂, hq, hT, rfl⟩ := regions_eq_trapSet hP hC
  exact ⟨⟨q, i, j, y₁, y₂, hq, hT⟩, rfl⟩

/-! ### The trapezoid diagonals -/

/-- **The trapezoid diagonals**: the pairs `(top, bot)` of the trapezoids whose top and bottom
vertices are not adjacent in `P`. -/
def trapDiagonals (P : Polygon) : Set (ℕ × ℕ) := {d | ∃ D : TrapData P, D.NonAdj ∧ d = D.diag}

theorem TrapData.diag_mem_trapDiagonals {P : Polygon} (D : TrapData P) (hD : D.NonAdj) :
    D.diag ∈ trapDiagonals P :=
  ⟨D, hD, rfl⟩

section
variable {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ trapDiagonals P)
include hP hd
/-- Elementary properties of a trapezoid diagonal: indices in range, distinct, the first
strictly above the second, not adjacent. -/
theorem trapDiagonals_spec :
    d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2 ∧ (P.vtx d.2).2 < (P.vtx d.1).2 ∧
      d.2 ≠ (d.1 + 1) % P.n ∧ d.1 ≠ (d.2 + 1) % P.n := by
  obtain ⟨D, hD, rfl⟩ := hd
  exact ⟨D.top_lt hP, D.bot_lt hP, D.top_ne_bot hP, D.bot_snd_lt_top_snd hP, hD.1, hD.2⟩

/-- **Each trapezoid diagonal is an interior diagonal.** -/
theorem trapDiagonals_isDiagonal :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = d.1 ∧ (s + L) % P.n = d.2 ∧ diagSeg P d ⊆ P.filled := by
  obtain ⟨D, hD, rfl⟩ := hd
  exact D.exists_isDiagonal hP hD


end

theorem trapDiagonals_finite {P : Polygon} (hP : P.Simple) : (trapDiagonals P).Finite :=
  ((Set.finite_lt_nat P.n).prod (Set.finite_lt_nat P.n)).subset fun _ hd =>
    ⟨(trapDiagonals_spec hP hd).1, (trapDiagonals_spec hP hd).2.1⟩

open Classical in
/-- The region of a trapezoid diagonal (any trapezoid data producing it; well defined by
`TrapData.diag_eq_of_region_eq`), or `∅`. -/
noncomputable def regionOfDiag (P : Polygon) (d : ℕ × ℕ) : Set Point :=
  if h : ∃ D : TrapData P, D.NonAdj ∧ d = D.diag then (Classical.choose h).region else ∅

theorem regionOfDiag_spec {P : Polygon} {d : ℕ × ℕ} (hd : d ∈ trapDiagonals P) :
    ∃ D : TrapData P, D.NonAdj ∧ d = D.diag ∧ regionOfDiag P d = D.region := by
  have h : ∃ D : TrapData P, D.NonAdj ∧ d = D.diag := hd
  grind [regionOfDiag]

/-- **Distinct trapezoid diagonals meet at most in common endpoints.** -/
theorem trapDiagonals_inter {P : Polygon} (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ trapDiagonals P) (hd' : d' ∈ trapDiagonals P) (hne : d ≠ d') :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  obtain ⟨D, hD, rfl⟩ := hd
  obtain ⟨D', hD', rfl⟩ := hd'
  have hreg : D.region ≠ D'.region := fun h => hne (TrapData.diag_eq_of_region_eq hP D D' h)
  have hdisj : Disjoint D.region D'.region :=
    (regions_eq_or_disjoint (D.region_mem_regions hP) (D'.region_mem_regions hP)).resolve_left
      hreg
  rintro p ⟨hp, hp'⟩
  have h1 : p ∉ D.region := by
    intro hpD
    rcases D'.segment_cases hP hD' hp' with e | e | e
    · exact D.not_mem_region_of_vtx hP (D'.top_lt hP) (by simp_all)
    · exact D.not_mem_region_of_vtx hP (D'.bot_lt hP) (by simp_all)
    grind
  have h1' : p ∉ D'.region := by
    intro hpD
    rcases D.segment_cases hP hD hp with e | e | e
    · exact D'.not_mem_region_of_vtx hP (D.top_lt hP) (by simp_all)
    · exact D'.not_mem_region_of_vtx hP (D.bot_lt hP) (by simp_all)
    simp_all
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  exact ⟨D.eq_endpoint_of_mem_diagSeg hP hD hp h1, D'.eq_endpoint_of_mem_diagSeg hP hD' hp' h1'⟩

/-! ### Vertex-to-vertex chords -/

/-- **The vertex-to-vertex chords**: `(k, m)` such that the chord of vertex `k` in some locally
interior horizontal direction ends at vertex `m`. -/
def vtxChords (P : Polygon) : Set (ℕ × ℕ) :=
  {d | d.1 < P.n ∧ d.2 < P.n ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ DirInterior P d.1 σ ∧ chordEnd P d.1 σ = P.vtx d.2}

section
variable {P : Polygon} {d : ℕ × ℕ} (hd : d ∈ vtxChords P)
include hd
theorem vtxChords_spec :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ DirInterior P d.1 σ ∧ chordEnd P d.1 σ = P.vtx d.2 ∧
      diagSeg P d = chordSet P d.1 σ := by
  obtain ⟨-, -, σ, hσ, hdir, hend⟩ := hd
  aesop (add simp [diagSeg, chordSet]) (add safe (by omega))

/-- A vertex-to-vertex chord is a chord of the visibility map. -/
theorem vtxChords_diagSeg_mem_chords :
    diagSeg P d ∈ chords P := by
  obtain ⟨σ, hσ, hdir, -, hseg⟩ := vtxChords_spec hd
  exact ⟨d.1, σ, hd.1, hσ, hdir, hseg⟩

/-- The two endpoints of a vertex-to-vertex chord are at the same height. -/
theorem vtxChords_snd_eq :
    (P.vtx d.1).2 = (P.vtx d.2).2 := by
  obtain ⟨σ, -, -, hend, -⟩ := vtxChords_spec hd
  rw [← hend]
  rfl


end

section
variable {P : Polygon} (hP : P.Simple) {d : ℕ × ℕ} (hd : d ∈ vtxChords P)
include P hP hd
theorem vtxChords_ne :
    d.1 ≠ d.2 := by
  obtain ⟨σ, -, hdir, hend, -⟩ := vtxChords_spec hd
  intro h
  apply chordEnd_ne_vtx hP hd.1 hdir
  rw [hend, h]

/-- The endpoints of a vertex-to-vertex chord are not adjacent (the chord's open part is
interior, so it is not an edge). -/
theorem vtxChords_not_adjacent :
    d.2 ≠ (d.1 + 1) % P.n ∧ d.1 ≠ (d.2 + 1) % P.n := by
  obtain ⟨σ, hσ, hdir, hend, hseg⟩ := vtxChords_spec hd
  have hk := hd.1
  have hm := hd.2.1
  have hpos := chordParam_pos hP hk hdir
  have hzo : rayPt (P.vtx d.1) σ (chordParam P d.1 σ / 2) ∈ openChordSet P d.1 σ :=
    ⟨chordParam P d.1 σ / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hzi := openChordSet_subset_interior hP hk hdir hzo
  have hzs : rayPt (P.vtx d.1) σ (chordParam P d.1 σ / 2) ∈ diagSeg P d := by
    rw [hseg, chordSet_eq_openChordSet_union hP hk hdir]
    simp_all
  constructor
  · intro h
    apply hzi.2
    exact ⟨d.1, hk, by unfold Polygon.edge; rw [← h]; exact hzs⟩
  · intro h
    apply hzi.2
    exact ⟨d.2, hm, by unfold Polygon.edge; rw [← h, segment_comm]; exact hzs⟩

/-- **Each vertex-to-vertex chord is an interior diagonal.** -/
theorem vtxChords_isDiagonal :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = d.1 ∧ (s + L) % P.n = d.2 ∧ diagSeg P d ⊆ P.filled := by
  obtain ⟨σ, hσ, hdir, hend, hseg⟩ := vtxChords_spec hd
  have hk := hd.1
  have hm := hd.2.1
  have hne := vtxChords_ne hP hd
  obtain ⟨h1, h2⟩ := vtxChords_not_adjacent hP hd
  obtain ⟨L, hL2, hLn, hsL⟩ := exists_diag_index (simple_three_le hP) hk hm hne h1 h2
  have hs : d.1 % P.n = d.1 := Nat.mod_eq_of_lt hk
  refine ⟨d.1, L, ⟨hL2, hLn, ?_⟩, hs, hsL, ?_⟩
  · rw [hs, hsL]
    intro p hp hp1 hp2
    have hp' : p ∈ chordSet P d.1 σ := by rw [← hseg]; exact hp
    rcases mem_chordSet_cases hP hk hdir hp' with e | e | e
    all_goals simp_all
  · rw [hseg]
    exact chordSet_subset_filled hP hk hdir


end

/-- The index of a vertex point (`Classical.epsilon`; meaningful for vertices of a simple
polygon, see `vtxIndex_vtx`). -/
noncomputable def vtxIndex (P : Polygon) (p : Point) : ℕ :=
  Classical.epsilon fun m => m < P.n ∧ P.vtx m = p

section
variable {P : Polygon} (hP : P.Simple)
include hP
theorem vtxIndex_vtx {m : ℕ} (hm : m < P.n) :
    vtxIndex P (P.vtx m) = m := by
  have h := Classical.epsilon_spec (p := fun m' => m' < P.n ∧ P.vtx m' = P.vtx m) ⟨m, hm, rfl⟩
  exact simple_vtx_inj hP h.1 hm h.2

theorem vtxChords_subset_image :
    vtxChords P ⊆ (fun x : ℕ × ℝ => (x.1, vtxIndex P (chordEnd P x.1 x.2))) ''
      ((↑(Finset.range P.n) : Set ℕ) ×ˢ ({1, -1} : Set ℝ)) := by
  rintro ⟨k, m⟩ ⟨hk, hm, σ, hσ, -, hend⟩
  refine ⟨(k, σ), ⟨by simp_all, ?_⟩, ?_⟩
  · simp_all
  · show (k, vtxIndex P (chordEnd P k σ)) = (k, m)
    rw [hend, vtxIndex_vtx hP hm]

theorem vtxChords_finite : (vtxChords P).Finite :=
  ((Finset.range P.n).finite_toSet.prod ((finite_singleton (-1 : ℝ)).insert 1)).image _
    |>.subset (vtxChords_subset_image hP)

section
variable {d d' : ℕ × ℕ}
include d d'
/-- **A vertex-to-vertex chord meets a trapezoid diagonal at most in common endpoints.** -/
theorem vtxChords_inter_trapDiagonals
    (hd : d ∈ trapDiagonals P) (hd' : d' ∈ vtxChords P) :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  obtain ⟨D, hD, rfl⟩ := hd
  obtain ⟨σ, hσ, hdir, hend, hseg⟩ := vtxChords_spec hd'
  rintro p ⟨hp, hp'⟩
  have hpc : p ∈ chordUnion P :=
    ⟨chordSet P d'.1 σ, ⟨d'.1, σ, hd'.1, hσ, hdir, rfl⟩, by simp_all⟩
  have h1 : p ∉ D.region := fun h => (D.region_subset_freeRegion hP h).2 hpc
  have hend1 := D.eq_endpoint_of_mem_diagSeg hP hD hp h1
  have hpb : p ∈ P.boundary := by
    rcases hend1 with rfl | rfl
    · exact vtx_mem_boundary P (D.top_lt hP)
    · exact vtx_mem_boundary P (D.bot_lt hP)
  have hmem : p ∈ ({P.vtx d'.1, chordEnd P d'.1 σ} : Set Point) := by
    rw [← chordSet_inter_boundary hP hd'.1 hdir]
    simp_all
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hmem ⊢
  refine ⟨hend1, ?_⟩
  simp_all

/-- **Two vertex-to-vertex chords with distinct segments meet at most in common endpoints.**
(The pairs `(k, m)` and `(m, k)` name the same chord when both directions are recorded.) -/
theorem vtxChords_inter (hd : d ∈ vtxChords P)
    (hd' : d' ∈ vtxChords P) (hne : diagSeg P d ≠ diagSeg P d') :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  obtain ⟨σ, hσ, hdir, hend, hseg⟩ := vtxChords_spec hd
  obtain ⟨σ', hσ', hdir', hend', hseg'⟩ := vtxChords_spec hd'
  rw [hseg, hseg'] at hne ⊢
  intro p hp
  have := chord_inter hP hd.1 hd'.1 hσ hσ' hdir hdir' hne hp
  simp_all

/-! ### All inserted diagonals -/



end

end

/-- **All inserted diagonals**: the trapezoid diagonals together with the vertex-to-vertex
chords. -/
def allDiagonals (P : Polygon) : Set (ℕ × ℕ) := trapDiagonals P ∪ vtxChords P

section
variable {P : Polygon} (hP : P.Simple)
include hP
theorem allDiagonals_finite : (allDiagonals P).Finite :=
  (trapDiagonals_finite hP).union (vtxChords_finite hP)

section
variable {d : ℕ × ℕ} (hd : d ∈ allDiagonals P)
include d hd
/-- **Every inserted diagonal is an interior diagonal.** -/
theorem allDiagonals_isDiagonal :
    ∃ s L, IsDiagonal P s L ∧ s % P.n = d.1 ∧ (s + L) % P.n = d.2 ∧ diagSeg P d ⊆ P.filled := by
  rcases hd with hd | hd
  · exact trapDiagonals_isDiagonal hP hd
  · exact vtxChords_isDiagonal hP hd

/-- Indices of an inserted diagonal are in range and distinct. -/
theorem allDiagonals_lt :
    d.1 < P.n ∧ d.2 < P.n ∧ d.1 ≠ d.2 := by
  rcases hd with hd | hd
  · exact ⟨(trapDiagonals_spec hP hd).1, (trapDiagonals_spec hP hd).2.1,
      (trapDiagonals_spec hP hd).2.2.1⟩
  · exact ⟨hd.1, hd.2.1, vtxChords_ne hP hd⟩


end

/-- **Two inserted diagonals with distinct segments meet at most in common endpoints.** -/
theorem allDiagonals_inter {d d' : ℕ × ℕ} (hd : d ∈ allDiagonals P)
    (hd' : d' ∈ allDiagonals P) (hne : diagSeg P d ≠ diagSeg P d') :
    diagSeg P d ∩ diagSeg P d' ⊆
      ({P.vtx d.1, P.vtx d.2} : Set Point) ∩ {P.vtx d'.1, P.vtx d'.2} := by
  rcases hd with hd | hd <;> rcases hd' with hd' | hd'
  · exact trapDiagonals_inter hP hd hd' (fun h => hne (by rw [h]))
  · exact vtxChords_inter_trapDiagonals hP hd hd'
  · intro p hp
    have := vtxChords_inter_trapDiagonals hP hd' hd ⟨hp.2, hp.1⟩
    simp_all
  · exact vtxChords_inter hP hd hd' hne

/-! ### The mountain decomposition theorem: statement and plan

**What remains (not proved here).**  Let `P` be simple and let `Δ = allDiagonals P`.  Call a
list `l : List ℕ` of pairwise distinct indices `< n` a *piece* of the subdivision when
`3 ≤ l.length`, every edge of `subPoly P l` (see `Chazelle.EarClip.SubPoly`) is either an edge
of `P` (`l[k+1] = (l[k] + 1) % n`) or an inserted diagonal (`(l[k], l[k+1]) ∈ Δ` or
`(l[k+1], l[k]) ∈ Δ`, cyclically), and the interior of `(subPoly P l).filled` contains no
point of `P.boundary ∪ ⋃ d ∈ Δ, diagSeg P d` (so that the piece is a face of the subdivision).
The claim is:

  `∀ l, IsPiece P l → ∃ a < l.length, IsMountain (subPoly P l) a`

where `IsMountain Q a` means: the edge `a` of `Q` is the *base*, i.e. writing
`v₀ = Q.vtx ((a+1) % m), v₁, …, v_{m-1} = Q.vtx a` for the remaining vertices in cyclic order,
the sequence `v₀, …, v_{m-1}` is strictly `ylexLT`-monotone (increasing or decreasing); in
particular `Q` is a monotone polygon (with respect to the `ylexLT`-perturbed height) one of
whose two chains is the single edge `a`.  Together with `allDiagonals_isDiagonal` and
`allDiagonals_inter`, and `filled_eq_union_arcs` / `weakTriangulates_of_diagonal` applied along
each diagonal, this reduces the triangulation of `P` to the triangulation of mountains.

**Why the vertex-to-vertex chords are needed.**  With the exact (unperturbed) horizontal
chords of `Chazelle.Visibility`, the top–bottom diagonals alone do *not* decompose `P` into
mountains.  Example: `P = [(0,0), (1,1), (2,0), (3,0), (3,-2), (0,-2)]`.  Its only chord is
the segment from `(0,0)` to `(2,0)` (emitted by both endpoints); the two regions are the
triangle above it and the rectangle `(0,3) × (-2,0)` below.  For the rectangle, the closed top
side carries the vertices `(0,0), (2,0), (3,0)`, so `top = 0` (leftmost), the bottom side
carries `(0,-2), (3,-2)`, so `bot = 4` (rightmost); the diagonal `(0,4)` is inserted.  For the
triangle, `top = 1` and `bot = 2` (rightmost of `(0,0), (2,0)`) are adjacent: no diagonal.
Cutting along `(0,4)` alone leaves the piece `[0,1,2,3,4]`, i.e. `(0,0),(1,1),(2,0),(3,0),(3,-2)`,
whose two chains from the `ylexLT`-minimum `(3,-2)` to the maximum `(1,1)` are
`(3,-2),(0,0),(1,1)` and `(3,-2),(3,0),(2,0),(1,1)`: neither is a single edge, so the piece is
not a mountain (for any tie-break).  Inserting also the vertex-to-vertex chord `(0,2)` gives
the pieces `[0,1,2]`, `[0,2,3,4]` and `[4,5,0]`, all mountains with bases `(2,0)`, `(4,3)`
and `(0,4)`.  In general the `ylexLT`-perturbed trapezoidation (heights `y + ε x`) slices each
unperturbed trapezoid into a middle slab, whose top and bottom vertices are exactly
`topVtx` (leftmost on top) and `botVtx` (rightmost at the bottom), and thin slabs between
consecutive vertices of the closed top (resp. bottom) side, whose diagonals are exactly the
segments between consecutive side vertices, i.e. edges of `P` or vertex-to-vertex chords.  So
`allDiagonals P` is the diagonal set of the perturbed trapezoidation, for which the classical
argument applies.

**Proof plan for the claim.**  The boundary of a piece alternates between maximal chains of
`P`-edges and inserted diagonals.  (1) A maximal chain of `P`-edges `v_a, …, v_b` inside a piece
is `ylexLT`-monotone: if some interior vertex `v` of the chain were a `ylexLT`-local extremum,
say a local minimum, then near `v` the piece lies above `v`; the region of the visibility map
touching `v` from above has `v` on its closed bottom side, and either `v` is its bottom vertex
(so a diagonal is attached at `v` unless it is adjacent to the top vertex, in which case that
edge is a side edge and the trapezoid is a triangle with base at `v`, a mountain apex), or the
segment from `v` to the next side vertex is a vertex-to-vertex chord in `allDiagonals P`, also
attached at `v`; both contradict `v` being interior to a maximal `P`-chain.  (2) Each inserted
diagonal joins a top vertex to a bottom vertex of the same trapezoid (or two vertices at the
same height), so the chains meeting at a diagonal endpoint continue monotonically across it, and
a piece has exactly one `ylexLT`-maximum and one minimum; the base is the diagonal (or edge)
joining them when one of the two chains consists of that single segment, which is forced by
the trapezoid geometry: the chain opposite to the base lies on the side edges `i`, `j` of one
trapezoid and its top/bottom sides.  Auxiliary facts available here:
`TrapData.vtx_mem_closure_region` (every vertex on the closure of a region is on its closed top
or bottom side), `IsTrap.top_side` / `IsTrap.bot_side` (the open sides are boundary or chord
points), `TrapData.top_eq_side_of_adjacent`, `TrapData.bot_eq_side_of_adjacent`.
-/


end

end

end Chazelle.Mountain
