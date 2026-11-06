module

public import Chazelle.Merge.Augmented

/-!
# The fusion of two submaps (Chazelle §3.1, Lemma 3.1), Euclidean part

Let `J` be a junction of two adjacent chains `C₁ = J.left`, `C₂ = J.right` with union
`C = J.whole` (`Chazelle.Merge.Union`), and let `S₁ ⊆ augChords C₁`, `S₂ ⊆ augChords C₂` be
(augmented) submaps of `V(C₁)`, `V(C₂)` (`Chazelle.Merge.Augmented`).  Chazelle defines
(p. 501) the **fusion** `S` of `S₁` and `S₂` as the submap of `V(C)` whose chords are those
"seen by the endpoints of the exit chords of `S_i` (i = 1, 2) and by the companion vertices
resulting from the duplication of `C₁ ∩ C₂`"; its chords "need not be incident upon any vertex of
`∂C`, hence the notion of augmented maps and submaps" (Remark 1, p. 507).

## The fusion

The chord of `C` seen from an endpoint `p` of a chord `c` along `c` is `shoot C p σ`.  The fusion
is (`Junction.fusion`)

  `{shoot C (lend c) 1, shoot C (rend c) (-1) | c ∈ S₁ ∪ S₂, direction free for C}
     ∪ {chords of C at the shared vertex}`   (`Junction.sharedChords`).

Declaratively (`mem_fusion_iff`): the chords of the fusion are the chords of `C` contained in a
chord `c` of `S₁ ∪ S₂` and sharing an endpoint with it, plus the shared-vertex chords.

## Main results

* `fusion_subset_augChords`: the fusion is an augmented submap of `V(C)` (so fusions can be
  iterated, as in the recursion of §4); `ncard_fusion_le`: `|fusion| ≤ 2 (|S₁| + |S₂|) + 2`;
  `ncard_regions_fusion`: `#regions = |fusion| + 1 ≤ 2 (|S₁| + |S₂|) + 3` and the dual graph is
  a tree — the size bound `O(n₁/γ₁ + n₂/γ₂ + 1)` of Lemma 3.1 once Lemma 2.3 bounds `|S_i|`.
* **Endpoints are preserved** (`end_mem_fusion`, p. 508: "any exit chord endpoint of `S_i` is
  still an endpoint of a chord in `S`"): every endpoint of a chord `c` of `S₁ ∪ S₂` other than
  the shared vertex is an endpoint of a chord of the fusion contained in `c`.
* **Chords between two points of one side are old chords** (`fusion_mem_left`,
  `fusion_mem_right`): a chord of the fusion whose two endpoints lie on `C₁` (and differ from the
  shared vertex) is a chord of `S₁` — the claim "with the possible exception of the chords
  incident upon `a₀` or `a_{m+1}`, every chord of `S` that connects two points of `∂C_i` is also
  a chord of `S_i`" of p. 508, stated without proof in the paper.
* **Local shooting / the current region** (`augChord_subset_or_region_right`, `_left`;
  invariant (B) of p. 504): a chord of `C` with a point on `C₂` either lies on a chord of `S₂`
  (the tie case of p. 504) or has its open part inside a single region of `S₂`.
* **Vertex truncations** (`truncL_mem_fusion`, `truncR_mem_fusion`, `vfuse_subset_chords`,
  `vfuse_subset_fusion`): the truncations of the vertex chords of `S_i` (`Junction.truncL`,
  `truncR`) are chords of the fusion; the *vertex fusion* `vfuse S₁ S₂` (truncations only) is a
  set of vertex chords of `C` contained in the fusion.
* **The region structure: overlay and contraction.**  The *overlay map* `overlayChords S₁ S₂`
  consists of all pieces (augmented chords of `C`) of the chords of `S₁ ∪ S₂`, plus the shared
  chords; it is a finite chord system (`overlayChordSystem`) whose free set is
  `overlayFree = C.dom \ (⋃ S₁ ∪ ⋃ S₂ ∪ ⋃ sharedChords)` (`freeIn_overlayChords`).  Its regions
  refine the regions of `S₁` and of `S₂` (`overlay_refines_left`, `_right`; in the box model
  after cutting also along the slit of `C_i`).  The fusion is a sub-family of the overlay
  (`fusion_subset_overlayChords`), so **each region of the fusion is the union of the overlay
  regions joined through the overlay chords not in the fusion** (`fusion_region_eq`, by the
  contraction theorem of `Chazelle.Merge.Removal`), and these *middle pieces* of a chord of `S₁`
  join two points of `C₂` and lie on a chord of `S₂` or inside one region of `S₂`
  (`middle_piece_left`; symmetrically `middle_piece_right`).  Every region of the fusion is
  bounded by the obstacle and by pieces of chords of `S₁`, `S₂` and of the shared chords
  (`frontier_fusion_region_subset`).

## What is *not* true: the fusion does not refine the overlay

The fusion keeps, of a chord `c ∈ S₁` crossed by `C₂`, only its *first* and *last* pieces
(from each endpoint of `c` to the first point of `C₂`).  The middle pieces of `c` (between two
consecutive crossings of `C₂`) are not chords of the fusion: the two sides of such a piece lie in
different regions of `S₁` but in the same region of the fusion.  So a region of the fusion is in
general **not** contained in a region of `S₁`; `fusion_region_eq` and `middle_piece_left` give
the exact relation instead.  The same holds for the vertex fusion `vfuse`.  This is consistent
with the paper, which never claims refinement (§3.2 only bounds the number of arcs per region).
-/

namespace Chazelle.Merge

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd rayPt_zero continuous_rayPt hseg
  segment_horizontal_eq_hseg)
open Chazelle.Chain (IsHChordIn ChordSystem freeIn regionsIn mem_regionsIn openHSeg
  hseg_inter_eq_openHSeg isPreconnected_openHSeg openHSeg_nonempty mem_openHSeg_iff)

/-! ### The fusion -/

namespace Junction

variable (J : Junction)

section
variable {p : Point}
/-- A point off the domain of `C₁` at height `≤ C₁.top.2` is off the domain of `C`. -/
theorem not_mem_whole_dom_of_left (hp : p.2 ≤ J.left.top.2) (h : p ∉ J.left.dom) :
    p ∉ J.whole.dom := by
  rw [not_mem_dom_iff J.whole (hp.trans J.left_top_le)]
  rcases (not_mem_dom_iff J.left hp).1 h with h' | h'
  · aesop
  · exact Or.inr (J.left_set_subset h')

/-- A point off the domain of `C₂` at height `≤ C₂.top.2` is off the domain of `C`. -/
theorem not_mem_whole_dom_of_right (hp : p.2 ≤ J.right.top.2)
    (h : p ∉ J.right.dom) : p ∉ J.whole.dom := by
  rw [not_mem_dom_iff J.whole (hp.trans J.right_top_le)]
  rcases (not_mem_dom_iff J.right hp).1 h with h' | h'
  · aesop
  · exact Or.inr (J.right_set_subset h')

/-- A point of the domain of `C₁` below the top of `C₁` and off `C₂` is in the domain of `C`. -/
theorem mem_whole_dom_of_left (hp : p.2 ≤ J.left.top.2) (h : p ∈ J.left.dom)
    (h2 : p ∉ J.right.set) : p ∈ J.whole.dom := by
  by_contra hnd
  rcases (not_mem_dom_iff J.whole (hp.trans J.left_top_le)).1 hnd with h' | h'
  · exact h' (J.left.dom_subset_box h)
  · rw [whole_set] at h'
    rcases h' with h' | h'
    · exact J.left.not_mem_set_of_mem_dom h h'
    simp_all

/-- A point of the domain of `C₂` below the top of `C₂` and off `C₁` is in the domain of `C`. -/
theorem mem_whole_dom_of_right (hp : p.2 ≤ J.right.top.2) (h : p ∈ J.right.dom)
    (h1 : p ∉ J.left.set) : p ∈ J.whole.dom := by
  by_contra hnd
  rcases (not_mem_dom_iff J.whole (hp.trans J.right_top_le)).1 hnd with h' | h'
  · exact h' (J.right.dom_subset_box h)
  · rw [whole_set] at h'
    rcases h' with h' | h'
    · exact h1 h'
    · exact J.right.not_mem_set_of_mem_dom h h'

/-- A point of the domain of `C` at height `≤ C₁.top.2` is in the domain of `C₁`. -/
theorem mem_left_dom_of_whole (hp : p.2 ≤ J.left.top.2) (h : p ∈ J.whole.dom) :
    p ∈ J.left.dom := by
  by_contra hnd
  rcases (not_mem_dom_iff J.left hp).1 hnd with h' | h'
  · exact h' (J.whole.dom_subset_box h)
  · exact J.whole.not_mem_set_of_mem_dom h (J.left_set_subset h')

/-- A point of the domain of `C` at height `≤ C₂.top.2` is in the domain of `C₂`. -/
theorem mem_right_dom_of_whole (hp : p.2 ≤ J.right.top.2) (h : p ∈ J.whole.dom) :
    p ∈ J.right.dom := by
  by_contra hnd
  rcases (not_mem_dom_iff J.right hp).1 hnd with h' | h'
  · exact h' (J.whole.dom_subset_box h)
  · exact J.whole.not_mem_set_of_mem_dom h (J.right_set_subset h')


end

/-- The chords of `C` at the shared vertex (Chazelle's chords "incident upon the vertices of
`∂C` resulting from the duplication of the vertex `C₁ ∩ C₂`"). -/
def sharedChords : Set (Set Point) :=
  {d | ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ J.whole.DirFree J.m₁ σ ∧ d = J.whole.chordSet J.m₁ σ}

/-- **The fusion of `S₁` and `S₂`** (Chazelle p. 501): the chords of `C` seen from the two
endpoints of every chord of `S₁ ∪ S₂` along that chord (when the direction is free for `C`),
together with the chords of `C` at the shared vertex. -/
def fusion (S₁ S₂ : Set (Set Point)) : Set (Set Point) :=
  {d | ∃ c ∈ S₁ ∪ S₂, FreeAt J.whole (lend c) 1 ∧ d = shoot J.whole (lend c) 1} ∪
    {d | ∃ c ∈ S₁ ∪ S₂, FreeAt J.whole (rend c) (-1) ∧ d = shoot J.whole (rend c) (-1)} ∪
    J.sharedChords

/-- The shared-vertex chords are vertex chords of `C`. -/
theorem sharedChords_subset_chords : J.sharedChords ⊆ J.whole.chords := by
  rintro d ⟨σ, hσ, h, rfl⟩
  exact ⟨J.m₁, σ, by simp_all, hσ, h, rfl⟩

/-- The shared-vertex chords belong to the fusion. -/
theorem sharedChords_subset_fusion (S₁ S₂ : Set (Set Point)) :
    J.sharedChords ⊆ J.fusion S₁ S₂ :=
  fun _ h => Or.inr h

section
variable {c : Set Point}
/-- The endpoints of an augmented chord of `C₁` are off the domain of `C`, at height
`≤ C.top.2`. -/
theorem ends_left (hc : c ∈ augChords J.left) :
    (lend c).2 ≤ J.left.top.2 ∧ lend c ∉ J.whole.dom ∧ (rend c).2 ≤ J.left.top.2 ∧
      rend c ∉ J.whole.dom := by
  obtain ⟨y, a, b, h, hy, -, hl, hr⟩ := augChords_spec hc
  rw [hl, hr]
  exact ⟨hy, J.not_mem_whole_dom_of_left hy h.left_not, hy,
    J.not_mem_whole_dom_of_left hy h.right_not⟩

/-- The endpoints of an augmented chord of `C₂` are off the domain of `C`, at height
`≤ C₂.top.2`. -/
theorem ends_right (hc : c ∈ augChords J.right) :
    (lend c).2 ≤ J.right.top.2 ∧ lend c ∉ J.whole.dom ∧ (rend c).2 ≤ J.right.top.2 ∧
      rend c ∉ J.whole.dom := by
  obtain ⟨y, a, b, h, hy, -, hl, hr⟩ := augChords_spec hc
  rw [hl, hr]
  exact ⟨hy, J.not_mem_whole_dom_of_right hy h.left_not, hy,
    J.not_mem_whole_dom_of_right hy h.right_not⟩


end

/-- **The fusion is an augmented submap of `V(C)`.** -/
theorem fusion_subset_augChords {S₁ S₂ : Set (Set Point)} (hS₁ : S₁ ⊆ augChords J.left)
    (hS₂ : S₂ ⊆ augChords J.right) : J.fusion S₁ S₂ ⊆ augChords J.whole := by
  have hends : ∀ c ∈ S₁ ∪ S₂, (lend c).2 ≤ J.whole.top.2 ∧ lend c ∉ J.whole.dom ∧
      (rend c).2 ≤ J.whole.top.2 ∧ rend c ∉ J.whole.dom := by
    rintro c (hc | hc)
    · obtain ⟨h1, h2, h3, h4⟩ := J.ends_left (hS₁ hc)
      exact ⟨h1.trans J.left_top_le, h2, h3.trans J.left_top_le, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := J.ends_right (hS₂ hc)
      exact ⟨h1.trans J.right_top_le, h2, h3.trans J.right_top_le, h4⟩
  rintro d ((⟨c, hc, hfree, rfl⟩ | ⟨c, hc, hfree, rfl⟩) | hd)
  · obtain ⟨h1, h2, -, -⟩ := hends c hc
    exact shoot_mem_augChords J.whole h1 h2 (Or.inl rfl) hfree
  · obtain ⟨-, -, h3, h4⟩ := hends c hc
    exact shoot_mem_augChords J.whole h3 h4 (Or.inr rfl) hfree
  · exact chords_subset_augChords J.whole (J.sharedChords_subset_chords hd)

/-- There are at most two shared-vertex chords (finiteness). -/
theorem sharedChords_finite : J.sharedChords.Finite := by
  refine ((finite_singleton (-1 : ℝ)).insert 1).image (fun σ => J.whole.chordSet J.m₁ σ)
    |>.subset ?_
  rintro d ⟨σ, hσ, -, rfl⟩
  grind

/-- There are at most two shared-vertex chords. -/
theorem sharedChords_ncard_le : J.sharedChords.ncard ≤ 2 := by
  have hsub : J.sharedChords ⊆ (fun σ => J.whole.chordSet J.m₁ σ) '' ({1, -1} : Set ℝ) := by
    rintro d ⟨σ, hσ, -, rfl⟩
    grind
  calc J.sharedChords.ncard
      ≤ ((fun σ => J.whole.chordSet J.m₁ σ) '' ({1, -1} : Set ℝ)).ncard :=
        ncard_le_ncard hsub ((toFinite _).image _)
    _ ≤ ({1, -1} : Set ℝ).ncard := ncard_image_le (toFinite _)
    _ = 2 := ncard_pair (by norm_num)

/-- The fusion is covered by the two shooting images of `S₁ ∪ S₂` and the shared chords. -/
theorem fusion_subset_image (S₁ S₂ : Set (Set Point)) :
    J.fusion S₁ S₂ ⊆ (fun c => shoot J.whole (lend c) 1) '' (S₁ ∪ S₂) ∪
      (fun c => shoot J.whole (rend c) (-1)) '' (S₁ ∪ S₂) ∪ J.sharedChords := by
  rintro d ((⟨c, hc, -, rfl⟩ | ⟨c, hc, -, rfl⟩) | hd)
  all_goals grind

section
variable {S₁ S₂ : Set (Set Point)} (h₁ : S₁.Finite) (h₂ : S₂.Finite)
include h₁ h₂
/-- The fusion of finite submaps is finite. -/
theorem fusion_finite :
    (J.fusion S₁ S₂).Finite :=
  ((((h₁.union h₂).image _).union ((h₁.union h₂).image _)).union J.sharedChords_finite).subset
    (J.fusion_subset_image S₁ S₂)

/-- **Size of the fusion**: at most two chords per chord of `S₁ ∪ S₂`, plus the two chords at
the shared vertex. -/
theorem ncard_fusion_le :
    (J.fusion S₁ S₂).ncard ≤ 2 * (S₁.ncard + S₂.ncard) + 2 := by
  have h12 := h₁.union h₂
  have hu : (S₁ ∪ S₂).ncard ≤ S₁.ncard + S₂.ncard := ncard_union_le _ _
  calc (J.fusion S₁ S₂).ncard
      ≤ ((fun c => shoot J.whole (lend c) 1) '' (S₁ ∪ S₂) ∪
          (fun c => shoot J.whole (rend c) (-1)) '' (S₁ ∪ S₂) ∪ J.sharedChords).ncard :=
        ncard_le_ncard (J.fusion_subset_image S₁ S₂)
          (((h12.image _).union (h12.image _)).union J.sharedChords_finite)
    _ ≤ ((fun c => shoot J.whole (lend c) 1) '' (S₁ ∪ S₂)).ncard +
          ((fun c => shoot J.whole (rend c) (-1)) '' (S₁ ∪ S₂)).ncard + J.sharedChords.ncard :=
        (ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_union_le _ _) _)
    _ ≤ (S₁ ∪ S₂).ncard + (S₁ ∪ S₂).ncard + 2 :=
        Nat.add_le_add (Nat.add_le_add (ncard_image_le h12) (ncard_image_le h12))
          J.sharedChords_ncard_le
    _ ≤ 2 * (S₁.ncard + S₂.ncard) + 2 := by omega

/-! ### Endpoints are preserved -/


end

section
variable {c : Set Point} (hc : c ∈ augChords J.left ∪ augChords J.right)
include hc
/-- A chord of `C₁` shot from its left endpoint along itself w.r.t. `C` stays inside it. -/
theorem shoot_lend_subset :
    shoot J.whole (lend c) 1 ⊆ c := by
  rcases hc with hc | hc
  · obtain ⟨y, a, b, h, hy, rfl, hl, -⟩ := augChords_spec hc
    rw [hl]
    exact shoot_subset_pos J.whole h.lt (J.not_mem_whole_dom_of_left hy h.right_not)
  · obtain ⟨y, a, b, h, hy, rfl, hl, -⟩ := augChords_spec hc
    rw [hl]
    exact shoot_subset_pos J.whole h.lt (J.not_mem_whole_dom_of_right hy h.right_not)

/-- A chord of `C₁` or `C₂` shot from its right endpoint along itself w.r.t. `C` stays
inside it. -/
theorem shoot_rend_subset :
    shoot J.whole (rend c) (-1) ⊆ c := by
  rcases hc with hc | hc
  · obtain ⟨y, a, b, h, hy, rfl, -, hr⟩ := augChords_spec hc
    rw [hr]
    exact shoot_subset_neg J.whole h.lt (J.not_mem_whole_dom_of_left hy h.left_not)
  · obtain ⟨y, a, b, h, hy, rfl, -, hr⟩ := augChords_spec hc
    rw [hr]
    exact shoot_subset_neg J.whole h.lt (J.not_mem_whole_dom_of_right hy h.left_not)


end

section
variable (hP : J.P.Simple) {p : Point}
include hP
/-- An endpoint of an augmented chord of `C₁` lies on `C₂` only if it is the shared vertex. -/
theorem end_not_mem_right_of_left (hp : p.2 ≤ J.left.top.2)
    (hnd : p ∉ J.left.dom) (hne : p ≠ J.shared) : p ∉ J.right.set := by
  intro hr
  rcases (not_mem_dom_iff J.left hp).1 hnd with h | h
  · exact h (J.right.set_subset_box hr)
  · have : p ∈ J.left.set ∩ J.right.set := ⟨h, hr⟩
    rw [J.left_inter_right hP] at this
    simp_all

/-- An endpoint of an augmented chord of `C₂` lies on `C₁` only if it is the shared vertex. -/
theorem end_not_mem_left_of_right (hp : p.2 ≤ J.right.top.2)
    (hnd : p ∉ J.right.dom) (hne : p ≠ J.shared) : p ∉ J.left.set := by
  intro hl
  rcases (not_mem_dom_iff J.right hp).1 hnd with h | h
  · exact h (J.left.set_subset_box hl)
  · have : p ∈ J.left.set ∩ J.right.set := ⟨hl, h⟩
    rw [J.left_inter_right hP] at this
    simp_all


end

section
variable (hP : J.P.Simple) {c : Set Point}
include hP
section
variable (hc : c ∈ augChords J.left)
include hc
/-- **Endpoints are preserved (left chords, left endpoint).**  For a chord `c` of `S₁` whose left
endpoint is not the shared vertex, the rightward direction at `lend c` is free for `C`; so the
fusion contains a chord `shoot C (lend c) 1 ⊆ c` with endpoint `lend c`. -/
theorem lend_freeAt_left
    (hne : lend c ≠ J.shared) : FreeAt J.whole (lend c) 1 := by
  obtain ⟨y, a, b, h, hy, rfl, hl, -⟩ := augChords_spec hc
  rw [hl] at hne ⊢
  have hnr := J.end_not_mem_right_of_left hP hy h.left_not hne
  have hev := eventually_not_mem_of_not_mem J.right.isClosed_set hnr 1
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < b - a by linarith [h.lt])] with t ht1 ht2
  have e : rayPt ((a, y) : Point) 1 t = ((a + t, y) : Point) := by simp [rayPt]
  rw [e] at ht1 ⊢
  exact J.mem_whole_dom_of_left hy (h.open_mem _ (by simp_all) (by grind)) ht1

/-- Endpoints are preserved (left chords, right endpoint). -/
theorem rend_freeAt_left
    (hne : rend c ≠ J.shared) : FreeAt J.whole (rend c) (-1) := by
  obtain ⟨y, a, b, h, hy, rfl, -, hr⟩ := augChords_spec hc
  rw [hr] at hne ⊢
  have hnr := J.end_not_mem_right_of_left hP hy h.right_not hne
  have hev := eventually_not_mem_of_not_mem J.right.isClosed_set hnr (-1)
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < b - a by linarith [h.lt])] with t ht1 ht2
  have e : rayPt ((b, y) : Point) (-1) t = ((b - t, y) : Point) := by
    simp [rayPt, sub_eq_add_neg]
  rw [e] at ht1 ⊢
  exact J.mem_whole_dom_of_left hy (h.open_mem _ (by grind) (by simp_all)) ht1


end

section
variable (hc : c ∈ augChords J.right)
include hc
/-- Endpoints are preserved (right chords, left endpoint). -/
theorem lend_freeAt_right
    (hne : lend c ≠ J.shared) : FreeAt J.whole (lend c) 1 := by
  obtain ⟨y, a, b, h, hy, rfl, hl, -⟩ := augChords_spec hc
  rw [hl] at hne ⊢
  have hnl := J.end_not_mem_left_of_right hP hy h.left_not hne
  have hev := eventually_not_mem_of_not_mem J.left.isClosed_set hnl 1
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < b - a by linarith [h.lt])] with t ht1 ht2
  have e : rayPt ((a, y) : Point) 1 t = ((a + t, y) : Point) := by simp [rayPt]
  rw [e] at ht1 ⊢
  exact J.mem_whole_dom_of_right hy (h.open_mem _ (by simp_all) (by grind)) ht1

/-- Endpoints are preserved (right chords, right endpoint). -/
theorem rend_freeAt_right
    (hne : rend c ≠ J.shared) : FreeAt J.whole (rend c) (-1) := by
  obtain ⟨y, a, b, h, hy, rfl, -, hr⟩ := augChords_spec hc
  rw [hr] at hne ⊢
  have hnl := J.end_not_mem_left_of_right hP hy h.right_not hne
  have hev := eventually_not_mem_of_not_mem J.left.isClosed_set hnl (-1)
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : ℝ) < b - a by linarith [h.lt])] with t ht1 ht2
  have e : rayPt ((b, y) : Point) (-1) t = ((b - t, y) : Point) := by
    simp [rayPt, sub_eq_add_neg]
  rw [e] at ht1 ⊢
  exact J.mem_whole_dom_of_right hy (h.open_mem _ (by grind) (by simp_all)) ht1



end

end

/-- **Endpoints are preserved** (summary): every endpoint of a chord of `S₁ ∪ S₂` other than the
shared vertex is an endpoint of a chord of the fusion contained in that chord. -/
theorem end_mem_fusion (hP : J.P.Simple) {S₁ S₂ : Set (Set Point)}
    (hS₁ : S₁ ⊆ augChords J.left) (hS₂ : S₂ ⊆ augChords J.right) {c : Set Point}
    (hc : c ∈ S₁ ∪ S₂) :
    (lend c ≠ J.shared → ∃ d ∈ J.fusion S₁ S₂, lend c ∈ d ∧ d ⊆ c) ∧
      (rend c ≠ J.shared → ∃ d ∈ J.fusion S₁ S₂, rend c ∈ d ∧ d ⊆ c) := by
  have hc' : c ∈ augChords J.left ∪ augChords J.right := by
    grind
  refine ⟨fun hne => ⟨_, Or.inl (Or.inl ⟨c, hc, ?_, rfl⟩), Geometry.left_mem_segment _ _,
    J.shoot_lend_subset hc'⟩, fun hne => ⟨_, Or.inl (Or.inr ⟨c, hc, ?_, rfl⟩),
    Geometry.left_mem_segment _ _, J.shoot_rend_subset hc'⟩⟩
  · rcases hc with hc | hc
    · exact J.lend_freeAt_left hP (hS₁ hc) hne
    · exact J.lend_freeAt_right hP (hS₂ hc) hne
  · rcases hc with hc | hc
    · exact J.rend_freeAt_left hP (hS₁ hc) hne
    · exact J.rend_freeAt_right hP (hS₂ hc) hne

/-! ### Chords of the fusion between two points of one side -/

/-! ### Local shooting: the current region -/

/-! ### Vertex truncations -/

/-! ### The overlay and the boundary of the regions of the fusion -/

/-! ### The overlay as a chord system; the fusion as its contraction -/

end Junction

end

end Chazelle.Merge
