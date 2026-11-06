module

public meta import Chazelle.Arithmetic

public import Chazelle.Visibility.Map
public import Chazelle.Existence.Arc

/-!
# Submaps of the horizontal visibility map: chord separation and exact splitting

A *submap* is a set `S ⊆ chords P` of vertex chords of a simple polygon `P`.  Its free set
`freeOf P S` is the interior `P.filled \ P.boundary` minus the chords of `S`, and its
*regions* `regionsOf P S` are the connected components of the free set (so
`regions P = regionsOf P (chords P)`).

* `chord_separates` (Chazelle's Lemma 2.1, interior version): for `c ∈ S` and an interior
  point `z` of `c`, the points `z ± (0, ε)` lie in the free set of `S` and in *different*
  regions.  The proof builds the closed walk `arcPoly` from the chord and one boundary arc of
  `P` between its endpoints; its boundary lies in `P.boundary ∪ c`, so the crossing parity of
  this walk is constant on every region, while it flips across the chord (`parity_flip`).
* `regionsOf_insert` (exact splitting): adding a chord `c ∉ S` to `S` replaces the unique
  region `R` containing the open chord by exactly two regions `R₁ ≠ R₂` with
  `R₁ ∪ R₂ = R \ c`, and leaves the other regions unchanged.
* `ncard_regionsOf`: a submap with `k` chords has exactly `k + 1` regions; in particular
  `regions_ncard : (regions P).ncard = (chords P).ncard + 1 ≤ 2 n + 1`.
-/

namespace Chazelle.Visibility

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan

/-! ### Regions of a submap -/

section
variable (P : Polygon) (S : Set (Set Point))
include P S
/-- The free set of the submap `S`: the interior of `P` minus the chords of `S`. -/
def freeOf : Set Point :=
  (P.filled \ P.boundary) \ ⋃₀ S

/-- The regions of the submap `S`: the connected components of its free set. -/
def regionsOf : Set (Set Point) :=
  {C | ∃ z ∈ freeOf P S, C = connectedComponentIn (freeOf P S) z}


end

/-- The union of a set of chords is closed. -/
theorem isClosed_sUnion_of_subset_chords {P : Polygon} {S : Set (Set Point)}
    (hS : S ⊆ chords P) : IsClosed (⋃₀ S) :=
  ((chords_finite P).subset hS).isClosed_sUnion fun _ h => chords_isClosed (hS h)

/-- The free set of a submap is open. -/
theorem isOpen_freeOf {P : Polygon} (hP : P.Simple) {S : Set (Set Point)} (hS : S ⊆ chords P) :
    IsOpen (freeOf P S) :=
  (isOpen_filled_sdiff_boundary hP).sdiff (isClosed_sUnion_of_subset_chords hS)

theorem freeOf_anti (P : Polygon) {S T : Set (Set Point)} (h : S ⊆ T) :
    freeOf P T ⊆ freeOf P S :=
  fun _ hp => ⟨hp.1, fun hm => hp.2 (sUnion_mono h hm)⟩

theorem freeOf_insert (P : Polygon) (c : Set Point) (S : Set (Set Point)) :
    freeOf P (insert c S) = freeOf P S \ c := by
  grind [freeOf, sUnion_insert, Set.mem_sdiff, mem_union]

theorem mem_regionsOf {P : Polygon} {S : Set (Set Point)} {z : Point} (hz : z ∈ freeOf P S) :
    connectedComponentIn (freeOf P S) z ∈ regionsOf P S := ⟨z, hz, rfl⟩

/-- Every region of a submap is open. -/
theorem regionsOf_open {P : Polygon} (hP : P.Simple) {S : Set (Set Point)} (hS : S ⊆ chords P)
    {C : Set Point} (hC : C ∈ regionsOf P S) : IsOpen C := by
  obtain ⟨z, -, rfl⟩ := hC
  exact (isOpen_freeOf hP hS).connectedComponentIn

section
variable {P : Polygon} {S : Set (Set Point)} {C : Set Point} (hC : C ∈ regionsOf P S)
include P S hC
/-- Every region of a submap is nonempty. -/
theorem regionsOf_nonempty : C.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := hC
  exact ⟨z, mem_connectedComponentIn hz⟩

/-- Every region of a submap is preconnected. -/
theorem regionsOf_isPreconnected : IsPreconnected C := by
  obtain ⟨z, -, rfl⟩ := hC
  exact isPreconnected_connectedComponentIn

/-- Every region of a submap lies in the free set. -/
theorem regionsOf_subset : C ⊆ freeOf P S := by
  obtain ⟨z, -, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

/-- A region is the component of each of its points. -/
theorem regionsOf_eq_component {p : Point} (hp : p ∈ C) :
    C = connectedComponentIn (freeOf P S) p := by
  obtain ⟨z, -, rfl⟩ := hC
  exact connectedComponentIn_eq hp


end

section
variable {P : Polygon} {S : Set (Set Point)} {C D : Set Point} (hC : C ∈ regionsOf P S) (hD : D ∈ regionsOf P S)
include P S hC hD
/-- Two regions of a submap are equal or disjoint. -/
theorem regionsOf_eq_or_disjoint : C = D ∨ Disjoint C D := by
  by_cases h : Disjoint C D
  · simp_all
  · left
    obtain ⟨p, hpC, hpD⟩ := not_disjoint_iff.1 h
    rw [regionsOf_eq_component hC hpC, regionsOf_eq_component hD hpD]

/-- Two distinct regions of a submap are disjoint. -/
theorem regionsOf_disjoint_of_ne (hne : C ≠ D) : Disjoint C D :=
  (regionsOf_eq_or_disjoint hC hD).resolve_left hne


end

/-- The empty submap has a single region, the whole interior. -/
theorem regionsOf_empty {P : Polygon} (hP : P.Simple) :
    regionsOf P ∅ = {P.filled \ P.boundary} := by
  have hfree : freeOf P ∅ = P.filled \ P.boundary := by
    simp [freeOf]
  ext C
  simp only [regionsOf, mem_ofPred_eq, mem_singleton_iff, hfree]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (filled_sdiff_boundary_connected hP).connectedComponentIn hz
  · rintro rfl
    obtain ⟨z, hz⟩ := filled_sdiff_boundary_nonempty hP
    exact ⟨z, hz, ((filled_sdiff_boundary_connected hP).connectedComponentIn hz).symm⟩

/-! ### Chords: elementary facts -/

/-- Every chord is horizontal: all its points share the ordinate of any of them. -/
theorem chords_snd_eq {P : Polygon} {c : Set Point} (hc : c ∈ chords P) {p q : Point}
    (hp : p ∈ c) (hq : q ∈ c) : p.2 = q.2 := by
  obtain ⟨i, σ, -, -, -, rfl⟩ := hc
  rw [chordSet_eq_hseg] at hp hq
  rw [hp.1, hq.1]

section
variable {P : Polygon} (hP : P.Simple)
include hP
/-- A chord lies in the filled region. -/
theorem chords_subset_filled {c : Set Point} (hc : c ∈ chords P) :
    c ⊆ P.filled := by
  obtain ⟨i, σ, hi, -, h, rfl⟩ := hc
  exact chordSet_subset_filled hP hi h

/-- Two distinct chords meet only in boundary points. -/
theorem chords_inter_subset_boundary {c d : Set Point}
    (hc : c ∈ chords P) (hd : d ∈ chords P) (hne : c ≠ d) : c ∩ d ⊆ P.boundary := by
  obtain ⟨i, σ, hi, hσ, hiσ, rfl⟩ := hc
  obtain ⟨j, τ, hj, hτ, hjτ, rfl⟩ := hd
  intro p hp
  rcases chordSet_inter hP hi hj hσ hτ hiσ hjτ hp with h | ⟨h, -⟩
  · simp_all
  · simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact Existence.vtx_mem_boundary P hi
    · exact chordEnd_mem_boundary hP hi hiσ

/-- The interior part of a chord lies in the free set of every submap not containing it. -/
theorem chord_sdiff_subset_freeOf {S : Set (Set Point)}
    (hS : S ⊆ chords P) {c : Set Point} (hc : c ∈ chords P) (hcS : c ∉ S) :
    c \ P.boundary ⊆ freeOf P S := by
  rintro p ⟨hp, hpb⟩
  refine ⟨⟨chords_subset_filled hP hc hp, hpb⟩, ?_⟩
  rintro ⟨d, hd, hpd⟩
  have hne : c ≠ d := fun h => hcS (h ▸ hd)
  exact hpb (chords_inter_subset_boundary hP hc (hS hd) hne ⟨hp, hpd⟩)

/-- The interior part of a chord is the open chord. -/
theorem chordSet_sdiff_boundary {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : chordSet P i σ \ P.boundary = openChordSet P i σ := by
  ext p
  constructor
  · rintro ⟨hp, hpb⟩
    rw [chordSet_eq_openChordSet_union hP hi h] at hp
    rcases hp with hp | hp
    · exact hp
    · exfalso
      rcases hp with rfl | rfl
      · exact hpb (Existence.vtx_mem_boundary P hi)
      · exact hpb (chordEnd_mem_boundary hP hi h)
  · intro hp
    refine ⟨?_, (openChordSet_subset_interior hP hi h hp).2⟩
    rw [chordSet_eq_openChordSet_union hP hi h]
    simp_all


end

/-- The open chord is preconnected. -/
theorem isPreconnected_openChordSet (P : Polygon) (i : ℕ) (σ : ℝ) :
    IsPreconnected (openChordSet P i σ) :=
  isPreconnected_Ioo.image _ (continuous_rayPt _ σ).continuousOn

section
variable {P : Polygon} (hP : P.Simple)
include hP
/-- The open chord is nonempty. -/
theorem openChordSet_nonempty {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) : (openChordSet P i σ).Nonempty :=
  ⟨_, ⟨chordParam P i σ / 2, ⟨by linarith [chordParam_pos hP hi h],
    by linarith [chordParam_pos hP hi h]⟩, rfl⟩⟩

/-- The interior part of a chord is nonempty and preconnected. -/
theorem chord_sdiff_nonempty_isPreconnected {c : Set Point}
    (hc : c ∈ chords P) : (c \ P.boundary).Nonempty ∧ IsPreconnected (c \ P.boundary) := by
  obtain ⟨i, σ, hi, -, h, rfl⟩ := hc
  rw [chordSet_sdiff_boundary hP hi h]
  exact ⟨openChordSet_nonempty hP hi h, isPreconnected_openChordSet P i σ⟩

/-! ### The closed walk made of a chord and a boundary arc -/


end

/-- The closed walk with vertices `P.vtx i, P.vtx (i+1), …, P.vtx (i+m-1)` (indices mod `n`)
followed by the point `e`. -/
def arcPoly (P : Polygon) (i m : ℕ) (e : Point) : Polygon :=
  ⟨(List.range m).map (fun k => P.vtx ((i + k) % P.n)) ++ [e]⟩

section
variable (P : Polygon)
@[simp] theorem arcPoly_n (i m : ℕ) (e : Point) : (arcPoly P i m e).n = m + 1 := by
  simp [arcPoly, Polygon.n]

theorem arcPoly_vtx_of_lt (i : ℕ) {m : ℕ} (e : Point) {k : ℕ} (hk : k < m) :
    (arcPoly P i m e).vtx k = P.vtx ((i + k) % P.n) := by
  simp only [arcPoly, Polygon.vtx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp_all), List.getElem?_map, List.getElem?_range hk]
  rfl

theorem arcPoly_vtx_last (i m : ℕ) (e : Point) : (arcPoly P i m e).vtx m = e := by
  simp [arcPoly, Polygon.vtx, List.getD_eq_getElem?_getD]


end

section
variable (P : Polygon) (i : ℕ) {m : ℕ} (e : Point)
theorem arcPoly_edge_of_lt {k : ℕ} (hk : k + 1 < m) :
    (arcPoly P i m e).edge k = P.edge ((i + k) % P.n) := by
  unfold Polygon.edge
  rw [arcPoly_n, Nat.mod_eq_of_lt (by omega : k + 1 < m + 1), arcPoly_vtx_of_lt P i e (by omega),
    arcPoly_vtx_of_lt P i e hk, Existence.mod_add_one_mod]

section
variable (hm : 0 < m)
include hm
theorem arcPoly_edge_pen :
    (arcPoly P i m e).edge (m - 1) = Chazelle.segment (P.vtx ((i + (m - 1)) % P.n)) e := by
  unfold Polygon.edge
  rw [arcPoly_n, show m - 1 + 1 = m by omega, Nat.mod_eq_of_lt (by omega : m < m + 1),
    arcPoly_vtx_of_lt P i e (by omega), arcPoly_vtx_last]

theorem arcPoly_edge_last :
    (arcPoly P i m e).edge m = Chazelle.segment e (P.vtx (i % P.n)) := by
  unfold Polygon.edge
  rw [arcPoly_n, Nat.mod_self, arcPoly_vtx_of_lt P i e hm, arcPoly_vtx_last, Nat.add_zero]



end

end

section
variable (P : Polygon) (hn : 0 < P.n) (i : ℕ) {m : ℕ} (e : Point) (hm : 0 < m) (hpen : Chazelle.segment (P.vtx ((i + (m - 1)) % P.n)) e ⊆ P.boundary)
include hn hm hpen
/-- Every edge of the walk other than the last lies in the boundary of `P`, provided the
penultimate edge does. -/
theorem arcPoly_edge_subset_boundary {k : ℕ}
    (hk : k < m) : (arcPoly P i m e).edge k ⊆ P.boundary := by
  rcases Nat.lt_or_ge (k + 1) m with h | h
  · rw [arcPoly_edge_of_lt P i e h]
    exact Existence.edge_subset_boundary P (Nat.mod_lt _ hn)
  · have : k = m - 1 := by omega
    subst this
    rw [arcPoly_edge_pen P i e hm]
    exact hpen

/-- The boundary of the walk lies in the boundary of `P` together with the closing segment. -/
theorem arcPoly_boundary_subset :
    (arcPoly P i m e).boundary ⊆ P.boundary ∪ Chazelle.segment e (P.vtx (i % P.n)) := by
  rintro p ⟨k, hk, hp⟩
  rw [arcPoly_n] at hk
  rcases Nat.lt_or_ge k m with h | h
  · exact Or.inl (arcPoly_edge_subset_boundary P hn i e hm hpen h hp)
  · have : k = m := by omega
    subst this
    rw [arcPoly_edge_last P i e hm] at hp
    simp_all

/-! ### Chord separation -/


end

section
variable {P : Polygon} (hP : P.Simple)
include hP
/-- **The parity flip across a chord.**  For an interior point `z` of the chord of vertex `i`
in direction `σ`, there is a closed walk `Γ` whose boundary lies in `P.boundary ∪ chord`, such
that the points `z ± (0, ε)` (small `ε > 0`) are off the boundary of `Γ` and have different
crossing parities with respect to `Γ`. -/
theorem exists_walk_parity_flip {i : ℕ} (hi : i < P.n) {σ : ℝ}
    (h : DirInterior P i σ) {z : Point} (hz : z ∈ chordSet P i σ)
    (hzb : z ∉ P.boundary) :
    ∃ Γ : Polygon, Γ.boundary ⊆ P.boundary ∪ chordSet P i σ ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        (z.1, z.2 + ε) ∉ Γ.boundary ∧ (z.1, z.2 - ε) ∉ Γ.boundary ∧
          parity Γ (z.1, z.2 + ε) ≠ parity Γ (z.1, z.2 - ε) := by
  have hn : 0 < P.n := by omega
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
  have hii : i % P.n = i := Nat.mod_eq_of_lt hi
  refine ⟨arcPoly P i m e, ?_, ?_⟩
  · refine (arcPoly_boundary_subset P hn i e hm0 hpen).trans ?_
    rw [hii, Geometry.segment_comm]
    exact le_rfl
  · have hzΓ : z ∈ (arcPoly P i m e).edge m := by
      rw [arcPoly_edge_last P i e hm0, hii, Geometry.segment_comm]
      exact hz
    have hmn : m < (arcPoly P i m e).n := by grind [arcPoly_n]
    have hsucc : (m + 1) % (arcPoly P i m e).n = 0 := by rw [arcPoly_n, Nat.mod_self]
    have hv0 : (arcPoly P i m e).vtx 0 = P.vtx i := by
      rw [arcPoly_vtx_of_lt P i e hm0, Nat.add_zero, hii]
    have hne : ((arcPoly P i m e).vtx m).1 ≠ ((arcPoly P i m e).vtx ((m + 1) % (arcPoly P i m e).n)).1 := by
      rw [hsucc, hv0, arcPoly_vtx_last, he, chordEnd_fst]
      intro heq
      have hσ0 : σ ≠ 0 := h.ne_zero hi
      have hpos := chordParam_pos hP hi h
      core_grind
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

/-- **Chord separation** (Lemma 2.1, interior case).  Let `S ⊆ chords P`, `c ∈ S`, and let `z`
be an interior point of `c`.  Then for all small `ε > 0` the points `z ± (0, ε)` lie in the
free set of `S` and in different regions of `S`. -/
theorem chord_separates {S : Set (Set Point)} (hS : S ⊆ chords P)
    {c : Set Point} (hc : c ∈ S) {z : Point} (hz : z ∈ c) (hzb : z ∉ P.boundary) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      (z.1, z.2 + ε) ∈ freeOf P S ∧ (z.1, z.2 - ε) ∈ freeOf P S ∧
        connectedComponentIn (freeOf P S) (z.1, z.2 + ε) ≠
          connectedComponentIn (freeOf P S) (z.1, z.2 - ε) := by
  obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hS hc
  obtain ⟨Γ, hΓ, ε₁, hε₁, hflip⟩ := exists_walk_parity_flip hP hi h hz hzb
  -- the two points are eventually in the free set
  have hup : Tendsto (fun ε : ℝ => ((z.1, z.2 + ε) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1, z.2 + ε) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  have hdn : Tendsto (fun ε : ℝ => ((z.1, z.2 - ε) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1, z.2 - ε) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  have hzint : z ∈ P.filled \ P.boundary := ⟨chordSet_subset_filled hP hi h hz, hzb⟩
  have hint : (P.filled \ P.boundary) ∈ 𝓝 z := (isOpen_filled_sdiff_boundary hP).mem_nhds hzint
  -- the other chords: a closed set not containing `z`
  have hK : IsClosed (⋃₀ (S \ {chordSet P i σ})) :=
    isClosed_sUnion_of_subset_chords (fun _ hd => hS hd.1)
  have hzK : z ∉ ⋃₀ (S \ {chordSet P i σ}) := by
    rintro ⟨d, ⟨hdS, hdc⟩, hzd⟩
    rw [mem_singleton_iff] at hdc
    exact hzb (chords_inter_subset_boundary hP (hS hc) (hS hdS) (Ne.symm hdc) ⟨hz, hzd⟩)
  have hKn : (⋃₀ (S \ {chordSet P i σ}))ᶜ ∈ 𝓝 z := hK.isOpen_compl.mem_nhds hzK
  have hfree : ∀ ε : ℝ, 0 < ε → ∀ p : Point, p.1 = z.1 → p.2 ≠ z.2 →
      p ∈ P.filled \ P.boundary → p ∉ ⋃₀ (S \ {chordSet P i σ}) → p ∈ freeOf P S := by
    intro ε hε p hp1 hp2 hpint hpK
    refine ⟨hpint, ?_⟩
    rintro ⟨d, hdS, hpd⟩
    grind [Chazelle.Visibility.chords_snd_eq]
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (z.1, z.2 + ε) ∈ freeOf P S ∧ (z.1, z.2 - ε) ∈ freeOf P S ∧
        connectedComponentIn (freeOf P S) (z.1, z.2 + ε) ≠
          connectedComponentIn (freeOf P S) (z.1, z.2 - ε) := by
    filter_upwards [hup.eventually hint, hdn.eventually hint, hup.eventually hKn,
      hdn.eventually hKn, self_mem_nhdsWithin, Ioo_mem_nhdsGT hε₁] with ε h1 h2 h3 h4 h5 h6
    have hε : 0 < ε := h5
    have hp : (z.1, z.2 + ε) ∈ freeOf P S :=
      hfree ε hε _ rfl (by linarith) h1 h3
    have hq : (z.1, z.2 - ε) ∈ freeOf P S :=
      hfree ε hε _ rfl (by linarith) h2 h4
    refine ⟨hp, hq, fun heq => ?_⟩
    obtain ⟨-, -, hpar⟩ := hflip ε hε h6.2
    apply hpar
    have hsub : freeOf P S ⊆ Γ.boundaryᶜ := by
      intro p hp hpΓ
      rcases hΓ hpΓ with hb | hcc
      · exact hp.1.2 hb
      · exact hp.2 ⟨_, hc, hcc⟩
    exact parity_eq_of_isPreconnected Γ isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans hsub) (mem_connectedComponentIn hp)
      (heq ▸ mem_connectedComponentIn hq)
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  exact ⟨ε₀, mem_Ioi.1 hε₀, fun ε h1 h2 => hsub ⟨h1, h2⟩⟩

/-! ### Half-disks -/


end

/-- The open half-disk (for the sup metric: half-square) of radius `r` around `w`, on the side
`τ` (`1` = above, `-1` = below). -/
def halfDisk (w : Point) (r τ : ℝ) : Set Point := ball w r ∩ {p | 0 < τ * (p.2 - w.2)}

theorem mem_halfDisk_iff {w p : Point} {r τ : ℝ} :
    p ∈ halfDisk w r τ ↔ (|p.1 - w.1| < r ∧ |p.2 - w.2| < r) ∧ 0 < τ * (p.2 - w.2) := by
  grind [halfDisk, mem_inter_iff, mem_ofPred_eq, mem_ball_iff_abs]

section
variable (w : Point) (r τ : ℝ)
theorem halfDisk_subset_ball : halfDisk w r τ ⊆ ball w r :=
  inter_subset_left

theorem convex_halfDisk : Convex ℝ (halfDisk w r τ) := by
  refine (convex_ball w r).inter ?_
  intro p hp q hq a b ha hb hab
  simp only [mem_ofPred_eq] at hp hq ⊢
  simp only [Geometry.add_snd, Geometry.smul_snd]
  have : τ * (a * p.2 + b * q.2 - w.2) = a * (τ * (p.2 - w.2)) + b * (τ * (q.2 - w.2)) := by
    grind
  rw [this]
  rcases ha.lt_or_eq with ha' | ha'
  · positivity
  · rw [← ha', zero_add] at hab
    positivity

theorem isPreconnected_halfDisk : IsPreconnected (halfDisk w r τ) :=
  (convex_halfDisk w r τ).isPreconnected


end

/-- The point at signed vertical distance `s` from `w` lies in the half-disk. -/
theorem vert_mem_halfDisk {w : Point} {r τ s : ℝ} (hτ : τ = 1 ∨ τ = -1) (hs0 : 0 < s)
    (hsr : s < r) : ((w.1, w.2 + τ * s) : Point) ∈ halfDisk w r τ := by
  rw [mem_halfDisk_iff]
  simp only [sub_self, abs_zero, add_sub_cancel_left]
  rcases hτ with rfl | rfl
  all_goals grind

section
variable {w w' : Point} {r r' τ : ℝ}
/-- A half-disk around a point at the same height, inside the ball, is inside the half-disk. -/
theorem halfDisk_mono (hh : w'.2 = w.2) (hb : ball w' r' ⊆ ball w r) :
    halfDisk w' r' τ ⊆ halfDisk w r τ := by
  rintro p ⟨hp1, hp2⟩
  refine ⟨hb hp1, ?_⟩
  simp_all

/-- Two half-disks on the same side, centred at the same height and at horizontal distance
less than the first radius, meet. -/
theorem halfDisk_inter_nonempty (hτ : τ = 1 ∨ τ = -1)
    (hh : w'.2 = w.2) (hx : |w'.1 - w.1| < r) (hr' : 0 < r') :
    (halfDisk w r τ ∩ halfDisk w' r' τ).Nonempty := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hx
  set s := min r r' / 2 with hs
  have hs0 : 0 < s := by simp_all
  have hsr : s < r := by grind
  have hsr' : s < r' := by grind
  refine ⟨(w'.1, w.2 + τ * s), ?_, ?_⟩
  · rw [mem_halfDisk_iff]
    simp only [add_sub_cancel_left]
    have habs : |τ * s| < r := by
      grind
    refine ⟨⟨hx, habs⟩, ?_⟩
    have : τ * (τ * s) = s := by grind
    simp_all
  · rw [← hh]
    exact vert_mem_halfDisk hτ hs0 hsr'

/-! ### Exact splitting -/


end

section
variable {P : Polygon} {S : Set (Set Point)}
/-- A half-disk at a chord point, inside the free set of `S`, avoids the chord and so lies in
the free set of `insert c S`. -/
theorem halfDisk_subset_freeOf_insert {c : Set Point}
    (hc : c ∈ chords P) {w : Point} (hw : w ∈ c) {r τ : ℝ} (hball : ball w r ⊆ freeOf P S) :
    halfDisk w r τ ⊆ freeOf P (insert c S) := by
  rintro p ⟨hp1, hp2⟩
  grind [Chazelle.Visibility.freeOf_insert, Chazelle.Visibility.chords_snd_eq]

/-- A preconnected subset of the free set meeting a region lies in it. -/
theorem subset_regionsOf_of_inter {U : Set Point}
    (hU : U ∈ regionsOf P S) {T : Set Point} (hT : IsPreconnected T) (hTS : T ⊆ freeOf P S)
    (hne : (T ∩ U).Nonempty) : T ⊆ U := by
  obtain ⟨q, hqT, hqU⟩ := hne
  rw [regionsOf_eq_component hU hqU]
  exact hT.subset_connectedComponentIn hqT hTS


end

section
variable {P : Polygon} (hP : P.Simple)
include hP
/-- Around every interior point of a chord `c` inside an open set `R` there is a ball inside
`R` whose points at the height of the chord lie on `c`. -/
theorem exists_ball_chord {c : Set Point} (hc : c ∈ chords P)
    {R : Set Point} (hR : IsOpen R) (hcR : c \ P.boundary ⊆ R) {w : Point}
    (hw : w ∈ c \ P.boundary) :
    ∃ r > (0 : ℝ), ball w r ⊆ R ∧ ∀ p ∈ ball w r, p.2 = w.2 → p ∈ c := by
  obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hc
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hR w (hcR hw)
  rw [chordSet_sdiff_boundary hP hi h] at hw
  obtain ⟨t, ⟨ht0, htL⟩, rfl⟩ := hw
  refine ⟨min r₁ (min t (chordParam P i σ - t)), lt_min hr₁ (lt_min ht0 (by linarith)),
    (ball_subset_ball (min_le_left _ _)).trans hball, fun p hp hp2 => ?_⟩
  rw [mem_ball_iff_abs] at hp
  simp only [rayPt_fst, rayPt_snd] at hp hp2
  have h1 : |p.1 - ((P.vtx i).1 + σ * t)| < t :=
    lt_of_lt_of_le hp.1 ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : |p.1 - ((P.vtx i).1 + σ * t)| < chordParam P i σ - t :=
    lt_of_lt_of_le hp.1 ((min_le_right _ _).trans (min_le_right _ _))
  rw [abs_lt] at h1 h2
  have hσσ : σ * σ = 1 := by grind
  have hmem : p ∈ openChordSet P i σ := by
    refine ⟨t + σ * (p.1 - ((P.vtx i).1 + σ * t)), ⟨?_, ?_⟩, ?_⟩
    · rcases hσ with rfl | rfl <;> linarith
    · rcases hσ with rfl | rfl <;> linarith
    grind [Geometry.point_ext_iff, rayPt_fst, rayPt_snd]
  rw [chordSet_eq_openChordSet_union hP hi h]
  grind

/-- **Half-disks on one side of a chord all lie in the same region.**  Let `R` be an open set
containing the interior part of the chord `c` and contained in the free set of `S`, and let
`U` be a region of `insert c S`.  If some half-disk (on side `τ`, inside `R`) at an interior
point of `c` lies in `U`, then every such half-disk does. -/
theorem halfDisk_all {S : Set (Set Point)} {c : Set Point}
    (hc : c ∈ chords P) {R : Set Point} (hR : IsOpen R) (hcR : c \ P.boundary ⊆ R)
    (hRS : R ⊆ freeOf P S) {U : Set Point} (hU : U ∈ regionsOf P (insert c S)) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1)
    (hex : ∃ w ∈ c \ P.boundary, ∃ r > (0 : ℝ), ball w r ⊆ R ∧ halfDisk w r τ ⊆ U) :
    ∀ w ∈ c \ P.boundary, ∀ r > (0 : ℝ), ball w r ⊆ R → halfDisk w r τ ⊆ U := by
  -- a half-disk inside `R` meeting `U` lies in `U`
  have key : ∀ w ∈ c, ∀ r : ℝ, ball w r ⊆ R → (halfDisk w r τ ∩ U).Nonempty →
      halfDisk w r τ ⊆ U := fun w hw r hb hne =>
    subset_regionsOf_of_inter hU (isPreconnected_halfDisk w r τ)
      (halfDisk_subset_freeOf_insert hc hw (hb.trans hRS)) hne
  obtain ⟨i, σ, hi, hσ, h, rfl⟩ := hc
  have hσ1 : |σ| = 1 := by grind
  have hopen : chordSet P i σ \ P.boundary = openChordSet P i σ := chordSet_sdiff_boundary hP hi h
  rw [hopen] at hcR hex ⊢
  set v := P.vtx i
  set L := chordParam P i σ
  set T : Set ℝ := {t | ∃ r > (0 : ℝ), ball (rayPt v σ t) r ⊆ R ∧ halfDisk (rayPt v σ t) r τ ⊆ U}
    with hT
  -- `T` is open
  have hTopen : IsOpen T := by
    rw [Metric.isOpen_iff]
    rintro t ⟨r, hr, hb, hU'⟩
    refine ⟨r / 2, half_pos hr, fun t' ht' => ?_⟩
    rw [mem_ball, Real.dist_eq] at ht'
    have hb' : ball (rayPt v σ t') (r / 2) ⊆ ball (rayPt v σ t) r := by
      intro p hp
      rw [mem_ball_iff_abs] at hp ⊢
      simp only [rayPt_fst, rayPt_snd] at hp ⊢
      refine ⟨?_, by linarith⟩
      have : p.1 - (v.1 + σ * t) = (p.1 - (v.1 + σ * t')) + σ * (t' - t) := by ring
      rw [this]
      calc |(p.1 - (v.1 + σ * t')) + σ * (t' - t)|
          ≤ |p.1 - (v.1 + σ * t')| + |σ * (t' - t)| := abs_add_le _ _
        _ < r / 2 + r / 2 := by
            grind
        _ = r := by ring
    exact ⟨r / 2, half_pos hr, hb'.trans hb,
      (halfDisk_mono (w := rayPt v σ t) (w' := rayPt v σ t') rfl hb').trans hU'⟩
  -- `T` is relatively closed in the parameter interval
  have hTclosed : closure T ∩ Ioo 0 L ⊆ T := by
    rintro t ⟨htc, ht⟩
    set w := rayPt v σ t with hw
    have hwR : w ∈ R := hcR ⟨t, ht, rfl⟩
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hR w hwR
    obtain ⟨t', ht'T, htt'⟩ := Metric.mem_closure_iff.1 htc (r / 2) (half_pos hr)
    obtain ⟨r', hr', -, hU'⟩ := ht'T
    rw [Real.dist_eq] at htt'
    have hwc : w ∈ chordSet P i σ := by
      rw [chordSet_eq_image hP hi h]
      grind
    refine ⟨r, hr, hb, key w hwc r hb ?_⟩
    · have hx : |(rayPt v σ t').1 - w.1| < r := by
        rw [hw]
        simp only [rayPt_fst]
        grind
      obtain ⟨p, hp1, hp2⟩ := halfDisk_inter_nonempty hτ (by grind [rayPt_snd]) hx hr'
      exact ⟨p, hp1, hU' hp2⟩
  -- `T` meets the parameter interval
  have hTne : (Ioo 0 L ∩ T).Nonempty := by
    obtain ⟨w, ⟨t, ht, rfl⟩, r, hr, hb, hU'⟩ := hex
    exact ⟨t, ht, r, hr, hb, hU'⟩
  have hall : Ioo 0 L ⊆ T :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hTopen hTne hTclosed
  -- conclusion
  rintro w ⟨t, ht, rfl⟩ r hr hb
  obtain ⟨r₁, hr₁, -, hU'⟩ := hall ht
  have hwc : rayPt v σ t ∈ chordSet P i σ := by
    rw [chordSet_eq_image hP hi h]
    grind
  refine key _ hwc r hb ?_
  · obtain ⟨p, hp1, hp2⟩ := halfDisk_inter_nonempty hτ rfl (by simpa using hr) hr₁
    exact ⟨p, hp1, hU' hp2⟩


end

section
variable {P : Polygon} (hP : P.Simple) {S : Set (Set Point)} (hS : S ⊆ chords P) {c : Set Point} (hc : c ∈ chords P) (hcS : c ∉ S)
include hP hS hc hcS
/-- **Every region of `insert c S` inside the region `R` of `c` contains a half-disk at an
interior point of `c`.** -/
theorem exists_halfDisk_subset {z₀ : Point}
    (hz₀ : z₀ ∈ c \ P.boundary) {U : Set Point} (hU : U ∈ regionsOf P (insert c S)) {u : Point}
    (huU : u ∈ U) (huR : u ∈ connectedComponentIn (freeOf P S) z₀) :
    ∃ w ∈ c \ P.boundary, ∃ r > (0 : ℝ), ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
      ball w r ⊆ connectedComponentIn (freeOf P S) z₀ ∧ halfDisk w r τ ⊆ U := by
  have hS' : insert c S ⊆ chords P := insert_subset hc hS
  set A := freeOf P S with hA
  set A' := freeOf P (insert c S) with hA'
  set R := connectedComponentIn A z₀ with hR
  
  have hA'eq : A' = A \ c := freeOf_insert P c S
  have hz₀A : z₀ ∈ A := chord_sdiff_subset_freeOf hP hS hc hcS hz₀
  have hcR : c \ P.boundary ⊆ R :=
    (chord_sdiff_nonempty_isPreconnected hP hc).2.subset_connectedComponentIn hz₀
      (chord_sdiff_subset_freeOf hP hS hc hcS)
  have hRopen : IsOpen R := (isOpen_freeOf hP hS).connectedComponentIn
  have hRA : R ⊆ A := connectedComponentIn_subset _ _
  have hUopen : IsOpen U := regionsOf_open hP hS' hU
  have hUA' : U ⊆ A' := regionsOf_subset hU
  have hUeq : U = connectedComponentIn A' u := regionsOf_eq_component hU huU
  -- limit points of `U` in `A'` lie in `U`
  have hclos : closure U ∩ A' ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ A') :=
      (regionsOf_isPreconnected hU).subset_closure (subset_inter subset_closure hUA')
        inter_subset_left
    have := hpre.subset_connectedComponentIn ⟨subset_closure huU, hUA' huU⟩ inter_subset_right
    simp_all
  -- a chord point in the closure of `U`
  have hex : ∃ w ∈ c \ P.boundary, w ∈ closure U := by
    by_contra hno
    push Not at hno
    have hcl : closure U ∩ R ⊆ U := by
      rintro p ⟨hpc, hpR⟩
      refine hclos ⟨hpc, ?_⟩
      rw [hA'eq]
      refine ⟨hRA hpR, fun hpcc => ?_⟩
      exact hno p ⟨hpcc, (hRA hpR).1.2⟩ hpc
    have hRU : R ⊆ U :=
      isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUopen ⟨u, huR, huU⟩ hcl
    core_grind
  obtain ⟨w, hw, hwc⟩ := hex
  obtain ⟨r, hr, hb, hline⟩ := exists_ball_chord hP hc hRopen hcR hw
  obtain ⟨q, hqU, hdq⟩ := Metric.mem_closure_iff.1 hwc r hr
  have hqb : q ∈ ball w r := by grind [mem_ball, dist_comm]
  have hqc : q ∉ c := by
    grind
  have hq2 : q.2 ≠ w.2 := fun h => hqc (hline q hqb h)
  refine ⟨w, hw, r, hr, if w.2 < q.2 then 1 else -1, ?_, hb, ?_⟩
  · grind
  · 
    refine subset_regionsOf_of_inter hU (isPreconnected_halfDisk _ _ _)
      (halfDisk_subset_freeOf_insert hc hw.1 (hb.trans hRA)) ⟨q, ⟨hqb, ?_⟩, hqU⟩
    simp only [mem_ofPred_eq]
    rcases lt_or_gt_of_ne hq2 with hlt | hlt
    · rw [ite_eq_right (not_lt.2 hlt.le)]; linarith
    simp_all

/-- **Exact splitting.**  Adding a chord `c ∉ S` to a submap `S ⊆ chords P` replaces the region
`R` of `S` containing the interior of `c` by exactly two regions `R₁ ≠ R₂` with
`R₁ ∪ R₂ = R \ c`, and leaves every other region unchanged. -/
theorem regionsOf_insert :
    ∃ R ∈ regionsOf P S, c \ P.boundary ⊆ R ∧ ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ R₁ ∪ R₂ = R \ c ∧
      R₁ ∈ regionsOf P (insert c S) ∧ R₂ ∈ regionsOf P (insert c S) ∧
      regionsOf P (insert c S) = (regionsOf P S \ {R}) ∪ {R₁, R₂} := by
  have hS' : insert c S ⊆ chords P := insert_subset hc hS
  obtain ⟨z₀, hz₀⟩ := (chord_sdiff_nonempty_isPreconnected hP hc).1
  set A := freeOf P S with hA
  set A' := freeOf P (insert c S) with hA'
  set R := connectedComponentIn A z₀ with hR
  have hA'A : A' ⊆ A := freeOf_anti P (subset_insert c S)
  have hA'eq : A' = A \ c := freeOf_insert P c S
  have hz₀A : z₀ ∈ A := chord_sdiff_subset_freeOf hP hS hc hcS hz₀
  have hRmem : R ∈ regionsOf P S := mem_regionsOf hz₀A
  have hcR : c \ P.boundary ⊆ R :=
    (chord_sdiff_nonempty_isPreconnected hP hc).2.subset_connectedComponentIn hz₀
      (chord_sdiff_subset_freeOf hP hS hc hcS)
  have hRopen : IsOpen R := (isOpen_freeOf hP hS).connectedComponentIn
  have hRA : R ⊆ A := connectedComponentIn_subset _ _
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.1 hRopen z₀ (hcR hz₀)
  -- the two candidate regions
  let pt : ℝ → Point := fun τ => (z₀.1, z₀.2 + τ * (r₀ / 2))
  have hpt : ∀ τ, (τ = 1 ∨ τ = -1) → pt τ ∈ halfDisk z₀ r₀ τ := fun τ hτ =>
    vert_mem_halfDisk hτ (half_pos hr₀) (by linarith)
  have hhalf : ∀ τ, halfDisk z₀ r₀ τ ⊆ A' := fun τ =>
    halfDisk_subset_freeOf_insert hc hz₀.1 (hb₀.trans hRA)
  have hptA' : ∀ τ, (τ = 1 ∨ τ = -1) → pt τ ∈ A' := fun τ hτ => hhalf τ (hpt τ hτ)
  have hRτ : ∀ τ, (τ = 1 ∨ τ = -1) → connectedComponentIn A' (pt τ) ∈ regionsOf P (insert c S) :=
    fun τ hτ => mem_regionsOf (hptA' τ hτ)
  have hhalfR : ∀ τ, (τ = 1 ∨ τ = -1) → halfDisk z₀ r₀ τ ⊆ connectedComponentIn A' (pt τ) :=
    fun τ hτ => (isPreconnected_halfDisk _ _ _).subset_connectedComponentIn (hpt τ hτ) (hhalf τ)
  -- components of `A'` inside `R`
  have hsubR : ∀ p ∈ A', p ∈ R → connectedComponentIn A' p ⊆ R := by
    intro p hp hpR
    rw [hR, connectedComponentIn_eq hpR]
    exact connectedComponentIn_mono p hA'A
  have hRτR : ∀ τ, (τ = 1 ∨ τ = -1) → connectedComponentIn A' (pt τ) ⊆ R := fun τ hτ =>
    hsubR _ (hptA' τ hτ) (hb₀ (halfDisk_subset_ball _ _ _ (hpt τ hτ)))
  -- every region of `insert c S` meeting `R` is one of the two
  have hcases : ∀ U ∈ regionsOf P (insert c S), (U ∩ R).Nonempty →
      U = connectedComponentIn A' (pt 1) ∨ U = connectedComponentIn A' (pt (-1)) := by
    intro U hU ⟨u, huU, huR⟩
    obtain ⟨w, hw, r, hr, τ, hτ, hb, hsub⟩ :=
      exists_halfDisk_subset hP hS hc hcS hz₀ hU huU huR
    have hall := halfDisk_all hP hc hRopen hcR hRA hU hτ ⟨w, hw, r, hr, hb, hsub⟩ z₀ hz₀ r₀ hr₀ hb₀
    have hptU : pt τ ∈ U := hall (hpt τ hτ)
    have hUeq : U = connectedComponentIn A' (pt τ) := regionsOf_eq_component hU hptU
    rcases hτ with rfl | rfl
    · grind
    grind
  -- the two regions differ
  have hne : connectedComponentIn A' (pt 1) ≠ connectedComponentIn A' (pt (-1)) := by
    obtain ⟨ε₀, hε₀, hsep⟩ :=
      chord_separates hP hS' (mem_insert c S) hz₀.1 hz₀.2
    set ε := min ε₀ r₀ / 2 with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε < ε₀ := by rw [hε]; linarith [min_le_left ε₀ r₀]
    have hε2 : ε < r₀ := by rw [hε]; linarith [min_le_right ε₀ r₀]
    obtain ⟨-, -, hdiff⟩ := hsep ε hε0 hε1
    intro heq
    apply hdiff
    have h1 : ((z₀.1, z₀.2 + ε) : Point) ∈ connectedComponentIn A' (pt 1) := by
      apply hhalfR 1 (Or.inl rfl)
      have := vert_mem_halfDisk (Or.inl rfl) hε0 hε2 (w := z₀)
      grind
    have h2 : ((z₀.1, z₀.2 - ε) : Point) ∈ connectedComponentIn A' (pt (-1)) := by
      apply hhalfR (-1) (Or.inr rfl)
      have := vert_mem_halfDisk (Or.inr rfl) hε0 hε2 (w := z₀)
      grind
    calc connectedComponentIn (freeOf P (insert c S)) (z₀.1, z₀.2 + ε)
        = connectedComponentIn A' (pt 1) := (connectedComponentIn_eq h1).symm
      _ = connectedComponentIn A' (pt (-1)) := heq
      _ = connectedComponentIn (freeOf P (insert c S)) (z₀.1, z₀.2 - ε) :=
          connectedComponentIn_eq h2
  -- other regions are unchanged
  have hother : ∀ U ∈ regionsOf P S, U ≠ R → U ∈ regionsOf P (insert c S) := by
    intro U hU hUR
    rcases id hU with ⟨u, hu, rfl⟩
    have hdisj : Disjoint (connectedComponentIn A u) R := regionsOf_disjoint_of_ne hU hRmem hUR
    have hUA' : connectedComponentIn A u ⊆ A' := by
      intro p hp
      rw [hA'eq]
      refine ⟨connectedComponentIn_subset _ _ hp, fun hpc => ?_⟩
      have hpR : p ∈ R := hcR ⟨hpc, (connectedComponentIn_subset _ _ hp).1.2⟩
      exact hdisj.notMem_of_mem_left hp hpR
    have huA' : u ∈ A' := hUA' (mem_connectedComponentIn hu)
    refine ⟨u, huA', ?_⟩
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hu) hUA'
    · exact connectedComponentIn_mono u hA'A
  refine ⟨R, hRmem, hcR, connectedComponentIn A' (pt 1), connectedComponentIn A' (pt (-1)), hne,
    ?_, hRτ 1 (Or.inl rfl), hRτ (-1) (Or.inr rfl), ?_⟩
  · apply Subset.antisymm
    · rintro p (hp | hp)
      · exact ⟨hRτR 1 (Or.inl rfl) hp, ((hA'eq ▸ connectedComponentIn_subset _ _ hp) : p ∈ A \ c).2⟩
      · exact ⟨hRτR (-1) (Or.inr rfl) hp,
          ((hA'eq ▸ connectedComponentIn_subset _ _ hp) : p ∈ A \ c).2⟩
    · rintro p ⟨hpR, hpc⟩
      have hpA' : p ∈ A' := by grind
      rcases hcases _ (mem_regionsOf hpA') ⟨p, mem_connectedComponentIn hpA', hpR⟩ with h | h
      · exact Or.inl (h ▸ mem_connectedComponentIn hpA')
      · exact Or.inr (h ▸ mem_connectedComponentIn hpA')
  · ext U
    simp only [mem_union, Set.mem_sdiff, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro hU
      obtain ⟨u, hu, rfl⟩ := hU
      have huA : u ∈ A := hA'A hu
      by_cases huR : u ∈ R
      · exact Or.inr (hcases _ (mem_regionsOf hu) ⟨u, mem_connectedComponentIn hu, huR⟩)
      · left
        have hUmem : connectedComponentIn A u ∈ regionsOf P S := mem_regionsOf huA
        have hUR : connectedComponentIn A u ≠ R := by
          intro h; exact huR (h ▸ mem_connectedComponentIn huA)
        obtain ⟨u', hu', heq⟩ := hother _ hUmem hUR
        have hu'' : u ∈ connectedComponentIn A' u' := heq ▸ mem_connectedComponentIn huA
        rw [connectedComponentIn_eq hu''] at heq
        grind
    · rintro (⟨hU, hUR⟩ | rfl | rfl)
      · grind
      · exact hRτ 1 (Or.inl rfl)
      grind

/-! ### Counting regions -/

/-- The region `R` split by `regionsOf_insert` is not one of the two new regions, and the two
new regions are not old regions other than `R`: bookkeeping for the count. -/
theorem ncard_regionsOf_insert
    (hfin : (regionsOf P S).Finite) :
    (regionsOf P (insert c S)).Finite ∧
      (regionsOf P (insert c S)).ncard = (regionsOf P S).ncard + 1 := by
  obtain ⟨R, hR, -, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := regionsOf_insert hP hS hc hcS
  have hnew : ∀ U, U ∈ regionsOf P (insert c S) → U ⊆ R → U ∉ regionsOf P S \ {R} := by
    rintro U hU hUR ⟨hUS, hUne⟩
    rw [mem_singleton_iff] at hUne
    obtain ⟨p, hp⟩ := regionsOf_nonempty hU
    exact (regionsOf_disjoint_of_ne hUS hR hUne).notMem_of_mem_left hp (hUR hp)
  have hR₁R : R₁ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inl hp
    grind
  have hR₂R : R₂ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inr hp
    grind
  have hdisj : Disjoint (regionsOf P S \ {R}) {R₁, R₂} := by
    grind
  rw [heq]
  refine ⟨hfin.sdiff.union (toFinite _), ?_⟩
  rw [ncard_union_eq hdisj hfin.sdiff (toFinite _), ncard_pair hne,
    ← ncard_sdiff_singleton_add_one hR hfin]


end

section
variable {P : Polygon} (hP : P.Simple) {S : Set (Set Point)} (hS : S ⊆ chords P)
include hP hS
/-- **Region count.**  A submap with `k` chords has exactly `k + 1` regions (and finitely
many). -/
theorem regionsOf_finite_ncard :
    (regionsOf P S).Finite ∧ (regionsOf P S).ncard = S.ncard + 1 := by
  have hfin : S.Finite := (chords_finite P).subset hS
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    rw [regionsOf_empty hP]
    simp
  | @insert c S hcS hSfin ih =>
    have hS' : S ⊆ chords P := (subset_insert c S).trans hS
    have hc : c ∈ chords P := hS (mem_insert c S)
    obtain ⟨hfin', hcard⟩ := ih hS'
    obtain ⟨hfin'', hcard''⟩ := ncard_regionsOf_insert hP hS' hc hcS hfin'
    simp_all

/-- A submap with `k` chords has exactly `k + 1` regions. -/
theorem ncard_regionsOf : (regionsOf P S).ncard = S.ncard + 1 :=
  (regionsOf_finite_ncard hP hS).2

/-- The regions of a submap form a finite set. -/
theorem regionsOf_finite : (regionsOf P S).Finite :=
  (regionsOf_finite_ncard hP hS).1


end

section
variable {P : Polygon} (hP : P.Simple)
include hP
/-- **The visibility map of a simple polygon has exactly one more region than it has chords.** -/
theorem regions_ncard :
    (regions P).ncard = (chords P).ncard + 1 :=
  ncard_regionsOf hP (subset_refl _)

/-- The visibility map has at most `2 n + 1` regions. -/
theorem regions_ncard_le : (regions P).ncard ≤ 2 * P.n + 1 := by
  rw [regions_ncard hP]
  exact Nat.add_le_add_right (chords_ncard_le P) 1

/-- The regions of the visibility map form a finite set. -/
theorem regions_finite : (regions P).Finite :=
  regionsOf_finite hP (subset_refl _)


end

end

end Chazelle.Visibility
