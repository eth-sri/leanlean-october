module

public import Chazelle.Chain.Submap
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Chazelle.RewriteTactics

/-!
# The dual graph of a submap of a chord system is a tree

Domain-parametrised version of the first part of `Chazelle/Visibility/DualTree.lean` (up to
`dual_isTree`), for a `ChordSystem D F`.  For a submap `S ⊆ F` the *dual graph* has the regions
of `S` as vertices, two distinct regions being adjacent when some chord of `S` *touches* both
(`TouchesIn D c U`: a point of `c ∩ D` lies in the closure of `U`).

* `ChordSystem.touches_iff`: every chord of `S` touches exactly two regions of `S`;
* `ChordSystem.dualGraph_reachable`: the dual graph is connected (induction on `S`);
* `ChordSystem.dual_isTree`: for a connected nonempty domain the dual graph on the regions
  (`dualTreeIn D S`) is a tree (Chazelle's Lemma 2.2, tree part);
* `ChordSystem.dualTree_card_edgeSet`: it has exactly `S.ncard` edges.

The chain instance is at the end (`Chain.dual_isTree`).  The contraction part of the interior
file (`SameRegion`, `sameRegion_iff_reflTransGen`) is not ported here.
-/

namespace Chazelle.Chain

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan

variable {D : Set Point} {F : Set (Set Point)}

/-! ### Touching -/

/-- A chord `c` *touches* a set `U`: some interior point of `c` lies in the closure of `U`. -/
def TouchesIn (D : Set Point) (c U : Set Point) : Prop := ∃ z ∈ c ∩ D, z ∈ closure U

/-- The centre of a half-disk is in its closure. -/
theorem mem_closure_halfDisk {w : Point} {r τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (hr : 0 < r) :
    w ∈ closure (halfDisk w r τ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set s := min ε r / 2 with hs
  have hs0 : 0 < s := by rw [hs]; exact half_pos (lt_min hε hr)
  have hsε : s < ε := by rw [hs]; linarith [min_le_left ε r]
  have hsr : s < r := by rw [hs]; linarith [min_le_right ε r]
  refine ⟨(w.1, w.2 + τ * s), vert_mem_halfDisk hτ hs0 hsr, ?_⟩
  rw [dist_comm, dist_eq_norm, Prod.norm_def]
  simp [Geometry.sub_fst, Geometry.sub_snd, sub_self, norm_zero, add_sub_cancel_left,
    Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
  rcases hτ with rfl | rfl <;> simp [hsε, hε]

/-- Both regions produced by splitting along `c` are touched by `c`. -/
theorem ChordSystem.touches_of_subset_split (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) {R : Set Point}
    (hR : R ∈ regionsIn D S) (hcR : c ∩ D ⊆ R) {U : Set Point}
    (hU : U ∈ regionsIn D (insert c S)) (hUR : U ⊆ R) : TouchesIn D c U := by
  obtain ⟨z₀, hz₀⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
  obtain ⟨u, hu⟩ := regionsIn_nonempty hU
  have hReq  := regionsIn_eq_component hR (hcR hz₀)
  have huR  := hReq ▸ hUR hu
  obtain ⟨w, hw, r, hr, τ, hτ, -, hsub⟩ := hF.exists_halfDisk_subset hS hc hcS hz₀ hU hu huR
  exact ⟨w, hw, closure_mono hsub (mem_closure_halfDisk hτ hr)⟩

/-- **A chord touches exactly the two regions it separates.**  With the data of
`regionsIn_insert`, a region of `insert c S` is touched by `c` iff it is `R₁` or `R₂`. -/
theorem ChordSystem.touches_iff_of_split (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) {R : Set Point}
    (hR : R ∈ regionsIn D S) (hcR : c ∩ D ⊆ R) {R₁ R₂ : Set Point}
    (hunion : R₁ ∪ R₂ = R \ c) (hR₁ : R₁ ∈ regionsIn D (insert c S))
    (hR₂ : R₂ ∈ regionsIn D (insert c S))
    (heq : regionsIn D (insert c S) = (regionsIn D S \ {R}) ∪ {R₁, R₂}) :
    ∀ W ∈ regionsIn D (insert c S), TouchesIn D c W ↔ W = R₁ ∨ W = R₂ := by
  have hR₁R : R₁ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inl hp
    rw [hunion] at this
    exact this.1
  have hR₂R : R₂ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inr hp
    rw [hunion] at this
    exact this.1
  intro W hW
  constructor
  · rintro ⟨z, hz, hzW⟩
    by_contra hnot
    push Not at hnot
    have hW' : W ∈ regionsIn D S \ {R} := by
      rw [heq] at hW
      rcases hW with h | h
      · exact h
      · simp [mem_insert_iff, mem_singleton_iff] at h
        rcases h with rfl | rfl
        · exact absurd rfl hnot.1
        · exact absurd rfl hnot.2
    rw [Set.mem_sdiff, mem_singleton_iff] at hW'
    have hdisj  := (regionsIn_disjoint_of_ne hW'.1 hR hW'.2).closure_left (hF.regionsIn_open hS hR)
    exact hdisj.notMem_of_mem_left hzW (hcR hz)
  · rintro (rfl | rfl)
    · exact hF.touches_of_subset_split hS hc hcS hR hcR hR₁ hR₁R
    · exact hF.touches_of_subset_split hS hc hcS hR hcR hR₂ hR₂R

/-- Every chord of a submap touches exactly two regions of it, and they are distinct. -/
theorem ChordSystem.touches_iff (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) :
    ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ ∀ W ∈ regionsIn D S, TouchesIn D c W ↔ W = R₁ ∨ W = R₂ := by
  have hS' : S \ {c} ⊆ F := fun _ h => hS h.1
  have hcS' : c ∉ S \ {c} := fun h => h.2 rfl
  have hins : insert c (S \ {c}) = S := insert_sdiff_singleton.trans (insert_eq_of_mem hc)
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ :=
    hF.regionsIn_insert hS' (hS hc) hcS'
  refine ⟨R₁, R₂, hne, ?_⟩
  have := hF.touches_iff_of_split hS' (hS hc) hcS' hR hcR hunion hR₁ hR₂ heq
  rwa [hins] at this

/-- If a chord `c' ≠ c` touches `R` and `R₁ ∪ R₂ = R \ c`, then it touches `R₁` or `R₂`. -/
theorem ChordSystem.touches_split_or (hF : ChordSystem D F) {c c' : Set Point} (hc : c ∈ F)
    (hc' : c' ∈ F) (hne : c ≠ c') {R R₁ R₂ : Set Point} (hunion : R₁ ∪ R₂ = R \ c)
    (h : TouchesIn D c' R) : TouchesIn D c' R₁ ∨ TouchesIn D c' R₂ := by
  obtain ⟨z, hz, hzR⟩ := h
  have hsub : R ⊆ R₁ ∪ R₂ ∪ c := by
    intro p hp
    by_cases hpc : p ∈ c
    · exact Or.inr hpc
    · left
      rw [hunion]
      exact ⟨hp, hpc⟩
  have hcl : closure R ⊆ closure R₁ ∪ closure R₂ ∪ c := by
    refine (closure_mono hsub).trans ?_
    rw [closure_union, closure_union, (hF.isClosed_chord hc).closure_eq]
  rcases hcl hzR with (h1 | h2) | h3
  · exact Or.inl ⟨z, hz, h1⟩
  · exact Or.inr ⟨z, hz, h2⟩
  · exact absurd hz.2 (hF.inter_subset_compl hc hc' hne ⟨h3, hz.1⟩)

/-! ### The dual graph -/

/-- Adjacency of the dual graph of `S`: two distinct regions of `S` touched by a common chord
of `S`. -/
def DualAdjIn (D : Set Point) (S : Set (Set Point)) (U V : Set Point) : Prop :=
  U ∈ regionsIn D S ∧ V ∈ regionsIn D S ∧ U ≠ V ∧ ∃ c ∈ S, TouchesIn D c U ∧ TouchesIn D c V

theorem DualAdjIn.symm {S : Set (Set Point)} {U V : Set Point} (h : DualAdjIn D S U V) :
    DualAdjIn D S V U := by
  obtain ⟨hU, hV, hne, c, hc, h1, h2⟩ := h
  exact ⟨hV, hU, hne.symm, c, hc, h2, h1⟩

/-- The dual graph of the submap `S`, on the ambient type `Set Point`: vertices outside
`regionsIn D S` are isolated. -/
def dualGraphIn (D : Set Point) (S : Set (Set Point)) : SimpleGraph (Set Point) where
  Adj := DualAdjIn D S
  symm := ⟨fun _ _ (h : DualAdjIn D S _ _) => h.symm⟩
  loopless := ⟨fun _ (h : DualAdjIn D S _ _) => h.2.2.1 rfl⟩

/-- The dual graph on the regions of `S`: the induced subgraph of `dualGraphIn D S` on
`regionsIn D S`. -/
abbrev dualTreeIn (D : Set Point) (S : Set (Set Point)) : SimpleGraph (regionsIn D S) :=
  (dualGraphIn D S).induce (regionsIn D S)

/-- The two regions touched by a chord are adjacent in the dual graph. -/
theorem dualGraphIn_adj_of_touches {S : Set (Set Point)} {c : Set Point} (hc : c ∈ S)
    {U V : Set Point} (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S) (hne : U ≠ V)
    (h1 : TouchesIn D c U) (h2 : TouchesIn D c V) : (dualGraphIn D S).Adj U V :=
  ⟨hU, hV, hne, c, hc, h1, h2⟩

/-! ### Connectivity -/

/-- The inductive step of connectivity: if the dual graph of `S` is connected on its regions,
so is the dual graph of `insert c S`. -/
theorem ChordSystem.dualGraph_reachable_insert (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S)
    (ih : ∀ U ∈ regionsIn D S, ∀ V ∈ regionsIn D S, (dualGraphIn D S).Reachable U V) :
    ∀ U ∈ regionsIn D (insert c S), ∀ V ∈ regionsIn D (insert c S),
      (dualGraphIn D (insert c S)).Reachable U V := by
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hF.regionsIn_insert hS hc hcS
  have htouch := hF.touches_iff_of_split hS hc hcS hR hcR hunion hR₁ hR₂ heq
  set G' := dualGraphIn D (insert c S) with hG'
  have hR₁R : R₁ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inl hp
    rw [hunion] at this
    exact this.1
  have hR₂R : R₂ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inr hp
    rw [hunion] at this
    exact this.1
  have hadj12  := dualGraphIn_adj_of_touches (mem_insert c S) hR₁ hR₂ hne ((htouch R₁ hR₁).2 (Or.inl rfl))
      ((htouch R₂ hR₂).2 (Or.inr rfl))
  -- old regions other than `R` differ from the two new ones
  have hnotR : ∀ V ∈ regionsIn D S, V ≠ R → V ≠ R₁ ∧ V ≠ R₂ := by
    intro V hV hVR
    have hdisj := regionsIn_disjoint_of_ne hV hR hVR
    constructor
    · rintro rfl
      obtain ⟨p, hp⟩ := regionsIn_nonempty hR₁
      exact hdisj.notMem_of_mem_left hp (hR₁R hp)
    · rintro rfl
      obtain ⟨p, hp⟩ := regionsIn_nonempty hR₂
      exact hdisj.notMem_of_mem_left hp (hR₂R hp)
  have hold : ∀ V ∈ regionsIn D S, V ≠ R → V ∈ regionsIn D (insert c S) := by
    intro V hV hVR
    rw [heq]
    exact Or.inl ⟨hV, hVR⟩
  -- the map from old regions to new regions
  let φ : Set Point → Set Point := fun U => if U = R then R₁ else U
  have hφR : φ R = R₁ := by simp [φ]
  have hφ : ∀ U, U ≠ R → φ U = U := fun U h => by simp [φ, h]
  -- an old edge at `R` becomes an edge at `R₁` or `R₂`
  have hedgeR : ∀ V ∈ regionsIn D S, V ≠ R → ∀ c' ∈ S, TouchesIn D c' R → TouchesIn D c' V →
      G'.Reachable R₁ V := by
    intro V hV hVR c' hc' hR' hV'
    have hV''  := hold V hV hVR
    have hne' := hnotR V hV hVR
    have hcc' : c ≠ c' := fun h => hcS (h ▸ hc')
    rcases hF.touches_split_or hc (hS hc') hcc' hunion hR' with h1 | h2
    · exact (dualGraphIn_adj_of_touches (mem_insert_of_mem c hc') hR₁ hV'' hne'.1.symm h1
        hV').reachable
    · exact hadj12.reachable.trans
        (dualGraphIn_adj_of_touches (mem_insert_of_mem c hc') hR₂ hV'' hne'.2.symm h2 hV').reachable
  have hlift : ∀ U V, (dualGraphIn D S).Adj U V → G'.Reachable (φ U) (φ V) := by
    intro U V hUV
    obtain ⟨hU, hV, hUV', c', hc', hU', hV'⟩ := hUV
    by_cases hUR : U = R
    · subst hUR
      have hVR  := Ne.symm hUV'
      rw [hφR, hφ V hVR]
      exact hedgeR V hV hVR c' hc' hU' hV'
    · by_cases hVR : V = R
      · subst hVR
        rw [hφR, hφ U hUR]
        exact (hedgeR U hU hUR c' hc' hV' hU').symm
      · rw [hφ U hUR, hφ V hVR]
        exact (dualGraphIn_adj_of_touches (mem_insert_of_mem c hc') (hold U hU hUR) (hold V hV hVR)
          hUV' hU' hV').reachable
  have hreach : ∀ U V, (dualGraphIn D S).Reachable U V → G'.Reachable (φ U) (φ V) := by
    intro U V h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hab ih' => exact ih'.trans (hlift _ _ hab)
  -- every new region reaches `R₁`
  have hcover : ∀ U ∈ regionsIn D (insert c S), G'.Reachable U R₁ := by
    intro U hU
    rw [heq] at hU
    rcases hU with ⟨hU, hUR⟩ | hU
    · rw [mem_singleton_iff] at hUR
      have := hreach U R (ih U hU R hR)
      rwa [hφ U hUR, hφR] at this
    · simp [mem_insert_iff, mem_singleton_iff] at hU
      rcases hU with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact hadj12.reachable.symm
  intro U hU V hV
  exact (hcover U hU).trans (hcover V hV).symm

/-- **The dual graph is connected**: any two regions of a submap are joined by a walk. -/
theorem ChordSystem.dualGraph_reachable (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) :
    ∀ U ∈ regionsIn D S, ∀ V ∈ regionsIn D S, (dualGraphIn D S).Reachable U V := by
  have hfin  := hF.finite.subset hS
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    intro U hU V hV
    rw [regionsIn_empty hD hne, mem_singleton_iff] at hU hV
    rw [hU, hV]
  | @insert c S hcS hSfin ih =>
    have hS'  := (subset_insert c S).trans hS
    exact hF.dualGraph_reachable_insert hS' (hS (mem_insert c S)) hcS (ih hS')

/-- The regions of a submap form a nonempty set. -/
theorem ChordSystem.regionsIn_nonempty_set (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) : (regionsIn D S).Nonempty :=
  nonempty_of_ncard_ne_zero (by rwo [hF.ncard_regionsIn hD hne hS])

/-- The dual graph on the regions is connected. -/
theorem ChordSystem.dualTree_connected (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) : (dualTreeIn D S).Connected := by
  have : Nonempty (regionsIn D S) := (hF.regionsIn_nonempty_set hD hne hS).to_subtype
  refine ⟨fun u v => ?_⟩
  have h := hF.dualGraph_reachable hD hne hS u u.2 v v.2
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  have key : ∀ W (_ : Relation.ReflTransGen (dualGraphIn D S).Adj u W),
      ∀ hW : W ∈ regionsIn D S, (dualTreeIn D S).Reachable u ⟨W, hW⟩ := by
    intro W h
    induction h with
    | refl => intro hW; exact SimpleGraph.Reachable.refl _
    | @tail W V _ hWV ih =>
      intro hV
      have hW : W ∈ regionsIn D S := hWV.1
      have hadj : (dualTreeIn D S).Adj ⟨W, hW⟩ ⟨V, hV⟩ := hWV
      exact (ih hW).trans hadj.reachable
  exact key v h v.2

/-! ### Counting edges -/

open Classical in
/-- The edge of the dual graph contributed by a chord `c ∈ S`: the (unordered) pair of the two
regions it touches.  (Junk value for a chord touching fewer or more regions.) -/
noncomputable def edgeOfIn (D : Set Point) (S : Set (Set Point)) (c : Set Point) :
    Sym2 (Set Point) :=
  if h : ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ ∀ W ∈ regionsIn D S, TouchesIn D c W ↔ W = R₁ ∨ W = R₂
  then s(Classical.choose h, Classical.choose (Classical.choose_spec h))
  else s(∅, ∅)

/-- Every edge of the dual graph is the edge of one of its chords. -/
theorem ChordSystem.edge_eq_edgeOf (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {U V : Set Point} (hUV : (dualGraphIn D S).Adj U V) : ∃ c ∈ S, s(U, V) = edgeOfIn D S c := by
  obtain ⟨hU, hV, hne, c, hc, hU', hV'⟩ := hUV
  refine ⟨c, hc, ?_⟩
  have h := hF.touches_iff hS hc
  unfold edgeOfIn
  rw [dite_eq_left h]
  obtain ⟨hne', hspec⟩ := Classical.choose_spec (Classical.choose_spec h)
  rcases (hspec U hU).1 hU' with rfl | rfl <;> rcases (hspec V hV).1 hV' with rfl | rfl
  · exact absurd rfl hne
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hne

/-- The edge set of the dual graph is contained in the image of `S` under `edgeOf`. -/
theorem ChordSystem.dualGraph_edgeSet_subset (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) : (dualGraphIn D S).edgeSet ⊆ edgeOfIn D S '' S := by
  intro e he
  induction e using Sym2.ind with
  | h U V =>
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨c, hc, heq⟩ := hF.edge_eq_edgeOf hS he
    exact ⟨c, hc, heq.symm⟩

/-- The dual graph has at most `S.ncard` edges. -/
theorem ChordSystem.dualGraph_card_edgeSet_le (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) : Nat.card (dualGraphIn D S).edgeSet ≤ S.ncard := by
  have hfin  := hF.finite.subset hS
  rw [Nat.card_coe_set_eq]
  calc (dualGraphIn D S).edgeSet.ncard
      ≤ (edgeOfIn D S '' S).ncard := ncard_le_ncard (hF.dualGraph_edgeSet_subset hS) (hfin.image _)
    _ ≤ S.ncard := ncard_image_le hfin

/-- The dual graph on the regions has at most `S.ncard` edges. -/
theorem ChordSystem.dualTree_card_edgeSet_le (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) : Nat.card (dualTreeIn D S).edgeSet ≤ S.ncard := by
  have hfin  := hF.finite.subset hS
  have : Finite (dualGraphIn D S).edgeSet :=
    ((hfin.image _).subset (hF.dualGraph_edgeSet_subset hS)).to_subtype
  calc Nat.card (dualTreeIn D S).edgeSet
      ≤ Nat.card (dualGraphIn D S).edgeSet :=
        Nat.card_le_card_of_injective _
          (SimpleGraph.Embedding.mapEdgeSet (SimpleGraph.Embedding.induce (regionsIn D S))).injective
    _ ≤ S.ncard := hF.dualGraph_card_edgeSet_le hS

/-! ### The tree -/

/-- **The dual graph of a submap is a tree** (Chazelle's Lemma 2.2, interior version): the graph
on the regions of `S ⊆ chords P` in which two regions are adjacent when a chord of `S` touches
both is connected and acyclic. -/
theorem ChordSystem.dual_isTree (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) :
    (dualTreeIn D S).IsTree := by
  have : Finite (regionsIn D S) := (hF.regionsIn_finite hD hne hS).to_subtype
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hconn := hF.dualTree_connected hD hne hS
  refine ⟨hconn, ?_⟩
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have h2 := hF.dualTree_card_edgeSet_le hS
  have h3 : Nat.card (regionsIn D S) = S.ncard + 1 := by
    rw [Nat.card_coe_set_eq, hF.ncard_regionsIn hD hne hS]
  omega

/-- The dual tree has exactly `S.ncard` edges. -/
theorem ChordSystem.dualTree_card_edgeSet (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) : Nat.card (dualTreeIn D S).edgeSet = S.ncard := by
  have : Finite (regionsIn D S) := (hF.regionsIn_finite hD hne hS).to_subtype
  have h1 := (hF.dualTree_connected hD hne hS).card_vert_le_card_edgeSet_add_one
  have h2 := hF.dualTree_card_edgeSet_le hS
  have h3 : Nat.card (regionsIn D S) = S.ncard + 1 := by
    rw [Nat.card_coe_set_eq, hF.ncard_regionsIn hD hne hS]
  omega

/-! ### The chain instance -/

variable (C : Chain)

end

end Chazelle.Chain
