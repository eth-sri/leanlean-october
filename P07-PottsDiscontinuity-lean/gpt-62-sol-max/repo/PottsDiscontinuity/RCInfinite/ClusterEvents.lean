module

public import PottsDiscontinuity.Duality.BondStates
public import PottsDiscontinuity.RCInfinite.TranslationSupport

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- The actual open cluster of a vertex, including the vertex itself. -/
def cluster (ω : LatticeConfiguration) (x : LatticeVertex) : Set LatticeVertex :=
  {y | (rcInfiniteOpenGraph ω).Reachable x y}

def infiniteAt (x : LatticeVertex) : Set LatticeConfiguration :=
  {ω | (cluster ω x).Infinite}

def infiniteClusterEvent : Set LatticeConfiguration :=
  {ω | ∃ x : LatticeVertex, ω ∈ infiniteAt x}

theorem rcInfiniteOpenGraph_adj (ω : LatticeConfiguration) (x y : LatticeVertex) :
    (rcInfiniteOpenGraph ω).Adj x y ↔
      ∃ h : s(x, y) ∈ squareLattice.edgeSet, ω ⟨s(x, y), h⟩ = true := by
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · exact And.left
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, hh⟩, (squareLattice.mem_edgeSet.mp h).ne⟩

theorem measurableSet_open_adj (x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Adj x y} := by
  by_cases h : squareLattice.Adj x y
  · have he := squareLattice.mem_edgeSet.mpr h
    have heq : {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Adj x y} =
        {ω | ω ⟨s(x, y), he⟩ = true} := by
      simp_all [rcInfiniteOpenGraph_adj]
    rw [heq]
    exact (isCylinder_coordinate _ true).measurableSet
  simp_all [rcInfiniteOpenGraph]

def openChain : ℕ → LatticeConfiguration → LatticeVertex → LatticeVertex → Prop
  | 0, _, x, y => x = y
  | n + 1, ω, x, y => ∃ z, (rcInfiniteOpenGraph ω).Adj x z ∧ openChain n ω z y

theorem openChain_reachable {n : ℕ} {ω : LatticeConfiguration} {x y : LatticeVertex}
    (h : openChain n ω x y) : (rcInfiniteOpenGraph ω).Reachable x y := by
  induction n generalizing x with
  | zero => exact h ▸ SimpleGraph.Reachable.refl x
  | succ n ih =>
    obtain ⟨z, hxz, hzy⟩ := h
    exact hxz.reachable.trans (ih hzy)

theorem reachable_iff_openChain (ω : LatticeConfiguration) (x y : LatticeVertex) :
    (rcInfiniteOpenGraph ω).Reachable x y ↔ ∃ n, openChain n ω x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => tauto
    | cons h w ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, _, h, hn⟩
  · rintro ⟨n, hn⟩
    exact openChain_reachable hn

theorem measurableSet_openChain (n : ℕ) (x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | openChain n ω x y} := by
  induction n generalizing x with
  | zero =>
    by_cases h : x = y <;> simp [openChain]
  | succ n ih =>
    have h := MeasurableSet.iUnion (fun z : LatticeVertex =>
      (measurableSet_open_adj x z).inter (ih z))
    convert h using 1
    ext ω
    simp [openChain]

theorem measurableSet_open_reachable (x y : LatticeVertex) :
    MeasurableSet {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable x y} := by
  have h := MeasurableSet.iUnion (fun n : ℕ => measurableSet_openChain n x y)
  convert h using 1
  ext ω
  simp [reachable_iff_openChain]

theorem infinite_cluster_iff (ω : LatticeConfiguration) (x : LatticeVertex) :
    (cluster ω x).Infinite ↔ ∀ F : Finset LatticeVertex,
      ∃ y, y ∉ F ∧ (rcInfiniteOpenGraph ω).Reachable x y := by
  constructor
  · intro h F
    obtain ⟨y, hy, hyF⟩ := h.exists_notMem_finset F
    tauto
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.mpr hy)

theorem measurableSet_infiniteAt (x : LatticeVertex) : MeasurableSet (infiniteAt x) := by
  have hinner (F : Finset LatticeVertex) : MeasurableSet
      (⋃ y : {y : LatticeVertex // y ∉ F},
        {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable x y.val}) :=
    MeasurableSet.iUnion fun y => measurableSet_open_reachable x y.val
  have h := MeasurableSet.iInter hinner
  convert h using 1
  ext ω
  simp only [infiniteAt, mem_ofPred_eq, infinite_cluster_iff, mem_iInter, mem_iUnion,
    Subtype.exists, exists_prop]

theorem measurableSet_infiniteClusterEvent : MeasurableSet infiniteClusterEvent := by
  have h := MeasurableSet.iUnion measurableSet_infiniteAt
  convert h using 1
  ext ω
  simp [infiniteClusterEvent]

section

variable (a : LatticeVertex) (ω : LatticeConfiguration)

theorem edgeTranslate_at_translatedEdge (e : Edge) :
    edgeTranslate a ω (translatedEdge a e) = ω e := by
  rw [latticeConfigurationTranslate_apply]
  congr 1
  apply Subtype.ext
  simp only [translatedEdge, SimpleGraph.Iso.mapEdgeSet_apply,
    SimpleGraph.Hom.mapEdgeSet_coe, Sym2.map_map]
  have hc : (latticeTranslate (-a)) ∘ (latticeTranslate a) = id :=
    funext (latticeTranslate_neg_cancel a)
  change Sym2.map ((latticeTranslate (-a)) ∘ (latticeTranslate a)) e.val = e.val
  rw [hc, Sym2.map_id]
  rfl

/-- The open graph translates as a graph, including all original vertices. -/
def openGraphTranslationIso :
    rcInfiniteOpenGraph ω ≃g rcInfiniteOpenGraph (edgeTranslate a ω) where
  toEquiv := (latticeTranslationIso a).toEquiv
  map_rel_iff' := by
    intro x y
    rw [rcInfiniteOpenGraph_adj, rcInfiniteOpenGraph_adj]
    by_cases h : squareLattice.Adj x y
    · have he : s(x, y) ∈ squareLattice.edgeSet := squareLattice.mem_edgeSet.mpr h
      have ht : s(latticeTranslate a x, latticeTranslate a y) ∈ squareLattice.edgeSet :=
        squareLattice.mem_edgeSet.mpr ((squareLattice_adj_translate_iff a x y).mpr h)
      have hstate : edgeTranslate a ω ⟨s(latticeTranslate a x, latticeTranslate a y), ht⟩ =
          ω ⟨s(x, y), he⟩ := edgeTranslate_at_translatedEdge a ω ⟨s(x, y), he⟩
      exact ⟨fun ⟨_, hh⟩ => ⟨he, hstate ▸ hh⟩,
        fun ⟨_, hh⟩ => ⟨ht, hstate.symm ▸ hh⟩⟩
    · have ht : ¬squareLattice.Adj (latticeTranslate a x) (latticeTranslate a y) :=
        fun hh => h ((squareLattice_adj_translate_iff a x y).mp hh)
      tauto

theorem cluster_translation (x : LatticeVertex) :
    cluster (edgeTranslate a ω) (latticeTranslate a x) = latticeTranslate a '' cluster ω x := by
  ext y
  obtain ⟨z, rfl⟩ := (latticeTranslationIso a).surjective y
  constructor
  · intro hz
    exact ⟨z, (openGraphTranslationIso a ω).reachable_iff.mp hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := (latticeTranslationIso a).injective hwz
    subst w
    exact (openGraphTranslationIso a ω).reachable_iff.mpr hw

theorem infiniteAt_translation (x : LatticeVertex) :
    edgeTranslate a ω ∈ infiniteAt (latticeTranslate a x) ↔ ω ∈ infiniteAt x := by
  change (cluster (edgeTranslate a ω) (latticeTranslate a x)).Infinite ↔ (cluster ω x).Infinite
  rw [cluster_translation]
  exact Set.infinite_image_iff (show Set.InjOn (latticeTranslate a) (cluster ω x) from
    (latticeTranslationIso a).injective.injOn)

end

theorem infiniteClusterEvent_eq_iUnion : infiniteClusterEvent = ⋃ x, infiniteAt x := by
  ext ω
  simp [infiniteClusterEvent]

theorem infiniteAt_preimage (a x : LatticeVertex) :
    (edgeTranslate a) ⁻¹' infiniteAt (latticeTranslate a x) = infiniteAt x := by
  ext ω
  exact infiniteAt_translation a ω x

end
end PottsDiscontinuity.RCInfinite
