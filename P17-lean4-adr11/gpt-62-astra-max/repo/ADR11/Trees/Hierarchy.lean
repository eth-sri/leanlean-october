module
public import ADR11.Basic
public import ADR11.Coalescent.Forest

/-! A clade is determined by rooted triples: take its least containing
cluster and choose two leaves spanning different children. -/
@[expose] public section
namespace ADR11
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X] {H : Clusters X}

theorem mem_childClusters {H : Clusters X} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem child_mem {A B : Finset X} (hb : B ∈ childClusters H A) : B ∈ H := (mem_childClusters.mp hb).1

theorem child_lt {A B : Finset X} (hb : B ∈ childClusters H A) : B ⊂ A := (mem_childClusters.mp hb).2.1

theorem kids_roots (H : Clusters X) (A : Finset X) : childClusters H A = roots (H.filter (· ⊂ A)) := by
  ext B; simp [mem_childClusters,mem_roots,Finset.ssubset_iff_subset_ne]; grind

/-- Every proper subclade lies in a maximal proper subclade. -/
theorem subset_child {A E : Finset X} (he : E ∈ H) (hlt : E ⊂ A) : ∃ B ∈ childClusters H A, E ⊆ B := by
  rw [kids_roots]; exact exists_mem_roots_subset (mem_filter.mpr ⟨he,hlt⟩)

namespace SpeciesTree
variable (σ : SpeciesTree X)
def internal := σ.clusters.filter fun A => 2 ≤ #A ∧ A ≠ univ

theorem complete_internal : σ.clusters = hierarchyOf σ.internal := by
  ext A; simp only [hierarchyOf,internal,mem_insert,mem_union,mem_filter,mem_image,mem_univ,true_and]
  constructor
  · intro h; have := (σ.nonempty_of_mem _ h).card_pos
    grind [Finset.card_eq_one]
  · rintro (rfl | ⟨h,-⟩ | ⟨x,rfl⟩); exacts [σ.univ_mem,h,σ.singleton_mem x]

abbrev kids := childClusters σ.clusters

@[elab_as_elim] theorem cladeInduction {P : Finset X → Prop} (A) (step : ∀ A, (∀ B ∈ σ.kids A, P B) → P A) : P A :=
  Finset.strongInductionOn A fun A ih => step A fun B hb => ih B (child_lt hb)

/-- Sibling clades are disjoint since they are roots of a subforest. -/
theorem siblings {A B C : Finset X} (hb : B ∈ σ.kids A) (hc : C ∈ σ.kids A) (ne : B ≠ C) : Disjoint B C := by
  rw [kids,kids_roots] at hb hc; exact (σ.forest.filter _).disjoint_of_mem_roots hb hc ne

theorem nested {A B : Finset X} (ha : A ∈ σ.clusters) (hb : B ∈ σ.clusters) {x : X} (hx : x ∈ A) (hy : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  have := σ.laminar _ ha _ hb; grind [Finset.disjoint_left]

/-- No clade can lie between a child and its parent. -/
theorem cut {A B C : Finset X} (ha : A ∈ σ.clusters) (hb : B ∈ σ.kids A) (hc : C ∈ σ.clusters)
    {x : X} (hx : x ∈ B) (hy : x ∈ C) : C ⊆ B ∨ A ⊆ C := by
  obtain ⟨hm,lt,gap⟩ := mem_childClusters.mp hb
  have := σ.nested hm hc hx hy
  have := σ.nested ha hc (lt.subset hx) hy
  grind

/-- Clades through a fixed leaf form a chain. -/
theorem least_at {P : Finset X → Prop} [DecidablePred P] {x : X} (ex : ∃ A ∈ σ.clusters, P A)
    (through : ∀ A, P A → x ∈ A) : ∃ M ∈ σ.clusters, P M ∧ ∀ C ∈ σ.clusters, P C → M ⊆ C := by
  obtain ⟨M,hm,least⟩ := (σ.clusters.filter P).exists_min_image card (by simp_all [Finset.Nonempty])
  obtain ⟨hm,hp⟩ := mem_filter.mp hm; refine ⟨M,hm,hp,fun C hc p => ?_⟩
  rcases σ.nested hm hc (through M hp) (through C p) with h | h; exact h
  rw [eq_of_subset_of_card_le h (least C (mem_filter.mpr ⟨hc,p⟩))]

theorem span {A : Finset X} (hn : 2 ≤ #A) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ∀ C ∈ σ.clusters, x ∈ C → y ∈ C → A ⊆ C := by
  obtain ⟨x,hx⟩ : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨M,hm,sub,least⟩ := σ.least_at (P := (A ⊆ ·)) ⟨univ,σ.univ_mem,subset_univ _⟩ (fun _ h => h hx)
  obtain ⟨B,hb,hs⟩ := subset_child (σ.singleton_mem x) ((singleton_subset_iff.mpr (sub hx)).ssubset_of_ne (fun e => by have := hn.trans (card_le_card sub); simp [← e] at this))
  have hxB := singleton_subset_iff.mp hs
  obtain ⟨y,hy,hyB⟩ := not_subset.mp fun h => (child_lt hb).not_ge (least B (child_mem hb) h)
  exact ⟨x,hx,y,hy,fun e => hyB (e ▸ hxB),fun C hc hxC hyC => sub.trans ((σ.cut hm hb hc hxB hxC).resolve_left fun s => hyB (s hyC))⟩

end SpeciesTree

/-! ### Unrooted trees -/

section Unroot

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sides of the splits of the unrooted tree of `G`: the non-root clusters of `G` and their
complements. -/
theorem mem_unroot {G : Clusters L} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  simp [unroot,and_comm]

end Unroot


namespace SpeciesTree
/-- The two sides of a split have the same unrooted length. -/
theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  unfold unrootedLength
  refine Finset.sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
  aesop

end SpeciesTree

end ADR11
