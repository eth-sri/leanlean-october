module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*}

/-- The trace of a cluster on the retained taxa. -/
abbrev trace {α : Type*} (S : Finset α) [DecidablePred (· ∈ S)] (A : Finset α) := A.subtype (· ∈ S)

/-! ### Clusters with a common element are nested -/

namespace IsHierarchy

variable [Fintype X] {H : ClusterFamily X}

/-- Two clusters of a hierarchy with a common element are nested. -/
theorem subset_or_subset_of_mem (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H)
    {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  have := hH.2.2.2 A hA B hB
  grind [disjoint_left]

variable [DecidableEq X]

/-- A cluster strictly contained in `A` that meets a child `B` of `A` is contained in `B`. -/
theorem subset_of_mem_childClusters (hH : IsHierarchy H) {A B C : Finset X}
    (hB : B ∈ childClusters H A) (hC : C ∈ H) (hCA : C ⊂ A) (hBC : ¬ Disjoint B C) : C ⊆ B := by
  have := hH.2.2.2 B (child_mem hB) C hC
  grind [mem_childClusters]

/-- A pair spanning `A`: no proper subcluster contains both. -/
theorem exists_spanning_pair (hH : IsHierarchy H) {A : Finset X} (h₂ : 2 ≤ #A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∀ C ∈ H, C ⊂ A → a ∈ C → b ∉ C := by
  obtain ⟨a, ha⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, haB⟩ := hH.exists_mem_childClusters h₂ ha
  obtain ⟨b, hb, hbB⟩ := exists_of_ssubset (child_lt hB)
  refine ⟨a, ha, b, hb, by grind, fun C hC hCA haC hbC => ?_⟩
  exact hbB (hH.subset_of_mem_childClusters hB hC hCA (not_disjoint_iff.2 ⟨a, haB, haC⟩) hbC)

/-- Clusters containing a fixed nonempty set form a chain, so a nonempty selection has a least member. -/
theorem exists_least (hH : IsHierarchy H) {A : Finset X} (hn : A.Nonempty) (p : Finset X → Prop)
    [DecidablePred p] (hp : ∃ C ∈ H, A ⊆ C ∧ p C) :
    ∃ C ∈ H, A ⊆ C ∧ p C ∧ ∀ B ∈ H, A ⊆ B → p B → C ⊆ B := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨D, hD⟩ := hp
  obtain ⟨C, -, hC, hmin⟩ := (H.filter fun C => A ⊆ C ∧ p C).exists_le_minimal (by grind : D ∈ _)
  obtain ⟨hC, hAC, hc⟩ := mem_filter.1 hC
  have key B (hB : B ∈ H) (hAB : A ⊆ B) := hH.subset_or_subset_of_mem hC hB (hAC ha) (hAB ha)
  grind [Minimal]

/-- A hierarchy is determined by the rooted triples it displays. -/
theorem mem_of_triples (hH : IsHierarchy H) {A : Finset X} (hn : A.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∉ A, ∃ C ∈ H, a ∈ C ∧ b ∈ C ∧ c ∉ C) : A ∈ H := by
  by_cases h₂ : 2 ≤ #A
  · obtain ⟨a, ha, b, hb, -, hs⟩ := hH.exists_spanning_pair h₂
    obtain ⟨C, hC, h₀, -, hc⟩ := hH.exists_least (A := {a,b}) (insert_nonempty ..) (fun _ => True)
      ⟨univ, hH.1, subset_univ _, trivial⟩
    have hCA : C ⊆ A := by grind [insert_subset_iff]
    have := hs C hC
    grind
  · have := hn.card_pos
    obtain ⟨a, rfl⟩ := card_eq_one.1 (by omega : #A = 1)
    exact hH.2.1 a

end IsHierarchy

variable [DecidableEq X]

theorem mem_of_trace_eq {S A B : Finset X} (e : trace S A = trace S B)
    {x : X} (hx : x ∈ S) : x ∈ A ↔ x ∈ B := by
  simpa using Iff.of_eq (congrArg (fun C : Finset S => (⟨x, hx⟩ : S) ∈ C) e)

/-! ### Induced subtrees -/

/-- The nonempty traces of a family of clusters. -/
def restrictClusters (S : Finset X) (H : ClusterFamily X) : ClusterFamily S :=
  (H.filter fun A => (trace S A).Nonempty).image (trace S)

/-- The traces of the sides of splits that meet `S` on both sides. -/
def restrictSplits (S : Finset X) (T : ClusterFamily X) : ClusterFamily S :=
  (restrictClusters S T).erase univ

@[simp] theorem mem_restrictClusters {S : Finset X} {H : ClusterFamily X} {C : Finset S} :
    C ∈ restrictClusters S H ↔ C.Nonempty ∧ ∃ A ∈ H, trace S A = C := by
  grind [restrictClusters]

@[simp] theorem mem_restrictSplits {S : Finset X} {T : ClusterFamily X} {C : Finset S} :
    C ∈ restrictSplits S T ↔ C ≠ univ ∧ C.Nonempty ∧ ∃ A ∈ T, trace S A = C := by simp [restrictSplits]

@[simp] theorem trace_singleton (S : Finset X) (x : S) : trace S {x.1} = {x} := by ext; simp

theorem trace_ne_univ {S A : Finset X} {x : X} (hx : x ∈ S) (h : x ∉ A) : trace S A ≠ univ :=
  fun e => h (mem_subtype.1 (e.symm ▸ mem_univ (⟨x, hx⟩ : S)))

theorem trace_disjoint {S A B : Finset X} (h : Disjoint A B) : Disjoint (trace S A) (trace S B) :=
  disjoint_left.2 fun _ hx hy => disjoint_left.1 h (mem_subtype.1 hx) (mem_subtype.1 hy)

theorem IsForest.traceFamily {F : ClusterFamily X} (hF : IsForest F) (S : Finset X) :
    IsForest (restrictClusters S F) :=
  (hF.subset (filter_subset _ _)).image (trace S) (fun _ h => (mem_filter.1 h).2)
    (fun _ _ h => subtype_mono h) trace_disjoint

variable [Fintype X]

@[simp] theorem trace_compl (S A : Finset X) : trace S Aᶜ = (trace S A)ᶜ := by ext; simp

namespace SpeciesTree

/-- Lengths of the concatenated edges in the induced tree. -/
noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with trace S A = C, σ.length A

/-- The induced species tree on a nonempty set of taxa. -/
noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) : SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := mem_restrictClusters.2 ⟨⟨⟨hS.choose, hS.choose_spec⟩, mem_univ _⟩, univ, σ.univ_mem, subtype_univ _⟩
  singleton_mem x := mem_restrictClusters.2 ⟨singleton_nonempty x, {x.1}, σ.singleton_mem _, trace_singleton S x⟩
  nonempty_of_mem := (σ.isHierarchy.2.2.traceFamily S).1
  laminar := (σ.isHierarchy.2.2.traceFamily S).2
  length := σ.restrictLength S
  length_pos C hC hu := by
    obtain ⟨-, A, ha, e⟩ := mem_restrictClusters.1 hC
    refine sum_pos (fun B hB => ?_) ⟨A, mem_filter.2 ⟨ha, e⟩⟩
    obtain ⟨hB, e⟩ := mem_filter.1 hB
    exact σ.length_pos B hB (fun h => hu (e.symm.trans (h ▸ subtype_univ _)))

@[simp] theorem restrict_clusters (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).clusters = restrictClusters S σ.clusters := rfl

@[simp] theorem restrict_length (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).length = σ.restrictLength S := rfl

/-- The length of the edge above a cluster `A ∩ S` of the induced tree, when `A` is the only
cluster of `σ` with this trace. -/
theorem restrictLength_subtype_eq (σ : SpeciesTree X) {S A : Finset X} (hA : A ∈ σ.clusters)
    (h : ∀ B ∈ σ.clusters, trace S B = trace S A → B = A) :
    σ.restrictLength S (trace S A) = σ.length A := by
  unfold restrictLength
  exact sum_eq_single_of_mem A (by simp [hA]) (by grind)

end SpeciesTree

/-! ### Unrooted trees -/

section Unroot

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sides of the splits of the unrooted tree of `G`: the non-root clusters of `G` and their
complements. -/
theorem mem_unroot {G : ClusterFamily L} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  simp [unroot, and_comm]

/-- The unrooted tree of `G` is closed under complements. -/
theorem compl_mem_unroot {G : ClusterFamily L} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  grind [mem_unroot, compl_compl]

end Unroot

/-! ### Unrooting induced subtrees -/

/-- The unrooted topology of an induced subtree is the induced unrooted topology. -/
theorem unroot_restrictClusters (S : Finset X) (F : ClusterFamily X) :
    unroot (restrictClusters S F) = restrictSplits S (unroot F) := by
  ext A
  simp only [mem_unroot, mem_restrictClusters, mem_restrictSplits, compl_ne_univ_iff_nonempty]
  have hC : Aᶜ.Nonempty ↔ A ≠ univ := by simp [nonempty_iff_ne_empty]
  have hB (B : Finset X) : trace S Bᶜ = A ↔ trace S B = Aᶜ := by
    rw [trace_compl, compl_eq_comm, eq_comm (a := Aᶜ)]
  have hu (B : Finset X) : trace S B ≠ univ → B ≠ univ := by
    rintro h rfl
    exact h (subtype_univ _)
  grind [compl_compl]

namespace SpeciesTree

/-- The unrooted topology of an induced subtree is the induced unrooted topology. -/
theorem restrict_unroot (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    unroot (σ.restrict S hS).clusters = restrictSplits S (unroot σ.clusters) :=
  unroot_restrictClusters S σ.clusters

/-- The two sides of a split have the same unrooted length. -/
theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  simp only [unrootedLength, compl_compl, or_comm]

/-- An isolated split has the same total length in the induced tree. -/
theorem restrict_unrootedLength_unique (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) (A : Finset X)
    (hn : (trace S A).Nonempty) (hc : ((trace S A)ᶜ).Nonempty)
    (h : ∀ B ∈ unroot σ.clusters, trace S B = trace S A → B = A) :
    (σ.restrict S hS).unrootedLength (trace S A) = σ.unrootedLength A := by
  simp only [unrootedLength, restrict_clusters, restrict_length, restrictLength]
  rw [sum_fiberwise_eq_sum_filter]
  congr 1
  ext B
  simp only [mem_filter, mem_restrictClusters, and_assoc]
  have hu : trace S A ≠ univ := by simpa using hc.ne_empty
  have hcu : (trace S A)ᶜ ≠ univ := (compl_ne_univ_iff_nonempty _).2 hn
  have h' C (hC : C ∈ unroot σ.clusters) (e : trace S C = (trace S A)ᶜ) : C = Aᶜ := by
    exact compl_injective (by simpa using h _ (compl_mem_unroot.2 hC) (by simp [e]))
  have hT : trace S univ = univ := subtype_univ _
  have hA := trace_compl S A
  grind [mem_unroot]

end SpeciesTree

/-- Add the obligatory clusters to a list of proper internal clusters. -/
def hierarchyOf (C : ClusterFamily X) : ClusterFamily X :=
  insert univ (C ∪ univ.image fun x => {x})

@[simp] theorem mem_hierarchyOf {C : ClusterFamily X} {A : Finset X} :
    A ∈ hierarchyOf C ↔ A = univ ∨ A ∈ C ∨ #A = 1 := by
  simp [hierarchyOf, card_eq_one, eq_comm (a := A)]

def internalClusters (σ : SpeciesTree X) := σ.clusters.filter fun A => 2 ≤ #A ∧ A ≠ univ

@[simp] theorem hierarchyOf_internalClusters (σ : SpeciesTree X) : hierarchyOf (internalClusters σ) = σ.clusters := by
  ext A
  simp only [mem_hierarchyOf, internalClusters, mem_filter]
  have hp := σ.nonempty_of_mem A
  have hu := σ.univ_mem
  have hs := σ.singleton_mem
  grind [card_pos, card_eq_one]

end ADR11
