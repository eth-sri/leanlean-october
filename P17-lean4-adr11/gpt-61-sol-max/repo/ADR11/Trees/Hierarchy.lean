module

public import ADR11.MSC.Basic
@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {σ σ' : SpeciesTree X} {H : Family X} {A S : Finset X}

theorem SpeciesTree.SameUnrootedMetricTree.length_eq
    (h : σ.SameUnrootedMetricTree σ') (A : Finset X) (h2 : 2 ≤ #A) (h2c : 2 ≤ #Aᶜ) :
    σ.unrootedLength A = σ'.unrootedLength A := by
  have zero (τ : SpeciesTree X) (hn : A ∉ unroot τ.clusters) : τ.unrootedLength A = 0 := by
    apply sum_eq_zero
    grind [mem_unroot]
  by_cases hA : A ∈ unroot σ.clusters
  · exact h.2 A hA h2 h2c
  · rw [zero σ hA, zero σ' (by rwa [← h.1])]

namespace SpeciesTree

@[simp] theorem restrict_clusters (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).clusters = restrictClusters S σ.clusters := rfl

@[simp] theorem restrict_length (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).length = σ.restrictLength S := rfl

end SpeciesTree

theorem mem_restrictClusters {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A.trace S).Nonempty ∧ A.trace S = C := by
  simp [restrictClusters, ← subtype_nonempty_iff, and_assoc]

theorem subtype_compl (A : Finset X) :
    Aᶜ.trace S = (A.trace S)ᶜ := by
  ext x
  simp [mem_subtype, mem_compl]

theorem subtype_ne_univ_iff :
    A.trace S ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, ← compl_ne_univ_iff_nonempty, compl_compl]

theorem subtype_mem_restrictClusters
    (hA : A ∈ H) (hAS : (A.trace S).Nonempty) : A.trace S ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

namespace SpeciesTree

theorem restrictLength_subtype_eq (σ : SpeciesTree X) (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ)
    (h : ∀ B ∈ σ.clusters, B.trace S = A.trace S → B = A) :
    σ.restrictLength S (A.trace S) = σ.length A := by
  grind [← Finset.sum_eq_single_of_mem A, restrictLength]

end SpeciesTree

variable {L : Type*} [Fintype L] [DecidableEq L]

theorem compl_mem_unroot {G : Family L} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

theorem IsHierarchy.mem_of_triples (hH : IsHierarchy H)
    (hA : A.Nonempty) (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ H, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ H := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨B, hB, hmin⟩ := (H.filter (A ⊆ ·)).exists_minimal
    ⟨univ, mem_filter.2 ⟨hH.1, subset_univ A⟩⟩
  obtain ⟨hBH, hAB⟩ := mem_filter.1 hB
  suffices hBA : B ⊆ A by rwa [subset_antisymm hBA hAB] at hBH
  intro b hbB
  by_contra hbA
  set F := H.filter (fun C => a ∈ C ∧ b ∉ C)
  obtain ⟨C, hC, hmax⟩ := F.exists_maximal (by
    simpa [F, filter_nonempty_iff] using h a ha a ha b hbA)
  obtain ⟨hCH, haC, hbC⟩ := mem_filter.1 hC
  have hAC : A ⊆ C := by
    intro a' ha'
    obtain ⟨D, hD, haD, ha'D, hbD⟩ := h a ha a' ha' b hbA
    have := hH.2.2.2 C hCH D hD
    grind [disjoint_left]
  have := hH.2.2.2 B hBH C hCH
  grind

theorem unroot_restrictClusters (S : Finset X) (H : Family X) :
    unroot (restrictClusters S H) = restrictSplits S (unroot H) := by
  simp only [unroot, restrictClusters, restrictSplits,
    ← filter_ne', filter_image, filter_union, image_union, image_image, filter_filter,
    Function.comp_def, subtype_compl, subtype_ne_univ_iff, compl_compl]
  congr! 2 <;> apply filter_congr <;> aesop

namespace SpeciesTree

theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  simp only [unrootedLength, compl_compl, or_comm]

end SpeciesTree

end ADR11
