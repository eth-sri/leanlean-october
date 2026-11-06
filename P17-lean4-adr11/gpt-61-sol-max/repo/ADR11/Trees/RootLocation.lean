module
public import ADR11.Trees.Hierarchy
@[expose] public section
namespace ADR11
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {σ σ' : SpeciesTree X}

theorem same_of_fives (hX : 5 ≤ Fintype.card X)
    (h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS)) :
    σ.SameRootedMetricTree σ' := by
  have five_superset (a b c : X) :
      ∃ S : Finset X, #S = 5 ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
    obtain ⟨S, h, -, hn⟩ := exists_subsuperset_card_eq (n := 5) (subset_univ {a, b, c})
      (card_le_three.trans (by norm_num)) (by simpa using hX)
    refine ⟨S, hn, ?_, ?_, ?_⟩ <;> apply h <;> simp

  have incl : ∀ τ τ' : SpeciesTree X,
      (∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
        (τ.restrict S hS).clusters = (τ'.restrict S hS).clusters) → τ.clusters ⊆ τ'.clusters := by
    intro τ τ' h5 A hA
    apply τ'.isHierarchy.mem_of_triples (τ.nonempty_of_mem A hA)
    intro a ha a' ha' b hb
    obtain ⟨S, hS5, haS, ha'S, hbS⟩ := five_superset a a' b
    have hS : S.Nonempty := ⟨a, haS⟩
    have hD : A.trace S ∈ (τ.restrict S hS).clusters :=
      subtype_mem_restrictClusters hA ⟨⟨a, haS⟩, by simpa using ha⟩
    rw [h5 S hS hS5] at hD
    obtain ⟨C, hC, _, hCD⟩ := mem_restrictClusters.1 hD
    simp only [Finset.ext_iff, Finset.mem_subtype, Subtype.forall] at hCD
    grind
  have hcl := Subset.antisymm (incl σ σ' fun S hS hS5 => (h5 S hS hS5).1)
    (incl σ' σ fun S hS hS5 => (h5 S hS hS5).1.symm)
  refine ⟨hcl, fun A hA hA2 hAu => ?_⟩
  obtain ⟨a₁, ha₁A⟩ := card_pos.1 (by omega : 0 < #A)
  obtain ⟨B, hB, ha₁⟩ := (σ.isHierarchy).exists_mem_childClusters hA2 ha₁A
  obtain ⟨a₂, ha₂A, ha₂⟩ := exists_of_ssubset (mem_childClusters.1 hB).2.1
  obtain ⟨P, hP, hmin⟩ := (σ.clusters.filter fun C => A ⊂ C).exists_minimal
    ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 hAu⟩⟩
  obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset (mem_filter.1 hP).2
  obtain ⟨S, hS5, ha1S, ha2S, hbS⟩ := five_superset a₁ a₂ b
  have hS : S.Nonempty := ⟨a₁, ha1S⟩
  have huniq : ∀ C ∈ σ.clusters, C.trace S = A.trace S → C = A := by
    intro C hC he
    simp only [Finset.ext_iff, Finset.mem_subtype, Subtype.forall] at he
    have hAC : A ⊆ C := by
      have := σ.laminar A hA C hC
      have := σ.laminar B (mem_childClusters.1 hB).1 C hC
      clear h5 incl
      grind [mem_childClusters, disjoint_left]
    by_contra hCA
    have hm := hmin (mem_filter.2 ⟨hC, Finset.ssubset_iff_subset_ne.2 ⟨hAC, Ne.symm hCA⟩⟩)
    have hn := σ.laminar P (mem_filter.1 hP).1 C hC
    have hAP := (mem_filter.1 hP).2.subset
    grind
  have := (h5 S hS hS5).2 _ (subtype_mem_restrictClusters hA ⟨⟨a₁, ha1S⟩, by simpa using ha₁A⟩) (by
    rw [card_subtype]
    exact one_lt_card.2 ⟨a₁, by simp [ha₁A, ha1S], a₂, by simp [ha₂A, ha2S], (by grind)⟩
  ) (subtype_ne_univ_iff.2 ⟨b, by simp [hbA, hbS]⟩)
  rw [SpeciesTree.restrict_length, SpeciesTree.restrict_length,
    σ.restrictLength_subtype_eq hA hAu huniq,
    σ'.restrictLength_subtype_eq (hcl ▸ hA) hAu fun C hC => huniq C (hcl ▸ hC)] at this
  exact this
end ADR11
