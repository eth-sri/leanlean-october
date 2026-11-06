module
public import ADR11.Trees.Classify
/-! On five taxa the 26 possible unrooted shapes can be checked uniformly. Their quartet
restrictions distinguish them, and each internal edge is isolated by one quartet. -/
@[expose] public section
namespace ADR11.FiveQuartet
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 8000
abbrev Taxa := Fin 5

abbrev pairs := Shape.pairs 5

theorem injective : ∀ P P' : pairs,
    (∀ S : Finset Taxa, #S = 4 →
      restrictSplits S (treeOfClusters P.1) = restrictSplits S (treeOfClusters P'.1)) → P.1 = P'.1 := by
  decide +kernel

theorem witness : ∀ P : pairs, ∀ A : P.1,
    ∃ S : Finset Taxa, #S = 4 ∧ 2 ≤ #(A.1.trace S) ∧
      2 ≤ #(A.1.trace S)ᶜ ∧
      ((treeOfClusters P.1).filter fun B =>
        B.trace S = A.1.trace S ∨
        B.trace S = (A.1.trace S)ᶜ) = {A.1, A.1ᶜ} := by decide +kernel

theorem same_of_restrict (σ σ' : SpeciesTree Taxa)
    (h : ∀ S : Finset Taxa, ∀ hS : S.Nonempty, #S = 4 →
      (σ.restrict S hS).SameUnrootedMetricTree (σ'.restrict S hS)) :
    σ.SameUnrootedMetricTree σ' := by
  let P := (unroot σ.clusters).filter fun A => #A = 2
  let P' := (unroot σ'.clusters).filter fun A => #A = 2
  have hp : P ∈ pairs := Shape.mem_pairs (by decide) σ
  have hp' : P' ∈ pairs := Shape.mem_pairs (by decide) σ'
  have ht : unroot σ.clusters = treeOfClusters P := Shape.topology (Or.inr rfl) σ
  have ht' : unroot σ'.clusters = treeOfClusters P' := Shape.topology (Or.inr rfl) σ'
  have hPP : P = P' := injective ⟨P, hp⟩ ⟨P', hp'⟩ fun S hS4 => by
    have hS : S.Nonempty := card_pos.1 (by omega)
    rw [← ht, ← ht', ← unroot_restrictClusters S σ.clusters,
      ← unroot_restrictClusters S σ'.clusters]
    exact (h S hS hS4).1
  have hU : unroot σ.clusters = unroot σ'.clusters := by rw [ht, ht', hPP]
  have heq : ∀ A ∈ P, σ.unrootedLength A = σ'.unrootedLength A := by
    intro A hA
    obtain ⟨S, hS4, hC2, hCc2, hfilter⟩ := witness ⟨P, hp⟩ ⟨A, hA⟩
    have hS : S.Nonempty := card_pos.1 (by omega)
    have hh := (h S hS hS4).length_eq (A.trace S) hC2 hCc2
    have hl : ∀ τ : SpeciesTree Taxa, unroot τ.clusters = treeOfClusters P →
        (τ.restrict S hS).unrootedLength (A.trace S) = τ.unrootedLength A := by
      intro τ hτ
      let C := A.trace S
      have hCne : C.Nonempty := card_pos.1 (zero_lt_two.trans_le hC2)
      have hCcne : Cᶜ.Nonempty := card_pos.1 (zero_lt_two.trans_le hCc2)
      have hCu : C ≠ univ := by simpa using (compl_ne_univ_iff_nonempty Cᶜ).2 hCcne
      have hCcu : Cᶜ ≠ univ := (compl_ne_univ_iff_nonempty C).2 hCne
      unfold SpeciesTree.unrootedLength
      rw [SpeciesTree.restrict_clusters, SpeciesTree.restrict_length]
      symm
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun B => B.trace S)
        (t := (restrictClusters S τ.clusters).filter (fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ)))]
      · apply Finset.sum_congr rfl
        intro D hD
        unfold SpeciesTree.restrictLength
        rw [filter_filter]
        refine Finset.sum_congr (filter_congr fun B hB => ?_) fun _ _ => rfl
        have hD' := (mem_filter.1 hD).2.2
        have hh := Finset.ext_iff.1 (hτ.symm ▸ hfilter) B
        simp only [mem_filter, mem_insert, mem_singleton] at hh
        grind [mem_unroot]
      · have hcompl := subtype_compl (S := S) A
        grind [← subtype_nonempty_iff, ← mem_restrictClusters]
    rwa [hl σ ht, hl σ' (hU ▸ ht)] at hh
  refine ⟨hU, fun A hA hA2 hAc2 => ?_⟩
  by_cases h2 : #A = 2
  · exact heq A (mem_filter.2 ⟨hA, h2⟩)
  · have hc : #Aᶜ = 2 := by
      have := card_compl A
      simp at this
      omega
    rw [← σ.unrootedLength_compl A, ← σ'.unrootedLength_compl A]
    exact heq Aᶜ (mem_filter.2 ⟨compl_mem_unroot.2 hA, hc⟩)
end ADR11.FiveQuartet
