module
public import ADR11.Computation.Shapes

@[expose] public section
namespace ADR11
open Finset _root_.ADR11.Computation

def fiveQuartets : Finset (Cl 5) := (univ : Finset (Fin 5)).powersetCard 4

section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
set_option synthInstance.maxSize 1000 in
private theorem five_quartet_certificate : ∀ k : Fin 3,
    (∀ U ∈ smallTopologies 5,
      (∀ Q ∈ fiveQuartets, restrictSplits Q (U5 k) = restrictSplits Q U) → U5 k = U) ∧
    (∀ A ∈ U5 k, 2 ≤ #A → 2 ≤ #Aᶜ →
      ∃ Q ∈ fiveQuartets, 2 ≤ #(trace Q A) ∧ 2 ≤ #((trace Q A)ᶜ) ∧
        ∀ B ∈ U5 k, trace Q B = trace Q A → B = A) := by decide +kernel
end

/-- Recover a five-taxon metric split system from its quartet marginals. -/
theorem five_metric_of_quartets (τ τ' : TreeOn 5) {k : Fin 3}
    (hu : unroot τ.clusters = U5 k)
    (h : ∀ Q : Cl 5, ∀ hQ : Q.Nonempty, #Q = 4 →
      (τ.restrict Q hQ).SameUnrootedMetricTree (τ'.restrict Q hQ)) : τ.SameUnrootedMetricTree τ' := by
  have metric (Q : Cl 5) (hQ : Q ∈ fiveQuartets) : ∃ hn : Q.Nonempty,
      (τ.restrict Q hn).SameUnrootedMetricTree (τ'.restrict Q hn) := by
    have hc := (mem_powersetCard.1 hQ).2
    exact ⟨card_pos.1 (by omega), h Q _ hc⟩
  choose hn H using metric
  have he : unroot τ.clusters = unroot τ'.clusters := hu.trans <|
    (five_quartet_certificate k).1 _ (topology_mem τ' (by decide)) fun Q hQ => by
      simpa only [SpeciesTree.restrict_unroot, hu] using (H Q hQ).1
  refine ⟨he, fun A hA h2 h2' => ?_⟩
  obtain ⟨Q, hQ, hA1, hA2, uniq⟩ := (five_quartet_certificate k).2 A (hu ▸ hA) h2 h2'
  have e (ρ : TreeOn 5) (hr : unroot ρ.clusters = U5 k) :=
    ρ.restrict_unrootedLength_unique Q (hn Q hQ) A (card_pos.1 (by omega)) (card_pos.1 (by omega))
      (fun B hB => uniq B (hr ▸ hB))
  rw [← e τ hu, ← e τ' (he ▸ hu)]
  apply (H Q hQ).2 _ _ hA1 hA2
  have ht : (trace Q A)ᶜ.Nonempty := card_pos.1 (by omega)
  simp only [SpeciesTree.restrict_unroot, mem_restrictSplits]
  exact ⟨by simpa using ht.ne_empty, card_pos.1 (by omega), A, hA, rfl⟩

end ADR11
