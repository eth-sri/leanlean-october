module

public import ADR11.MSC.Marginal
public import ADR11.Trees.Hierarchy
public import ADR11.Identifiability.Five
public import ADR11.Identifiability.Four
public import ADR11.Identifiability.Quartets

@[expose] public section

namespace ADR11
open Finset
open Real _root_.ADR11.Computation in
/-- Five-taxon rooted identifiability, also for multifurcating species trees. -/
theorem identify_five {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 5)
    (σ σ' : SpeciesTree X) (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  obtain ⟨e, k, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e]
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e).2 h
  have hu := five_metric_of_quartets _ _ he fun Q hQ h4 =>
    (quartet_identifiability (by simpa using h4) _ _).1 (unrootedDist_restrict_eq hd Q hQ)
  refine identify_normal_five _ _ he (hu.1 ▸ he) ?_ ?_ hd <;>
    exact congrArg (fun t => exp (-t)) (hu.length_eq (by decide) (by decide))

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem exists_five (hX : 5 ≤ Fintype.card X) (a b c : X) :
    ∃ S : Finset X, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ #S = 5 := by
  obtain ⟨S, h, -, hS⟩ := exists_subsuperset_card_eq (subset_univ ({a,b,c} : Finset X))
    (card_le_three.trans (by decide : 3 ≤ 5)) (by simpa using hX)
  exact ⟨S, by grind⟩

private theorem clusters_subset_of_five (hX : 5 ≤ Fintype.card X) {σ τ : SpeciesTree X}
    (h : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).clusters = (τ.restrict S hS).clusters) : σ.clusters ⊆ τ.clusters := by
  intro A hA
  apply τ.isHierarchy.mem_of_triples (σ.nonempty_of_mem A hA)
  intro a ha b hb c hc
  obtain ⟨S, haS, hbS, hcS, hS⟩ := exists_five hX a b c
  have hAS : trace S A ∈ (σ.restrict S ⟨a, haS⟩).clusters :=
    mem_restrictClusters.2 ⟨⟨⟨a, haS⟩, mem_subtype.2 ha⟩, A, hA, rfl⟩
  obtain ⟨-, B, hB, hBA⟩ := mem_restrictClusters.1 (h S ⟨a, haS⟩ hS ▸ hAS)
  exact ⟨B, hB, by grind [mem_of_trace_eq]⟩

private theorem same_of_five (hX : 5 ≤ Fintype.card X) {σ τ : SpeciesTree X}
    (h : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (τ.restrict S hS)) : σ.SameRootedMetricTree τ := by
  have hc := Subset.antisymm (clusters_subset_of_five hX fun S hn hS => (h S hn hS).1)
    (clusters_subset_of_five hX fun S hn hS => (h S hn hS).1.symm)
  refine ⟨hc, fun A hA h₂ hu => ?_⟩
  have hH := σ.isHierarchy
  obtain ⟨a, ha, b, hb, hab, hs⟩ := hH.exists_spanning_pair h₂
  obtain ⟨P, -, -, hp, hmin⟩ := hH.exists_least (σ.nonempty_of_mem A hA) (A ⊂ ·)
    ⟨univ, σ.univ_mem, subset_univ _, ssubset_univ_iff.2 hu⟩
  obtain ⟨c, hcP, hcA⟩ := exists_of_ssubset hp
  obtain ⟨S, haS, hbS, hcS, hS⟩ := exists_five hX a b c
  let C := trace S A
  have h₂ : 2 ≤ #C := one_lt_card.2
    ⟨⟨a, haS⟩, mem_subtype.2 ha, ⟨b, hbS⟩, mem_subtype.2 hb, hab ∘ congrArg Subtype.val⟩
  have hm : C ∈ (σ.restrict S ⟨a, haS⟩).clusters :=
    mem_restrictClusters.2 ⟨card_pos.1 (by omega), A, hA, rfl⟩
  have hCu : C ≠ univ := trace_ne_univ hcS hcA
  have uniq B (hB : B ∈ σ.clusters) (e : trace S B = C) : B = A := by
    have := hH.subset_or_subset_of_mem hB hA ((mem_of_trace_eq e haS).2 ha) ha
    have := hs B hB
    have := hmin B hB
    grind [mem_of_trace_eq]
  have hl := (h S ⟨a, haS⟩ hS).2 C hm h₂ hCu
  change σ.restrictLength S C = τ.restrictLength S C at hl
  rwa [σ.restrictLength_subtype_eq hA uniq,
    τ.restrictLength_subtype_eq (hc ▸ hA) (by simpa only [← hc] using uniq)] at hl

/-- Rooted identifiability on at least five taxa, including nonbinary species trees. -/
theorem rooted_identifiability (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  same_of_five hX fun S hS hk => identify_five (by simpa using hk) _ _ (unrootedDist_restrict_eq h S hS)

end ADR11
