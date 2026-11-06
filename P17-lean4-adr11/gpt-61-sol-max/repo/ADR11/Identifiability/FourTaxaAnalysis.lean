module
public import ADR11.Computation.Quartets
public import ADR11.Trees.Hierarchy
/-! The certified quartet distributions yield a uniform split-recovery criterion:
a two-taxon split is present exactly when its quartet has probability greater than `1/3`.
Together with the matching probability, this identifies the unrooted metric tree,
including unresolved species trees. -/
@[expose] public section
namespace ADR11
open Finset Real
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {A : Finset X}

theorem unrootedLength_pos (σ : SpeciesTree X)
    (hA : A ∈ unroot σ.clusters) : 0 < σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  refine Finset.sum_pos (fun C hC => ?_) ?_
  · rw [mem_filter] at hC
    exact σ.length_pos C hC.1 hC.2.1
  · simpa [filter_nonempty_iff, and_or_left, exists_or] using mem_unroot.1 hA

namespace Q4
def quartet (i : Fin 3) : Finset (Fin 4) := {0, ⟨i.val + 1, by omega⟩}
theorem cases : ∀ A : Finset (Fin 4), #A = 2 → ∃ i : Fin 3,
    treeOfClusters {A} = treeOfClusters {quartet i} ∧
    (A ∈ U4 1 ↔ i = 0) ∧ (i = 0 → A = {0, 1} ∨ A = ({0, 1} : Finset (Fin 4))ᶜ) ∧
    A ∉ U4 0 := by decide +kernel

end Q4

theorem unrootedDist_eq_iff_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := by
  have four_recovery (σ : SpeciesTree X) (A : Finset X) (hA : #A = 2) :
      (A ∈ unroot σ.clusters ↔ 1 / 3 < σ.unrootedDist id (treeOfClusters {A})) ∧
      (A ∈ unroot σ.clusters → σ.unrootedDist id (treeOfClusters {A}) =
        1 - 2 / 3 * exp (-σ.unrootedLength A)) := by
    obtain ⟨e, k, hc⟩ := Shape.normal (Or.inl rfl) hX U4 2 (by decide +kernel) σ
    let τ := σ.relabel e.symm
    let B := A.map e.symm.toEmbedding
    have hd := SpeciesTree.unrootedDist_relabel σ e.symm (treeOfClusters {A})
    have htree : relabelFamily e.symm (treeOfClusters {A}) = treeOfClusters {B} := by
      unfold treeOfClusters hierarchyOf
      rw [← unroot_relabelFamily]
      congr 1
      simp [B, relabelFamily, image_image, Function.comp_def]
      congr 2
      simpa only [image_image, Function.comp_def] using
        congrArg (image fun x : Fin 4 => ({x} : Finset (Fin 4)))
          (image_univ_of_surjective e.symm.surjective)
    rw [htree] at hd
    change τ.unrootedDist id (treeOfClusters {B}) = _ at hd
    rw [← map_mem_relabelFamily (e := e.symm) (F := unroot σ.clusters),
      ← unroot_relabelFamily, ← SpeciesTree.relabel_clusters, hc, ← hd,
      ← SpeciesTree.unrootedLength_relabel σ e.symm A]
    clear hd
    obtain ⟨i, ht, hm, he, hn⟩ := Q4.cases B (by simpa [B] using hA)
    have hp := Q4.core k τ hc
    have hx : k = 1 → exp (-τ.unrootedLength {0, 1}) < 1 := by
      intro hk
      subst k
      exact exp_lt_one_iff.2 (neg_lt_zero.2 (unrootedLength_pos τ (hc ▸ (by decide))))
    have hlen (hi : i = 0) : τ.unrootedLength B = τ.unrootedLength {0, 1} := by
      grind [SpeciesTree.unrootedLength_compl]
    fin_cases k <;> fin_cases i <;> simp_all [Q4.quartet, B, τ] <;> try linarith
    have := exp_lt_one_iff.2 (neg_lt_zero.2 hx)
    linarith

  constructor
  · intro h
    have hr (A : Finset X) (hA : #A = 2) : A ∈ unroot σ.clusters ↔ A ∈ unroot σ'.clusters := by
      rw [(four_recovery σ A hA).1, (four_recovery σ' A hA).1, h]
    refine ⟨?_, fun A hA h2 hc2 => ?_⟩
    · ext A
      rw [mem_unroot_iff (Or.inl hX) σ A, mem_unroot_iff (Or.inl hX) σ' A]
      simp only [mem_filter]
      grind
    · have hA2 : #A = 2 := by have := card_compl A; omega
      have h1 := (four_recovery σ A hA2).2 hA
      rw [h, ((four_recovery σ' A hA2).2 ((hr A hA2).1 hA))] at h1
      apply neg_injective
      apply exp_injective
      linarith
  · intro h
    obtain ⟨e, k, hc⟩ := Shape.normal (Or.inl rfl) hX U4 2 (by decide +kernel) σ
    have hc' : unroot (σ'.relabel e.symm).clusters = U4 k := by
      simpa only [SpeciesTree.relabel_clusters, unroot_relabelFamily, h.1] using hc
    apply (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).1
    let τ := σ.relabel e.symm
    let τ' := σ'.relabel e.symm
    have hx : (if k.val = 0 then 1 else exp (-τ.unrootedLength {0, 1})) =
        (if k.val = 0 then 1 else exp (-τ'.unrootedLength {0, 1})) := by
      fin_cases k
      · rfl
      · let A := ({0, 1} : Finset (Fin 4)).map e.toEmbedding
        have hl := h.length_eq A (by simp [A]) (by simp [card_compl, A, hX])
        rw [← SpeciesTree.unrootedLength_relabel σ e.symm A,
          ← SpeciesTree.unrootedLength_relabel σ' e.symm A] at hl
        simpa [τ, τ', A, Finset.map_map] using hl
    have hp := Q4.core k τ hc
    have hp' := Q4.core k τ' hc'
    rw [hx] at hp
    funext T
    by_cases ht : T ≠ treeOfClusters {{0, 1}} ∧ T ≠ treeOfClusters {{0, 2}} ∧ T ≠ treeOfClusters {{0, 3}}
    · have hz (θ : SpeciesTree (Fin 4)) (hθ : unroot θ.clusters = U4 k) : θ.unrootedDist id T = 0 := by
        let S : Finset (Family (Fin 4)) :=
          {treeOfClusters {{0, 1}}, treeOfClusters {{0, 2}}, treeOfClusters {{0, 3}}}
        obtain ⟨h1, h2, h3⟩ := Q4.core k θ hθ
        have hs : ∑ U ∈ S, θ.unrootedDist id U = 1 := by
          rw [sum_insert (by decide), sum_insert (by decide), sum_singleton, h1, h2, h3]
          ring
        apply (sum_eq_zero_iff_of_nonneg (s := Sᶜ)
          (fun U _ => unrootedDist_nonneg θ id U)).1 ?_ T (by simpa [S] using ht)
        linarith [sum_add_sum_compl S (θ.unrootedDist id), unrootedDist_sum θ id]
      rw [hz τ hc, hz τ' hc']
    · grind
end ADR11
