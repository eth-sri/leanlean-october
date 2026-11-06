/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenForest
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSymmDiff

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

/-- The symmetric difference of the faces in a finite list, with repetitions
interpreted by parity. -/
def faceSymmDiffList {V I : Type*} (F : I → SimpleGraph V) : List I → SimpleGraph V
  | [] => ⊥
  | i :: is => F i ∆ faceSymmDiffList F is



/-- If even-degree faces have distinct triangular pivot edges, they span every
 even-degree subgraph if deleting all pivots leaves an acyclic graph. -/
theorem exists_faceSymmDiffList_of_even_subgraph
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (F : I → SimpleGraph V) (p : I → Sym2 V) (rank : I → ℕ)
    [LocallyFinite G] [∀ i, LocallyFinite (F i)]
    (hFle : ∀ i, F i ≤ G)
    (hFeven : ∀ i v, Even ((F i).degree v))
    (hpF : ∀ i, p i ∈ (F i).edgeSet)
    (htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i)
    (hacyclic : (G.deleteEdges (Set.range p)).IsAcyclic)
    (H : SimpleGraph V) [LocallyFinite H]
    (hle : H ≤ G) (hHeven : ∀ v, Even (H.degree v)) :
    ∃ L : List I, L.Nodup ∧ faceSymmDiffList F L = H := by
  classical
  let aux : ∀ (S : Finset I) K [LocallyFinite K],
      K ≤ G → (∀ v, Even (K.degree v)) →
      (∀ j, j ∉ S → p j ∉ K.edgeSet) →
      (∀ i ∈ S, ∀ j, j ∉ S → rank i ≤ rank j) →
      ∃ L : List I, L.Nodup ∧ (∀ i ∈ L, i ∈ S) ∧ faceSymmDiffList F L = K := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih K instK hKG hKeven hKnopivot hrank
    by_cases hSn : S.Nonempty
    · obtain ⟨f, hfS, hfmax⟩ := S.exists_max_image rank hSn
      let S' := S.erase f
      
      have hS'sub  := Finset.erase_ssubset hfS
      
      by_cases hfp : p f ∈ K.edgeSet
      · let K' := K ∆ F f
        have hK'le : K' ≤ G := by
          intro v w hvw
          
          rcases hvw with h | h
          · exact hKG h.1
          · exact hFle f h.1
        
        have hK'even : ∀ v, Even (K'.degree v) := by
                                                    solve_by_elim [_root_.PottsDiscontinuity.TorusTopology.Planar.Medial.degree_even_symmDiff]
        have hK'no : ∀ j, j ∉ S' → p j ∉ K'.edgeSet := by
          intro j hj hjK'
          have hK'edge := hjK'
          rw [show K' = K ∆ F f by rfl, symmDiff_def, SimpleGraph.edgeSet_sup] at hK'edge
          simp only [SimpleGraph.edgeSet_sdiff] at hK'edge
          all_goals grind
        obtain ⟨L, hLnodup, hLmem, hLdecomp⟩ :=
          ih S' hS'sub K' hK'le hK'even hK'no (by
                                                 grind)
        refine ⟨f :: L, ?_, ?_, ?_⟩
        · grind
        · grind
        · change F f ∆ faceSymmDiffList F L = K
          rw [hLdecomp]
          
          rw [← symmDiff_assoc, symmDiff_symmDiff_self']
      · grind
    · have hSempty  := Finset.not_nonempty_iff_eq_empty.mp hSn
      subst S
      have hKleDel : K ≤ G.deleteEdges (Set.range p) := by
        intro v w hvw
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hKG hvw, ?_⟩
        intro hp
        obtain ⟨j, hpeq⟩ := Set.mem_range.mp hp
        apply hKnopivot j (by simp)
        simpa only [hpeq, SimpleGraph.mem_edgeSet] using hvw
      have hKacyclic  := hacyclic.anti hKleDel
      have hKevenN : ∀ v, Even  (K.neighborSet v).ncard  := by
        simp_all
      have hKbot  := eq_bot_of_isAcyclic_even_degree K hKacyclic (by
        intro v
        rw [← SimpleGraph.ncard_neighborSet]
        exact hKevenN v)
      subst K
      exact ⟨[], List.nodup_nil, by simp, by simp [faceSymmDiffList]⟩
  
  obtain ⟨L, hLnodup, hLmem, hLdecomp⟩ :=
    aux Finset.univ H hle hHeven (by simp) (by
                                              simp)
  exact ⟨L, hLnodup, hLdecomp⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
