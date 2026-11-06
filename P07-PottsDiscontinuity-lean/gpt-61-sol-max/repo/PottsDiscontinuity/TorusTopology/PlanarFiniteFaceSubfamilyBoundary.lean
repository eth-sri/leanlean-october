/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial




section

variable {V I : Type*} [DecidableEq I] (F : I → SimpleGraph V) (T S : Finset I) (hTS : T ⊆ S) (hcross : ∀ i ∈ T, ∀ j ∈ S, j ∉ T →
      Disjoint (F i).edgeSet (F j).edgeSet)
include V I F T S hTS hcross

/-- If a selected face family has no edge in common with any omitted face,
every edge in its symmetric-difference boundary remains in the larger family's
boundary. -/
theorem faceSymmDiffList_edge_mem_mono_of_no_cross_shared_edge
    
    (e : Sym2 V) :
    e ∈ (faceSymmDiffList F T.toList).edgeSet →
      e ∈ (faceSymmDiffList F S.toList).edgeSet := by
  classical
  let D := S \ T
  let p  := fun i => decide (e ∈ (F i).edgeSet)
  
  have hparS := faceSymmDiffList_edge_iff_countP_mod F S.toList e
  intro heT
  have hcountT :  T.toList.countP p  % 2 = 1 := by
                                                  solve_by_elim [_root_.Iff.mp, _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.faceSymmDiffList_edge_iff_countP_mod]
  have hpositive : 0 < T.toList.countP p := by omega
  
  obtain ⟨i, rest, hfilter⟩ : ∃ i rest, T.toList.filter p = i :: rest := List.exists_cons_of_length_pos (by
                                                                                                           simp_all)
  have hiFilter : i ∈ T.toList.filter p := by simp [hfilter]
  
  have hiT  := Finset.mem_toList.mp (List.mem_filter.mp hiFilter).1
  
  have hnotD : ∀ j ∈ D.toList, e ∉ (F j).edgeSet := by
    intro j hj hje
    have hjD : j ∈ S \ T := by
      simpa [D] using Finset.mem_toList.mp hj
    grind
  have hfalseD : ∀ j ∈ D.toList, p j = false := by
    grind
  have hcountD : D.toList.countP p = 0 := by
    simp_all
  
  have hnodup  :=
    List.Nodup.append T.nodup_toList D.nodup_toList (by
                                                       
                                                       intro j hjT hjD
                                                       
                                                       have hjSDiff : j ∈ S \ T := by simpa [D] using  Finset.mem_toList.mp hjD 
                                                       simp_all)
  have htoFinset : (T.toList ++ D.toList).toFinset = S := by
    simpa [D] using Finset.union_sdiff_of_subset hTS
  
  
  have hcountS : S.toList.countP p = T.toList.countP p := by
    calc
      S.toList.countP p = (T.toList ++ D.toList).countP p := (List.perm_of_nodup_nodup_toFinset_eq S.nodup_toList hnodup (by
                                                                                                                              simp_all)).countP_eq p
      _ = T.toList.countP p := by
        rw [List.countP_append, hcountD]
        simp
  grind

/-- The graph symmetric-difference boundary of a selected subfamily is contained
in that of the full family when no selected face shares an edge with an omitted
face. -/
theorem faceSymmDiffList_le_of_no_cross_shared_edge
     :
    faceSymmDiffList F T.toList ≤ faceSymmDiffList F S.toList := by
  intro u v huv
  apply (faceSymmDiffList F S.toList).mem_edgeSet.mp
  apply faceSymmDiffList_edge_mem_mono_of_no_cross_shared_edge F T S hTS hcross
  simp_all

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
