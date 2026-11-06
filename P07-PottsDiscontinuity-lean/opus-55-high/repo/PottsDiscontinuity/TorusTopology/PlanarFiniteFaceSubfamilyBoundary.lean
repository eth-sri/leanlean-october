/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

section
variable {V I : Type*} [DecidableEq I] (F : I → SimpleGraph V) (T S : Finset I) (hTS : T ⊆ S) (hcross : ∀ i ∈ T, ∀ j ∈ S, j ∉ T → Disjoint (F i).edgeSet (F j).edgeSet)
include T S hTS hcross
/-- If a selected face family has no edge in common with any omitted face,
every edge in its symmetric-difference boundary remains in the larger family's
boundary. -/
theorem faceSymmDiffList_edge_mem_mono_of_no_cross_shared_edge
    (e : Sym2 V) :
    e ∈ (faceSymmDiffList F T.toList).edgeSet →
      e ∈ (faceSymmDiffList F S.toList).edgeSet := by
  classical
  let D := S \ T
  let p := fun i => decide (e ∈ (F i).edgeSet)
  have hparT := faceSymmDiffList_edge_iff_countP_mod F T.toList e
  have hparS := faceSymmDiffList_edge_iff_countP_mod F S.toList e
  intro heT
  have hcountT : (T.toList.countP p) % 2 = 1 := by
    grind
  have hpositive : 0 < T.toList.countP p := by omega
  have hfilterpositive : 0 < (T.toList.filter p).length := by
    simp_all
  obtain ⟨i, rest, hfilter⟩ : ∃ i rest, T.toList.filter p = i :: rest := by
    cases h : T.toList.filter p with
    | nil => simp_all
    | cons i rest => simp
  have hiFilter : i ∈ T.toList.filter p := by simp_all
  have hiParts := List.mem_filter.mp hiFilter
  have hiT := Finset.mem_toList.mp hiParts.1
  have hnotD : ∀ j ∈ D.toList, e ∉ (F j).edgeSet := by
    intro j hj hje
    have hjD : j ∈ S \ T := by
      aesop
    grind
  have hfalseD : ∀ j ∈ D.toList, p j = false := by
    grind
  have hdisjoint : List.Disjoint T.toList D.toList := by
    intro j hjT hjD
    have hjFin := Finset.mem_toList.mp hjD
    have hjSDiff : j ∈ S \ T := by omega
    simp_all
  have htoFinset : (T.toList ++ D.toList).toFinset = S := by
    simpa [List.toFinset_append, D] using Finset.union_sdiff_of_subset hTS
  have hfin : S.toList.toFinset = (T.toList ++ D.toList).toFinset := by
    simp_all
  have hperm :=
    List.perm_of_nodup_nodup_toFinset_eq S.nodup_toList (List.Nodup.append T.nodup_toList D.nodup_toList hdisjoint) hfin
  have hcountS : S.toList.countP p = T.toList.countP p := by
    calc
      S.toList.countP p = (T.toList ++ D.toList).countP p := hperm.countP_eq p
      _ = T.toList.countP p := by
        simp_all
  have hcountSmod : (S.toList.countP p) % 2 = 1 := by
    omega
  exact hparS.mpr hcountSmod

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
