/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

theorem faceSymmDiffList_eq_implies_toFinset_eq
    {V I : Type*} [DecidableEq I]
    (F : I → SimpleGraph V) (p : I → Sym2 V) (rank : I → ℕ)
    (hpF : ∀ i, p i ∈ (F i).edgeSet)
    (htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i)
    (L M : List I) (hLnodup : L.Nodup) (hMnodup : M.Nodup)
    (hEq : faceSymmDiffList F L = faceSymmDiffList F M) :
    L.toFinset = M.toFinset := by
  classical
  by_contra hLM
  let D := L.toFinset ∆ M.toFinset
  have hDne : D.Nonempty := by
    aesop
  obtain ⟨f, hfD, hmax⟩ := D.exists_max_image rank hDne
  have hcommon : ∀ i, rank f < rank i →
      (i ∈ L.toFinset ↔ i ∈ M.toFinset) := by
    intro i hri
    constructor
    · intro hiL
      by_contra hiM
      have hiD : i ∈ D := by
        change i ∈ L.toFinset ∆ M.toFinset
        rw [Finset.mem_symmDiff]
        simp_all
      grind
    · intro hiM
      by_contra hiL
      have hiD : i ∈ D := by
        change i ∈ L.toFinset ∆ M.toFinset
        rw [Finset.mem_symmDiff]
        simp_all
      grind
  let P : I → Prop := fun i => p f ∈ (F i).edgeSet
  let CL : Finset I := L.toFinset.filter P
  let CM : Finset I := M.toFinset.filter P
  have herase : CL.erase f = CM.erase f := by
    grind
  have hcountL : L.countP (fun i => p f ∈ (F i).edgeSet) = CL.card :=
    (List.Nodup.card_eq_countP hLnodup).symm
  have hcountM : M.countP (fun i => p f ∈ (F i).edgeSet) = CM.card :=
    (List.Nodup.card_eq_countP hMnodup).symm
  have hmod :
      (L.countP (fun i => p f ∈ (F i).edgeSet) % 2 = 1) ↔
      (M.countP (fun i => p f ∈ (F i).edgeSet) % 2 = 1) := by
    have hparL := faceSymmDiffList_edge_iff_countP_mod F L (p f)
    have hparM := faceSymmDiffList_edge_iff_countP_mod F M (p f)
    simp_all
  rcases Finset.mem_symmDiff.mp hfD with ⟨hfL, hfM⟩ | ⟨hfM, hfL⟩
  · have hpf := hpF f
    have hfCL : f ∈ CL := by grind
    have hfCM : f ∉ CM := by
      grind
    have hcardL : CL.card = (CL.erase f).card + 1 := by
      grind
    have hcardM : CM.card = (CM.erase f).card := by
      simp_all
    grind
  · have hpf := hpF f
    have hfCM : f ∈ CM := by grind
    have hfCL : f ∉ CL := by
      grind
    have hcardM : CM.card = (CM.erase f).card + 1 := by
      grind
    have hcardL : CL.card = (CL.erase f).card := by
      rw [Finset.erase_eq_of_notMem hfCL]
    grind

end PottsDiscontinuity.TorusTopology.Planar.Medial
