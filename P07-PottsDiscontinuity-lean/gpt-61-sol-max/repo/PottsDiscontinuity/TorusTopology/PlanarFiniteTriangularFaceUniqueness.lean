/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial


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
  
  
  obtain ⟨f, hfD, hmax⟩ := (L.toFinset ∆ M.toFinset).exists_max_image rank (Finset.symmDiff_nonempty.mpr hLM)
  have hcommon : ∀ i, rank f < rank i →
      (i ∈ L.toFinset ↔ i ∈ M.toFinset) := by
    intro i hri
    constructor
    · 
      by_contra hiM
      
      have hbound := hmax i (by
                               
                               rw [Finset.mem_symmDiff]
                               simp_all)
      omega
    · 
      by_contra hiL
      
      have hbound := hmax i (by
                               
                               rw [Finset.mem_symmDiff]
                               simp_all)
      omega
  let P  := fun i => p f ∈ (F i).edgeSet
  let CL  := L.toFinset.filter P
  let CM  := M.toFinset.filter P
  have herase : CL.erase f = CM.erase f := by
    grind
  have hcountL : L.countP (fun i => p f ∈ (F i).edgeSet) = CL.card := (List.Nodup.card_eq_countP hLnodup).symm
  have hcountM : M.countP (fun i => p f ∈ (F i).edgeSet) = CM.card := (List.Nodup.card_eq_countP hMnodup).symm
  have hmod :
       L.countP (fun i => p f ∈ (F i).edgeSet) % 2 = 1  ↔
       M.countP (fun i => p f ∈ (F i).edgeSet) % 2 = 1  := by
    have hparL := faceSymmDiffList_edge_iff_countP_mod F L (p f)
    have hparM := faceSymmDiffList_edge_iff_countP_mod F M (p f)
    simp_all
  rcases Finset.mem_symmDiff.mp hfD with ⟨hfL, hfM⟩ | ⟨hfM, hfL⟩
  · 
    
    
    have hcardL : CL.card = (CL.erase f).card + 1 := by
      grind
    have hcardM : CM.card = (CM.erase f).card := by
      rw [Finset.erase_eq_of_notMem (by
                                       grind)]
    rw [← herase] at hcardM
    omega
  · 
    
    
    have hcardM : CM.card = (CM.erase f).card + 1 := by
      grind
    have hcardL : CL.card = (CL.erase f).card := by
      rw [Finset.erase_eq_of_notMem (by
                                       grind)]
    rw [← herase] at hcardM
    omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
