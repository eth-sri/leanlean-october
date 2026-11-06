import Mathlib.Tactic

import RequestProject.GenusCubicalBoundaryCollapse
import RequestProject.GenusFullCubeMarking
import RequestProject.OrderThreeNormalization

/-! The actual marked-spine image is supported in quotient cube dimension at most two. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev markedSpineToFullCube_face_dimension (f : (markedSpineCx q).F)  :=
  genusSpineCellToOld_dimension_le_two q f.1.1.2.2

variable (d : (markedSpineCx q).F →₀ ℤ)
/-- Every actual finite old-spine face chain maps into full-cube triangles whose top
cube has dimension at most two. -/
theorem markedSpineToFullCube_chain_dimension 
    (t : (orderCx (QCube (cmpRel (GenusVertex q)))).F)
    (ht : t ∈ (chain2 (markedSpineToFullCube q) d).support) :
    t.1.2.2.spx.card ≤ 2 := by
  classical
  
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  exact markedSpineToFullCube_face_dimension q f

/-- Normalization preserves the actual maximum cube dimension of the marked-spine image. -/
theorem markedSpineToFullCube_normalized_dimension 
    (t : StrictOrdTri (QCube (cmpRel (GenusVertex q))))
    (ht : t ∈ (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)).support) :
    t.1.2.2.spx.card ≤ 2 := by
  classical
  by_contra hdim
  have hzero : normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
    rw  [normalizeOrdChain2, Finsupp.linearCombination_apply, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hn : normalizeOrdTriangle a t = 0 := by
      unfold normalizeOrdTriangle
      split_ifs with h
      · by_cases he : (⟨a.1, h⟩ : StrictOrdTri _) = t
        · have hd := markedSpineToFullCube_chain_dimension q d a ha
          have htop := congrArg (fun x : StrictOrdTri (QCube (cmpRel (GenusVertex q))) =>
            x.1.2.2) he
          change a.1.2.2 = t.1.2.2 at htop
          rw  [htop] at hd
          exact False.elim (hdim hd)
        · simp [he]
      · simp
    change (((chain2 (markedSpineToFullCube q) d) a) • normalizeOrdTriangle a) t = 0
    rw  [Finsupp.smul_apply, hn, smul_zero]
  exact Finsupp.mem_support_iff.mp ht hzero

end FiniteChains.Davis.Genus
