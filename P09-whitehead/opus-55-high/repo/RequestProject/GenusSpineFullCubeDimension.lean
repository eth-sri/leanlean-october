import RequestProject.GenusCubicalBoundaryCollapse
import RequestProject.GenusFullCubeMarking
import RequestProject.OrderThreeNormalization
import RequestProject.Tac


/-! The actual marked-spine image is supported in quotient cube dimension at most two. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineToFullCube_face_dimension f :
    ((markedSpineToFullCube q).onF f).1.2.2.spx.card ≤ 2 :=
  genusSpineCellToOld_dimension_le_two q f.1.1.2.2

/-- Every actual finite old-spine face chain maps into full-cube triangles whose top
cube has dimension at most two. -/
theorem markedSpineToFullCube_chain_dimension d
    t
    (ht : t ∈ (chain2 (markedSpineToFullCube q) d).support) :
    t.1.2.2.spx.card ≤ 2 := by
  classical
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  exact markedSpineToFullCube_face_dimension q f

/-- Normalization preserves the actual maximum cube dimension of the marked-spine image. -/
theorem markedSpineToFullCube_normalized_dimension d
    t
    (ht : t ∈ (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)).support) :
    t.1.2.2.spx.card ≤ 2 := by
  classical
  by_contra hdim
  have hzero : normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
    rwd [normalizeOrdChain2, Finsupp.linearCombination_apply, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hn : normalizeOrdTriangle a t = 0 := by
      unfold normalizeOrdTriangle
      split_ifs with h
      · by_cases he : ⟨a.1, h⟩ = t
        · have hd := markedSpineToFullCube_chain_dimension q d a ha
          grind
        simp_all
      · simp
    simp_all
  simp_all
