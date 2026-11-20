module

public import RequestProject.GenusCubicalBoundaryCollapse
public import RequestProject.GenusFullCubeMarking
public import RequestProject.OrderNormalizationSupport

@[expose] public section

/-! The actual marked-spine image is supported in quotient cube dimension at most two. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineToFullCube_normalized_dimension (d : (markedSpineCx q).F →₀ ℤ)
    (t : StrictOrdTri (QCube (cmpRel (GenusVertex q))))
    (ht : t ∈ (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)).support) :
    t.1.2.2.spx.card ≤ 2 := by
  obtain ⟨f, _, h⟩ := normalizeOrdChain2_image_support _ _ ht
  rw [← h]
  exact genusSpineCellToOld_dimension_le_two q f.1.1.2.2

/-- The normalized image has no coefficient through the removed positive vertex. -/
theorem markedSpineToFullCube_normalized_zero_at_origin (d : (markedSpineCx q).F →₀ ℤ)
    (t : StrictOrdTri (QCube (cmpRel (GenusVertex q))))
    (ht : t.1.1.spx = ∅ ∧ t.1.1.sgn = 0) :
    normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
  by_contra h
  obtain ⟨f, _, he⟩ := normalizeOrdChain2_image_support _ _ (Finsupp.mem_support_iff.mpr h)
  rw [← he] at ht
  exact (genusSpineCellToOld q f.1.1.1).2 ht

end FiniteChains.Davis.Genus
