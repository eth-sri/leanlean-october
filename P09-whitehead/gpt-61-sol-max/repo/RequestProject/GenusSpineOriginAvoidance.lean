import Mathlib.Tactic

import RequestProject.GenusSpineFullCubeDimension

/-! The actual old-spine chain image avoids the removed positive vertex. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev markedSpineToFullCube_face_avoids_origin (f : (markedSpineCx q).F)  :=
  (genusSpineCellToOld q f.1.1.1).2

variable (d : (markedSpineCx q).F →₀ ℤ)
theorem markedSpineToFullCube_chain_avoids_origin 
    (t : (orderCx (QCube (cmpRel (GenusVertex q)))).F)
    (ht : t ∈ (chain2 (markedSpineToFullCube q) d).support) :
    ¬ (t.1.1.spx = ∅ ∧ t.1.1.sgn = 0) := by
  classical
  
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  exact markedSpineToFullCube_face_avoids_origin q f

/-- Normalization creates no coefficient at a flag through the removed positive vertex. -/
theorem markedSpineToFullCube_normalized_zero_at_origin 
    (t : StrictOrdTri (QCube (cmpRel (GenusVertex q))))
    (ht : t.1.1.spx = ∅ ∧ t.1.1.sgn = 0) :
    normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
  classical
  rw  [normalizeOrdChain2, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hn : normalizeOrdTriangle a t = 0 := by
    unfold normalizeOrdTriangle
    split_ifs with h
    · by_cases he : (⟨a.1, h⟩ : StrictOrdTri _) = t
      · have hfirst := congrArg (fun x : StrictOrdTri (QCube (cmpRel (GenusVertex q))) =>
          x.1.1) he
        change a.1.1 = t.1.1 at hfirst
        have hnot := markedSpineToFullCube_chain_avoids_origin q d a ha
        rw  [hfirst] at hnot
        exact False.elim (hnot ht)
      · simp [he]
    · simp
  change (((chain2 (markedSpineToFullCube q) d) a) • normalizeOrdTriangle a) t = 0
  rw  [Finsupp.smul_apply, hn, smul_zero]

end FiniteChains.Davis.Genus
