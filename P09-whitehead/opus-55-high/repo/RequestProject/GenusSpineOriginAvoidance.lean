import RequestProject.GenusSpineFullCubeDimension
import RequestProject.Tac


/-! The actual old-spine chain image avoids the removed positive vertex. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineToFullCube_face_avoids_origin f :
    ¬ (((markedSpineToFullCube q).onF f).1.1.spx = ∅ ∧
      ((markedSpineToFullCube q).onF f).1.1.sgn = 0) :=
  (genusSpineCellToOld q f.1.1.1).2

theorem markedSpineToFullCube_chain_avoids_origin d
    t
    (ht : t ∈ (chain2 (markedSpineToFullCube q) d).support) :
    ¬ (t.1.1.spx = ∅ ∧ t.1.1.sgn = 0) := by
  classical
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  exact markedSpineToFullCube_face_avoids_origin q f

/-- Normalization creates no coefficient at a flag through the removed positive vertex. -/
theorem markedSpineToFullCube_normalized_zero_at_origin d
    t
    (ht : t.1.1.spx = ∅ ∧ t.1.1.sgn = 0) :
    normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) t = 0 := by
  classical
  rwd [normalizeOrdChain2, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hn : normalizeOrdTriangle a t = 0 := by
    unfold normalizeOrdTriangle
    split_ifs with h
    · by_cases he : ⟨a.1, h⟩ = t
      · have hfirst := congrArg (fun x =>
          x.1.1) he
        have hnot := markedSpineToFullCube_chain_avoids_origin q d a ha
        simp_all
      simp_all
    · simp
  simp_all
