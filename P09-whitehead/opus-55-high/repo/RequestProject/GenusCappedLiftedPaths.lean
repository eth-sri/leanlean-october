import RequestProject.GenusCappedRootedGauge
import RequestProject.GenusCappedSpine
import RequestProject.TreeCover
import RequestProject.Tac


/-! Exact lifted-path comparison between the capped tree cover and the full cube cover. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def rootedCappedEdgeGerm
    (z : (PresGroup (cappedSpinePresentation q) × (markedSpineCx q).E) × Bool) :=
  (rootedCappedFullEdge q z.1.1 z.1.2, z.2)

/-- Comparison of an oriented lifted edge, including reverse traversal. -/
theorem rootedCapped_liftGerm (g : PresGroup (cappedSpinePresentation q))
    (eb : (markedSpineCx q).E × Bool) :
    rootedCappedEdgeGerm q
      (SpanningTree.liftGerm (cappedSpineTree q) (relSub (cappedSpinePresentation q)) g eb) =
      Comb.liftGerm (rootedCappedFullVertex q g
        (gSrcX (markedSpineCx q) eb))
        ((markedSpineToFullCube q).onE eb.1, eb.2)
        (by rw [rootedCappedFullVertex_end, germSrc_onE]) := by
  cases' eb with e b
  cases b with
  | true => rfl
  | false =>
      have h := rootedCappedFullVertex_path q g
        (isPath_single (X := markedSpineCx q) (e, false))
      have he : extend ((markedSpineToFullCube q).onE e, false)
          (rootedCappedFullVertex q g ((markedSpineCx q).tgt e)) =
          rootedCappedFullVertex q
            (g * QuotientGroup.mk (SpanningTree.germWord _ (e, false)))
            ((markedSpineCx q).src e) := by
        simp_all [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil, SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, ite_false, Bool.false_eq_true]
      aesop

/-- The comparison sends the entire genuine tree-cover lift to the actual path-class lift. -/
theorem rootedCapped_liftPath (g : PresGroup (cappedSpinePresentation q))
    {a b} {p}
    (hp : IsPathX (markedSpineCx q) p a b) :
    (SpanningTree.liftK (cappedSpineTree q) (relSub (cappedSpinePresentation q)) p g).map
      (rootedCappedEdgeGerm q) =
      uLiftPath (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) := by
  induction p generalizing a g with
  | nil => rfl
  | cons eb p ih =>
      cases' hp with ha hp
      subst a
      have hs : endV (rootedCappedFullVertex q g
          (gSrcX (markedSpineCx q) eb)) =
          germSrc (orderCx (QCube (cmpRel _))).src
            (orderCx (QCube (cmpRel _))).tgt
            ((markedSpineToFullCube q).onE eb.1, eb.2) := by
        rw [rootedCappedFullVertex_end, germSrc_onE]
      have he : extend ((markedSpineToFullCube q).onE eb.1, eb.2)
          (rootedCappedFullVertex q g
            (gSrcX (markedSpineCx q) eb)) =
          rootedCappedFullVertex q
            (g * QuotientGroup.mk (SpanningTree.germWord _ eb))
            (gTgtX (markedSpineCx q) eb) := by
        have h := rootedCappedFullVertex_path q g (isPath_single (X := markedSpineCx q) eb)
        simp_all [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil, SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, ite_false, Bool.false_eq_true]
      change rootedCappedEdgeGerm q (SpanningTree.liftGerm _ _ g eb) :: _ =
        uLiftPath (((markedSpineToFullCube q).onE eb.1, eb.2) ::
          mapPath (markedSpineToFullCube q) p) _
      rw [uLiftPath_cons hs, he]
      apply congrArg₂ List.cons
      · exact rootedCapped_liftGerm q g eb
      tauto
