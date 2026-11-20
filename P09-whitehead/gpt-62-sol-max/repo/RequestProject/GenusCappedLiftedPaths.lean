module

public import RequestProject.GenusCappedRootedGauge
public import RequestProject.GenusCappedSpine
public import RequestProject.TreeCover

@[expose] public section

/-! Exact lifted-path comparison between the capped tree cover and the full cube cover. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def rootedCappedEdgeGerm
    (z : (PresGroup (cappedSpinePresentation q) × (markedSpineCx q).E) × Bool) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) × Bool :=
  (rootedCappedFullEdge q z.1.1 z.1.2, z.2)

/-- The comparison sends the entire genuine tree-cover lift to the actual path-class lift. -/
theorem rootedCapped_liftPath (g : PresGroup (cappedSpinePresentation q))
    {a b : (markedSpineCx q).V} {p : List ((markedSpineCx q).E × Bool)}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    (SpanningTree.liftK (cappedSpineTree q) (relSub (cappedSpinePresentation q)) p g).map
      (rootedCappedEdgeGerm q) =
      uLiftPath (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) := by
  let T := cappedSpineTree q
  let N := relSub (cappedSpinePresentation q)
  let hN : ∀ f, SpanningTree.treeRel T f ∈ N := by
    erw [cappedSpineTree_rel]; exact rel_mem_relSub _
  have he := map_eq_uLiftPath (K := SpanningTree.treeCover T N hN)
    (fun x => rootedCappedFullVertex q x.1 x.2) (fun x => rootedCappedFullEdge q x.1 x.2)
    (fun _ => rfl) (fun e => by
      have h := rootedCappedFullVertex_path q e.1 (isPath_single (X := markedSpineCx q) (e.2, true))
      change extend ((markedSpineToFullCube q).onE e.2, true)
        (rootedCappedFullVertex q e.1 ((markedSpineCx q).src e.2)) =
        rootedCappedFullVertex q (e.1 * QuotientGroup.mk ((markedSpineTree q).germWord (e.2, true)))
          ((markedSpineCx q).tgt e.2)
      simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
        SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, QuotientGroup.mk_mul,
        QuotientGroup.mk_one, germSrc_true, germTgt_true] using h)
    (SpanningTree.liftK_isPath (T := T) (N := N) hp g)
  change _ = uLiftPath ((SpanningTree.liftK T N p g).map fun e =>
    ((markedSpineToFullCube q).onE e.1.2, e.2)) _ at he
  refine he.trans (congrArg (fun l => uLiftPath l _) ?_)
  simpa only [List.map_map, Function.comp_def, mapPath] using
    congrArg (List.map fun d : (markedSpineCx q).E × Bool => ((markedSpineToFullCube q).onE d.1, d.2))
      (SpanningTree.map_liftK (T := T) (N := N) p g)

end FiniteChains.Davis.Genus
