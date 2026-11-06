import RequestProject.GenusUniversalReferenceCorrection
import RequestProject.GenusPolygonBoundaryWord
import RequestProject.LiftedWordFoxChains
import RequestProject.Tac


/-! The explicit degree-one polygon has exactly the prescribed named Fox
boundary in the original universal old cover. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Comb
universe u v
theorem wordPath_map_values {a} {b} {I}
    f (p : I → Loop X a) (r : I → Loop Y b)
    (hr : ∀ i, (r i).1 = mapPath f (p i).1) l :
    wordPath r l = mapPath f (wordPath p l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      cases' x with i t
      cases t <;> simp only [wordPath_cons, germLoopPath_pos, germLoopPath_neg,
        hr, ih, mapPath_append, mapPath_revPath]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def universalOldSurfaceLoop (i : Fin q × Bool) :
    Loop (spineOldCx q) (universalSpineOldBase q) :=
  ⟨surfaceOldMarking q i, by
    rwd [universalSpineOldBase_eq]
    exact surfaceOldMarking_isPath q i⟩

theorem universalSpineOldReceiver_marked i :
    universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      Pi1.mk (universalOldSurfaceLoop q i) := by
  rwd [← namedSpinePi1Equiv_marked q i]
  change pi1Map _ _
    ((namedSpinePi1Equiv q).symm
      ((namedSpinePi1Equiv q) (Pi1.mk (treeMarkedSpineLoop q i)))) = _
  rwd [MulEquiv.symm_apply_apply]
  apply Quotient.sound
  change Htpy _ (universalSpineOldBase q) (universalSpineOldBase q)
    (mapPath (universalSpineToOld q) (treeMarkedSpineLoop q i).1) (surfaceOldMarking q i)
  rwd [universalSpine_marking_path, universalSpineOldBase_eq]
  exact spineMarkedLoop_toOld_htpy q i

/-- Internal generators do not occur in the polygon word. Representatives
are chosen only to apply the general word-chain dictionary on the full named
alphabet; the marked loops remain the original explicit surface paths. -/
def universalOldNamedLoop : NamedSpineGen q → Loop (spineOldCx q) (universalSpineOldBase q)
  | .inl z => Classical.choose (Quotient.exists_rep
      (universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))
  | .inr i => universalOldSurfaceLoop q i

theorem universalOldNamedLoop_class a :
    universalSpineOldReceiver q (qof (relSub (namedSpinePresentation q)) a) =
      Pi1.mk (universalOldNamedLoop q a) := by
  cases a with
  | inl z => exact (Classical.choose_spec (Quotient.exists_rep
      _)).symm
  | inr i => exact universalSpineOldReceiver_marked q i

theorem universalOldNamedLoop_polygon_word :
    wordPath (universalOldNamedLoop q)
      (genusNamedSurfaceLetters (I := SpinePresentationGen q) q) =
    mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
  simp [genusNamedSurfaceLetters, wordPath_map_letters, wordPath_map_values _ (finiteMarkedLoops q)
    (fun i => universalOldNamedLoop q (Sum.inr i)) (by aesop), genusSurfaceLetters_wordPath]

theorem universalPolygonFoxCoordinates :
    (coords (relSub (namedSpinePresentation q)) (NamedSpineGen q)).symm
      (fun a => proj (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q))) =
    Finsupp.mapDomain
      (fun x => (x.1, Sum.inr x.2))
      (universalReferenceMarkingCoefficients q) := by
  apply (coords _ _).injective
  rwd [LinearEquiv.apply_symm_apply]
  funext a
  ext g
  cases a with
  | inl z =>
      rwd [namedSpineSurfaceWord_fox_internal, map_zero, Finsupp.zero_apply,
        Finsupp.mapDomain_notin_range]
      simp
  | inr i =>
      have hinj : Function.Injective
          (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
            (x.1, Sum.inr (α := SpinePresentationGen q) x.2)) := by
        intro x y h
        grind
      erw [Finsupp.mapDomain_apply_of_injective hinj (a := (g, i))]
      rfl

theorem universalOldNamedLoop_chainMap_marked
    (c : PresGroup (namedSpinePresentation q) × (Fin q × Bool) →₀ ℤ) :
    loopCoefficientChainMap (relSub (namedSpinePresentation q))
      (universalOldNamedLoop q) (universalSpineOldReceiver q)
      (Finsupp.mapDomain (fun x => (x.1, Sum.inr x.2)) c) =
    universalSurfaceMarkingChains q c := by
  lin_ind c with c d hc hd => simp [Finsupp.mapDomain_add, map_add, hc, hd]
  | x n =>
      simp [Finsupp.mapDomain_single, loopCoefficientChainMap,
        universalSurfaceMarkingChains, Finsupp.linearCombination_single,
        universalOldNamedLoop, universalOldSurfaceLoop, loopCoefficientVertex]

/-- No degree or boundary hypothesis is left: the explicitly constructed
polygon boundary is exactly the original named surface Fox gradient. -/
theorem universalOldPolygonChain_boundary_marked :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      universalSurfaceMarkingChains q (universalReferenceMarkingCoefficients q) := by
  rwd [universalOldPolygonChain_boundary, ← universalOldNamedLoop_polygon_word]
  rwd [lifted_wordPath_fox _
    _ _ (universalOldNamedLoop_class q)]
  rwd [genusNamedSurfaceLetters_mk]
  rwd [universalPolygonFoxCoordinates, universalOldNamedLoop_chainMap_marked]
