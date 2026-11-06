import Mathlib.Tactic

import RequestProject.GenusUniversalReferenceCorrection
import RequestProject.GenusPolygonBoundaryWord
import RequestProject.LiftedWordFoxChains

/-! The explicit degree-one polygon has exactly the prescribed named Fox
boundary in the original universal old cover. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
theorem wordPath_map_values {X Y : Complex2.{u}} {a : X.V} {b : Y.V} {I : Type v}
    (f : Hom X Y) (p : I → Loop X a) (r : I → Loop Y b)
    (hr : ∀ i, (r i).1 = mapPath f (p i).1) (l : List (I × Bool)) :
    wordPath r l = mapPath f (wordPath p l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨i, t⟩ := x
      cases t <;> simp [hr, ih, mapPath_revPath]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def universalOldSurfaceLoop (i : Fin q × Bool) :
    Loop (spineOldCx q) (universalSpineOldBase q) :=
  ⟨surfaceOldMarking q i, by
    rw (config := { transparency := .default }) [universalSpineOldBase_eq]
    exact surfaceOldMarking_isPath q i⟩

theorem universalSpineOldReceiver_marked (i : Fin q × Bool) :
    universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      Pi1.mk (universalOldSurfaceLoop q i) := by
  rw (config := { transparency := .default }) [← namedSpinePi1Equiv_marked q i]
  change pi1Map (universalSpineToOld q) (markedSpineTree q).root
    ((namedSpinePi1Equiv q).symm
      ((namedSpinePi1Equiv q) (Pi1.mk (treeMarkedSpineLoop q i)))) = _
  rw  [MulEquiv.symm_apply_apply]
  apply Quotient.sound
  change Htpy (spineOldCx q) (universalSpineOldBase q) (universalSpineOldBase q)
    (mapPath (universalSpineToOld q) (treeMarkedSpineLoop q i).1) (surfaceOldMarking q i)
  rw  [universalSpine_marking_path, universalSpineOldBase_eq]
  exact spineMarkedLoop_toOld_htpy q i

/-- Internal generators do not occur in the polygon word. Representatives
are chosen only to apply the general word-chain dictionary on the full named
alphabet; the marked loops remain the original explicit surface paths. -/
def universalOldNamedLoop : NamedSpineGen q → Loop (spineOldCx q) (universalSpineOldBase q)
  | .inl z => Classical.choose (Quotient.exists_rep
      (universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))
  | .inr i => universalOldSurfaceLoop q i

theorem universalOldNamedLoop_class (a : NamedSpineGen q) :
    universalSpineOldReceiver q (qof (relSub (namedSpinePresentation q)) a) =
      Pi1.mk (universalOldNamedLoop q a) := by
  cases a with
  | inl z => exact (Classical.choose_spec (Quotient.exists_rep
      (universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))).symm
  | inr i => exact universalSpineOldReceiver_marked q i

theorem universalOldNamedLoop_polygon_word :
    wordPath (universalOldNamedLoop q)
      (genusNamedSurfaceLetters (I := SpinePresentationGen q) q) =
    mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
  rw  [genusNamedSurfaceLetters, wordPath_map_letters]
  rw  [wordPath_map_values (surfCx (cmpRel (GenusVertex q))) (finiteMarkedLoops q)
    (fun i => universalOldNamedLoop q (Sum.inr i)) (fun _ => rfl)]
  rw  [genusSurfaceLetters_wordPath]

theorem universalPolygonFoxCoordinates :
    (coords (relSub (namedSpinePresentation q)) (NamedSpineGen q)).symm
      (fun a => proj (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q))) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) => (x.1, Sum.inr x.2))
      (universalReferenceMarkingCoefficients q) := by
  apply (coords (relSub (namedSpinePresentation q)) (NamedSpineGen q)).injective
  rw  [LinearEquiv.apply_symm_apply]
  funext a
  ext g
  rw  [coords_apply]
  cases a with
  | inl z =>
      simp_all [FiniteChains.Davis.Genus.namedSpineSurfaceWord_fox_internal, Finsupp.mapDomain_notin_range]
  | inr i =>
      have hinj : Function.Injective
          (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
            (x.1, Sum.inr (α := SpinePresentationGen q) x.2)) := by
        intro x y h
        exact Prod.ext
          (congrArg (fun z : PresGroup (namedSpinePresentation q) × NamedSpineGen q => z.1) h)
          (Sum.inr.inj (congrArg
            (fun z : PresGroup (namedSpinePresentation q) × NamedSpineGen q => z.2) h))
      erw [Finsupp.mapDomain_apply_of_injective hinj (a := (g, i))]
      rw (config := { transparency := .default }) [← ReceivedTree.cellCoordinates_apply (Fin q × Bool)
        (universalReferenceMarkingCoefficients q) i g]

theorem universalOldNamedLoop_chainMap_marked
    (c : PresGroup (namedSpinePresentation q) × (Fin q × Bool) →₀ ℤ) :
    loopCoefficientChainMap (relSub (namedSpinePresentation q))
      (universalOldNamedLoop q) (universalSpineOldReceiver q)
      (Finsupp.mapDomain (fun x => (x.1, Sum.inr x.2)) c) =
    universalSurfaceMarkingChains q c := by
  induction c using Finsupp.induction_linear <;> simp_all [loopCoefficientChainMap, universalSurfaceMarkingChains, universalOldNamedLoop, universalOldSurfaceLoop, loopCoefficientVertex] <;> rfl

/-- No degree or boundary hypothesis is left: the explicitly constructed
polygon boundary is exactly the original named surface Fox gradient. -/
theorem universalOldPolygonChain_boundary_marked :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      universalSurfaceMarkingChains q (universalReferenceMarkingCoefficients q) := by
  rw  [universalOldPolygonChain_boundary, ← universalOldNamedLoop_polygon_word]
  rw  [lifted_wordPath_fox (relSub (namedSpinePresentation q))
    (universalOldNamedLoop q) (universalSpineOldReceiver q) (universalOldNamedLoop_class q)]
  rw  [genusNamedSurfaceLetters_mk]
  change loopCoefficientChainMap (relSub (namedSpinePresentation q))
    (universalOldNamedLoop q) (universalSpineOldReceiver q)
    ((coords (relSub (namedSpinePresentation q)) (NamedSpineGen q)).symm
      (fun a => proj (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q)))) = _
  rw  [universalPolygonFoxCoordinates, universalOldNamedLoop_chainMap_marked]

end FiniteChains.Davis.Genus
