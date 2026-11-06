import Mathlib.Tactic

import RequestProject.GenusUniversalPolygonReference
import RequestProject.GenusQuotientRelativeCorrection
import RequestProject.GenusNormalizedSpineFoxFilling

/-! The pre-substitution correction uses precisely the old marking corrections
already used after substitution. Pending final Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem universalOldBasePath :
    IsPath (spineOldCx q).src (spineOldCx q).tgt []
      (universalSpineOldBase q) (spineOldBase q) := universalSpineOldBase_eq q

def universalOldBaseTransport  :=
  uCoverPathTransport (universalOldBasePath q)

theorem universalOldBaseTransport_base :
    (universalOldBaseTransport q).onV (UV.base (spineOldCx q) (spineOldBase q)) =
      UV.base (spineOldCx q) (universalSpineOldBase q) := rfl

def universalSpineMarkingChains :
    ((PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (spineOldCx q) (universalSpineOldBase q)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath (spineOldMarking q x.2)
    (deckV (universalSpineOldReceiver q x.1) (UV.base (spineOldCx q) (universalSpineOldBase q)))))

def universalSurfaceMarkingChains :
    ((PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (spineOldCx q) (universalSpineOldBase q)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath (surfaceOldMarking q x.2)
    (deckV (universalSpineOldReceiver q x.1) (UV.base (spineOldCx q) (universalSpineOldBase q)))))

variable (g : PresGroup (namedSpinePresentation q))
variable (i : Fin q × Bool)
def universalOldMarkingCorrection    :=
  (univDeck (spineOldCx q) (universalSpineOldBase q)).faceChains
    (universalSpineOldReceiver q g)
    (chain2 (universalOldBaseTransport q) (spineOldMarkingCorrection q i))

theorem universalOldMarkingCorrection_boundary
      :
    Comb.bdry2 _ (universalOldMarkingCorrection q g i) =
      pathChain (uLiftPath (spineOldMarking q i)
        (deckV (universalSpineOldReceiver q g) (UV.base (spineOldCx q) (universalSpineOldBase q)))) -
      pathChain (uLiftPath (surfaceOldMarking q i)
        (deckV (universalSpineOldReceiver q g) (UV.base (spineOldCx q) (universalSpineOldBase q)))) := by
  rw  [universalOldMarkingCorrection, DeckAction.faceChains_boundary, bdry2_chain2,
    spineOldMarkingCorrection_boundary, map_sub, map_sub]
  have hp : IsPath (spineOldCx q).src (spineOldCx q).tgt (spineOldMarking q i)
      (endV (UV.base (spineOldCx q) (universalSpineOldBase q))) (universalSpineOldBase q) := by
    rw (config := { transparency := .default }) [endV_base, universalSpineOldBase_eq]
    exact spineOldMarking_isPath q i
  have hs : IsPath (spineOldCx q).src (spineOldCx q).tgt (surfaceOldMarking q i)
      (endV (UV.base (spineOldCx q) (universalSpineOldBase q))) (universalSpineOldBase q) := by
    rw (config := { transparency := .default }) [endV_base, universalSpineOldBase_eq]
    exact surfaceOldMarking_isPath q i
  rw  [universalOldBaseTransport,
    uCoverPathTransport_pathChain _ _ (spineOldMarking_isPath q i),
    uCoverPathTransport_pathChain _ _ (surfaceOldMarking_isPath q i)]
  change chain1 ((univDeck (spineOldCx q) (universalSpineOldBase q)).cellHom
      (universalSpineOldReceiver q g))
      (pathChain (uLiftPath (spineOldMarking q i)
        ((universalOldBaseTransport q).onV (UV.base (spineOldCx q) (spineOldBase q))))) -
    chain1 ((univDeck (spineOldCx q) (universalSpineOldBase q)).cellHom
      (universalSpineOldReceiver q g))
      (pathChain (uLiftPath (surfaceOldMarking q i)
        ((universalOldBaseTransport q).onV (UV.base (spineOldCx q) (spineOldBase q))))) = _
  rw  [universalOldBaseTransport_base, univDeck_pathChain _ _ _ hp,
    univDeck_pathChain _ _ _ hs]

def universalOldMarkingCorrections :
    ((PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => universalOldMarkingCorrection q x.1 x.2)

variable (c : (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ)
theorem universalOldMarkingCorrections_boundary
     :
    Comb.bdry2 _ (universalOldMarkingCorrections q c) =
      universalSpineMarkingChains q c - universalSurfaceMarkingChains q c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw  [map_add, map_add, hc, hd, map_add, map_add]
    abel
  | single x n =>
    simp only [universalOldMarkingCorrections, universalSpineMarkingChains,
      universalSurfaceMarkingChains, Finsupp.linearCombination_single, map_smul,
      universalOldMarkingCorrection_boundary, smul_sub]

theorem universalSpine_marking_path  :
    mapPath (universalSpineToOld q) (treeMarkedSpineLoop q i).1 = spineOldMarking q i := by
  
  rw (config := { transparency := .default }) [← mapPath_comp, markedSpineLoop_inclusion]
  rfl

theorem universalSpine_receiver_root  :
    ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
      (universalSpineOldReceiver q) g (markedSpineTree q).root =
        deckV (universalSpineOldReceiver q g) (UV.base (spineOldCx q) (universalSpineOldBase q)) := by
  simp [ReceivedTree.receiverVertex, SpanningTree.mappedTreeReference]

theorem universalSpineMarkingChains_eq
     :
    chain1 (universalNamedSpineComparison q)
      (ReceivedTree.markedChainMap (markedSpineTree q) (universalSpineWordReceiver q)
        (fun i => (treeMarkedSpineLoop q i).1) c) = universalSpineMarkingChains q c := by
  simp_all [universalNamedSpineComparison, ReceivedTree.comparison_markedChainMap, ReceivedTree.geometricMarkedChainMap, universalSpineMarkingChains, universalSpine_marking_path, universalSpine_receiver_root] <;> rfl

def universalReferenceMarkingCoefficients  :=
  (ReceivedTree.cellCoordinates (Fin q × Bool)).symm (namedSpineSurfaceMarkingCoefficient q)

def universalReferenceOldChain  :=
  universalOldPolygonChain q + universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)

/-- Once the exact polygon boundary is read in marked Fox coordinates, the
prescribed old class has precisely the original received-spine boundary. -/
theorem universalReferenceOldChain_boundary
    (hpolygon : Comb.bdry2 _ (universalOldPolygonChain q) =
      universalSurfaceMarkingChains q (universalReferenceMarkingCoefficients q)) :
    Comb.bdry2 _ (universalReferenceOldChain q) =
      chain1 (universalNamedSpineComparison q)
        (ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q)) := by
  simp_all [ReceivedTree.markedChain, universalSpineMarkingChains_eq, universalReferenceOldChain, universalOldMarkingCorrections_boundary, universalReferenceMarkingCoefficients] <;> rfl

end FiniteChains.Davis.Genus
