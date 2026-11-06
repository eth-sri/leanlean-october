import RequestProject.GenusUniversalPolygonFoxBoundary
import RequestProject.Tac


/-! The marked filling is selected before substitution with the geometric
class of the explicit degree-one polygon. Pending final Lean verification. -/
noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem normalizedSpineReference_exists :
    ∃ d,
      Comb.bdry2 (universalNamedSpineCover q) d =
        ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        universalNerveChain2 (universalReferenceOldChain q) =
          universalNerveChain2 (chain2 (universalNamedSpineComparison q) d) + Nerve.bdry y := by
  cases' exists_universalNamedSpine_markedFilling q with d hd
  have hz : Comb.bdry2 _ (universalReferenceOldChain q) =
      chain1 (universalNamedSpineComparison q) (Comb.bdry2 _ d) := by
    rw [hd]
    exact universalReferenceOldChain_boundary q (universalOldPolygonChain_boundary_marked q)
  obtain ⟨d', hd', y, hy, hzy⟩ := universalSpine_adjust_to_chain q d _ hz
  grind

/-- Genuine received-spine coordinates of the geometrically normalized
surface filling. This choice uses no core or substituted word. -/
def normalizedSpineReference :=
  Classical.choose (normalizedSpineReference_exists q)

theorem normalizedSpineReference_boundary :
    Comb.bdry2 (universalNamedSpineCover q) (normalizedSpineReference q) =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) :=
  (Classical.choose_spec (normalizedSpineReference_exists q)).1

theorem normalizedSpineReference_geometry :
    ∃ y ∈ Nerve.Inc (universalOldOrder q),
      universalNerveChain2 (universalReferenceOldChain q) =
        universalNerveChain2 (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q)) +
          Nerve.bdry y :=
  (Classical.choose_spec (normalizedSpineReference_exists q)).2

/-- After removing the exact old marking correction, the chosen chain
represents the actual degree-one source polygon modulo an old three-boundary. -/
theorem normalizedSpineReference_corrected_geometry :
    ∃ y ∈ Nerve.Inc (universalOldOrder q),
      universalNerveChain2
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
          universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)) =
        universalNerveChain2 (universalOldPolygonChain q) + Nerve.bdry y := by
  obtain ⟨y, hy, hzy⟩ := normalizedSpineReference_geometry q
  refine ⟨-y, (Nerve.Inc _).neg_mem hy, ?_⟩
  rw [universalReferenceOldChain, map_add] at hzy
  rw [map_sub, map_neg]
  grind
