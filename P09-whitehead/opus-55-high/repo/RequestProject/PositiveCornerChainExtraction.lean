import RequestProject.PositiveCornerLink
import RequestProject.MinimalCornerChains
import RequestProject.SurfaceFullCubeConeChains
import RequestProject.Tac
noncomputable section


/-! Actual surface chains extracted from the restored positive corner. -/
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

def cornerSurfaceMap :=
  orderCxMap (positiveCornerLinkEquiv A) (positiveCornerLinkEquiv A).monotone

def cornerSurfaceChain2 :
    ((orderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] ((orderCx (NeSpx A)).E →₀ ℤ) :=
  (chain1 (cornerSurfaceMap A)).comp (cornerChain2 _)

def cornerSurfaceChain3 :=
  (chain2 (cornerSurfaceMap A)).comp (cornerChain3 _)

/-- The extracted corner of a full-cube three-boundary is an actual surface boundary. -/
theorem cornerSurfaceChain2_ordBoundary3 c :
    cornerSurfaceChain2 A (ordBoundary3 c) =
      -Comb.bdry2 (orderCx (NeSpx A)) (cornerSurfaceChain3 A c) := by
  change chain1 (cornerSurfaceMap A) (cornerChain2 _ (ordBoundary3 c)) = _
  grind [cornerChain2_ordBoundary3 _ (fun v hv => (le_positiveCorner_iff A v).mp hv), map_neg, cornerSurfaceChain3, LinearMap.comp_apply, bdry2_chain2]

/-- Extracting the explicit cone fan recovers exactly its input surface edge chain. -/
theorem cornerSurfaceChain2_surfaceCornerFan c :
    cornerSurfaceChain2 A (surfaceCornerFan A c) = c := by
  lin_ind c e n =>
      have hlt : positiveCorner A < surfaceFullCube A e.1.1 :=
        (positiveCorner_lt_iff A _).mpr ⟨e.1.1.2.1, rfl⟩
      rw [surfaceCornerFan, coneEdgeChain, Finsupp.linearCombination_single, map_smul]
      change n • chain1 (cornerSurfaceMap A)
        (cornerChain2 _
          (Finsupp.single (coneEdgeTriangle _
            (surfaceFullCube_monotone A) _
            (positiveCorner_le_surface A) e) 1)) = _
      rw [cornerChain2, Finsupp.linearCombination_single, one_smul]
      have h : positiveCorner A = positiveCorner A ∧
          positiveCorner A < surfaceFullCube A e.1.1 := by simp_all
      simp_all [coneEdgeTriangle, cornerTriangleEdge, chain1, cornerSurfaceMap, orderCxMap, positiveCornerLinkEquiv, surfaceFullCube, posQCube]
