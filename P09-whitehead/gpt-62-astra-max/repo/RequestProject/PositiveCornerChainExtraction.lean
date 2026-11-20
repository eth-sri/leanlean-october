module

public import RequestProject.PositiveCornerLink
public import RequestProject.MinimalCornerChains
public import RequestProject.SurfaceFullCubeConeChains

@[expose] public section

/-! Actual surface chains extracted from the restored positive corner. -/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

def cornerSurfaceMap :=
  orderCxMap (positiveCornerLinkEquiv A) (positiveCornerLinkEquiv A).monotone

def cornerSurfaceChain2 :
    ((orderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] ((orderCx (NeSpx A)).E →₀ ℤ) :=
  (chain1 (cornerSurfaceMap A)).comp (cornerChain2 (positiveCorner A))

def cornerSurfaceChain3 :=
  (chain2 (cornerSurfaceMap A)).comp (cornerChain3 (positiveCorner A))

/-- The extracted corner of a full-cube three-boundary is an actual surface boundary. -/
theorem cornerSurfaceChain2_ordBoundary3 (c : OrdTet (QCube A) →₀ ℤ) :
    cornerSurfaceChain2 A (ordBoundary3 c) =
      -Comb.bdry2 (orderCx (NeSpx A)) (cornerSurfaceChain3 A c) := by
  change chain1 (cornerSurfaceMap A) (cornerChain2 (positiveCorner A) (ordBoundary3 c)) = _
  rw [cornerChain2_ordBoundary3 _ (fun v hv => (le_positiveCorner_iff A v).mp hv), map_neg]
  rw [cornerSurfaceChain3, LinearMap.comp_apply, bdry2_chain2]

/-- Extracting the explicit cone fan recovers exactly its input surface edge chain. -/
theorem cornerSurfaceChain2_surfaceCornerFan (c : (orderCx (NeSpx A)).E →₀ ℤ) :
    cornerSurfaceChain2 A (surfaceCornerFan A c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
      have hlt : positiveCorner A < surfaceFullCube A e.1.1 :=
        (positiveCorner_lt_iff A _).mpr ⟨e.1.1.2.1, rfl⟩
      rw [surfaceCornerFan, coneEdgeChain, Finsupp.linearCombination_single, map_smul]
      change n • chain1 (cornerSurfaceMap A)
        (cornerChain2 (positiveCorner A)
          (Finsupp.single (coneEdgeTriangle (surfaceFullCube A)
            (surfaceFullCube_monotone A) (positiveCorner A)
            (positiveCorner_le_surface A) e) 1)) = _
      rw [cornerChain2, Finsupp.linearCombination_single, one_smul]
      simp_all [coneEdgeTriangle, cornerTriangleEdge, dif_pos, chain1, cornerSurfaceMap, orderCxMap, positiveCornerLinkEquiv, surfaceFullCube, posQCube]

end FiniteChains.Davis
