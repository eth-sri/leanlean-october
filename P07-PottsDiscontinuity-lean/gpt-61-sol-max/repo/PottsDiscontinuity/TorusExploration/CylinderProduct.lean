module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.CylinderIndexedBridge
public import PottsDiscontinuity.TorusExploration.DistinctProduct
public import PottsDiscontinuity.TorusExploration.PlanarConnectionBound

/-! The cylinder distinct-crossing product bound with its geometric premise proved. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus FK CorrLength MeasureTheory
variable {N M : ℕ}
noncomputable section

local instance cylinderProductVertexDecidableEq : DecidableEq (FaceVertex N M true) := Classical.decEq _

/-- The source exploration estimate and its r-1-fold iteration, for arbitrary
fixed bottom and top endpoints on the seam-closed cylinder. -/
theorem cylinder_distinctConnections_le (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (x y : ℕ → FaceVertex N M true)
    (hbottom : ∀ i, (x i).val.2.val=0) (htop : ∀ i, (y i).val.2.val+1=M)
    (r : ℕ) (hr : 1 ≤ r) :
    (measure (fullCylinderGraph hN hM) θ (BoundaryCondition.free ∅)
      (distinctConnections (fullCylinderGraph hN hM) x y r)).toReal ≤
       Real.sqrt (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite (2*(M-1))))) ^(r-1) := by
  let G := fullCylinderGraph hN hM
  
  apply distinctConnections_probability_le_pow G θ x y _ (Real.sqrt_nonneg _) _ r hr
  intro j hj C hC hx hy
  
  
  obtain ⟨f,hfy,hf⟩ := multiComplement_embedding hN hM (by omega) (by omega) G
    le_rfl C (cylinderIndexedConfiguration hN hM hN4 hM4 C) (openGraph_cylinderIndexedConfiguration hN hM hN4 hM4 C)
    (prefixSeeds x j) (Finset.mem_image.2 ⟨0,Finset.mem_range.2 (by omega),rfl⟩) (hbottom 0) (htop 0) (hC.1 0 (by omega))
  
  
  
  exact Real.le_sqrt_of_sq_le (finiteFree_connectivity_sq_le_diagonal (G.induce (actualMultiClusterComplementSet G (prefixSeeds x j) C)) θ μ hμ f hf
    ⟨x j,hx⟩ ⟨y j,hy⟩ (M-1) (by
                               grind))

end
end PottsDiscontinuity.TorusExploration
