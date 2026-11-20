module

public import PottsDiscontinuity.CorrLength.RotatedFreeLimit
public import PottsDiscontinuity.TorusRC.FiniteConnectionTransport
public import PottsDiscontinuity.TorusRC.LiftedBoxes

/-! # Comparison of rotated-lattice image boxes with native lifted square boxes -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open CorrLength FK

/-- An image box of radius r lies in the native square of radius 2r. -/
theorem squareBox_mem_liftedBox (r R : ℕ) (hR : 2*r ≤ R)
    (v : BoxVertex (0,0) r) : inLiftedBox R rotatedLatticeOrigin (squareToRotatedVertex v.val) := by
  have hv := (mem_latticeBox (0,0) v.val r).mp v.property
  dsimp at hv
  dsimp [inLiftedBox,rotatedLatticeOrigin,squareToRotatedVertex]
  constructor <;> apply abs_le.mpr <;> constructor <;> omega

/-- The original square-lattice coordinates, embedded in the actual native
rotated square; this retains the induced graph and every sampled edge. -/
def squareBoxToLiftedBox (r R : ℕ) (hR : 2*r ≤ R) :
    BoxVertex (0,0) r ↪ LiftedBoxVertex rotatedLatticeOrigin R where
  toFun v := ⟨squareToRotatedVertex v.val,squareBox_mem_liftedBox r R hR v⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    have hh := congrArg (fun z : LiftedBoxVertex rotatedLatticeOrigin R =>
      rotatedToSquareVertex z.val) h
    simpa only [rotatedToSquare_squareToRotated] using hh

theorem squareBoxGraph_map_le_liftedBox (r R : ℕ) (hR : 2*r ≤ R) :
    (boxGraph (0,0) r).map (squareBoxToLiftedBox r R hR) ≤
      liftedBoxGraph rotatedLatticeOrigin R := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := hxy
  change rotatedLattice.Adj (squareToRotatedVertex u.val) (squareToRotatedVertex v.val)
  rw [rotatedLattice_adj_iff_square,rotatedToSquare_squareToRotated,rotatedToSquare_squareToRotated]
  exact huv

noncomputable section

local instance squareBoxComparisonEdgeFintype (r : ℕ) : Fintype (boxGraph (0,0) r).edgeSet :=
  Fintype.ofFinite _
local instance nativeBoxComparisonEdgeFintype (R : ℕ) :
    Fintype (liftedBoxGraph rotatedLatticeOrigin R).edgeSet := Fintype.ofFinite _

/-- Every finite square-box connection probability is dominated by the
native lifted-box free law once the image box fits. -/
theorem squareBox_connection_probability_le_native (θ : Parameters)
    (r R : ℕ) (hR : 2*r ≤ R) (u v : BoxVertex (0,0) r) :
    torusRCFiberEventProbability (law (boxGraph (0,0) r) θ (BoundaryCondition.free ∅))
      {A | ActualConnected (boxGraph (0,0) r) A u v} ≤
    liftedBoxFreeConnectionProbability θ rotatedLatticeOrigin R
      (squareToRotatedVertex u.val) (squareToRotatedVertex v.val) := by
  classical
  let G := boxGraph (0,0) r
  let H := liftedBoxGraph rotatedLatticeOrigin R
  let f := squareBoxToLiftedBox r R hR
  let hGH := squareBoxGraph_map_le_liftedBox r R hR
  let E := {A | ActualConnected G A u v}
  let F : Configuration G → ℝ := E.indicator (fun _ => 1)
  refine (embedded_free_expectation_le G H f hGH θ ∅ ∅ F
    (Set.indicator_nonneg fun _ _ => zero_le_one)
    (event_indicator_monotone (fun _ _ hAB hA => actualConnected_mono hAB hA))).trans ?_
  apply FiniteProbability.expectation_mono
  intro A
  change E.indicator _ _ ≤ (liftedBoxFreeConnectionEvent rotatedLatticeOrigin R
    (squareToRotatedVertex u.val) (squareToRotatedVertex v.val)).indicator _ _
  rw [← Set.indicator_comp_right (embeddedConfigurationRestriction G H f hGH)]
  exact Set.indicator_le_indicator_apply_of_subset (fun B hB =>
    ⟨squareBox_mem_liftedBox r R hR u, squareBox_mem_liftedBox r R hR v,
      actualConnected_embeddedRestriction f hGH B u v hB⟩) zero_le_one

end
end PottsDiscontinuity.TorusRC
