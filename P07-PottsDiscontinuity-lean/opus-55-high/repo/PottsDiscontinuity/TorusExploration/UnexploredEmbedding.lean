module

public import PottsDiscontinuity.TorusExploration.UnexploredCylinder
public import PottsDiscontinuity.TorusExploration.PlanarLiftEdges

/-! The full unexplored cylinder embeds in the planar rotated lattice. -/

public section

namespace PottsDiscontinuity.TorusExploration
open Torus CorrLength
variable {N M : ℕ}

/-- The lift as an injective map of the entire finite vertex carrier. -/
def potentialLiftEmbedding (hN : Even N) (F : FaceVertex N M true → ℤ) :
    FaceVertex N M true ↪ RotatedVertex :=
  ⟨potentialLift hN F,potentialLift_injective hN F⟩

section
variable (hN : Even N) (hM : Even M)
theorem potentialLift_adj (A : RCConfig N M)
    (F : FaceVertex N M true → ℤ)
    (hF : ∀ e : OpenDiamondEdge A,
      F (faceEndpoint hN hM true e.val true) - F (faceEndpoint hN hM true e.val false) =
        integerSeamCrossX e.val)
    (hseam : ∀ e : OpenDiamondEdge A, e.val.2.val ≠ 0)
    {u v : FaceVertex N M true} (huv : (diamondOpenGraph hN hM true A).Adj u v) :
    rotatedLattice.Adj (potentialLift hN F u) (potentialLift hN F v) := by
  obtain ⟨⟨e,he,hep⟩,_⟩ := huv
  have h := potentialLift_edge_adj hN hM A F hF ⟨e,he⟩ (hseam ⟨e,he⟩)
  rcases Sym2.eq_iff.1 hep with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · omega
  tauto

/-- No extra topology hypothesis: the entire remaining cylinder graph embeds
in the plane after the first bottom-to-top cluster has been exposed. -/
theorem exists_unexploredCylinder_embedding (hNp : 0 < N) (hMlarge : 1 < M) {A : RCConfig N M}
    {u v : FaceVertex N M true} (hu : u.val.2.val=0) (hv : v.val.2.val+1=M)
    (hp : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).Reachable u v) :
    ∃ f : FaceVertex N M true ↪ RotatedVertex,
      (∀ w, (f w).val.2 = (w.val.2.val : ℤ)) ∧
      ∀ a b, (diamondOpenGraph hN hM true (unexploredCylinderConfig hN hM A u)).Adj a b →
        rotatedLattice.Adj (f a) (f b) := by
  obtain ⟨F,hF⟩ := unexploredCylinder_integerPotential hN hM hNp hMlarge hu hv hp
  refine ⟨potentialLiftEmbedding hN F,fun _ => rfl,?_⟩
  intro a b hab
  apply potentialLift_adj hN hM _ F hF _ hab
  grind [unexploredCylinderConfig]
end

end PottsDiscontinuity.TorusExploration
