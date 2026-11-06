
import GS.UnitaryLocalModel.TopologyFullImage
import GS.NonmanifoldCompletion.NeighbourhoodModel




/-!
# From the full compact image to a pointed neighbourhood model

This module records the inherited-topology bookkeeping. Once the actual
full-family coverage theorem supplies the source-neighbourhood assertion,
no additional local topological premise is required on either side.
-/
namespace GS.UnitaryLocalModel

/-- View the compact image inside an ambient matrix family. -/
def fullCompactSource (F : Set (CMat (q*2)))
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) : Set F :=
  {M | M.val ∈ FullCompactImage ψ o r}

def fullCompactSourceHomeomorph (F : Set (CMat (q*2)))
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
    (hsub : FullCompactImage ψ o r ⊆ F) :
    fullCompactSource F ψ o r ≃ₜ FullCompactImage ψ o r where
  toFun := fun x => ⟨x.val.val,x.property⟩
  invFun := fun y => ⟨⟨y.val,hsub y.property⟩,y.property⟩
  left_inv := by tauto
  right_inv := by tauto
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The bounded factor is a neighbourhood within the whole rank cone. -/
def outerConeRegion (q d : ℕ) (o : Fin q) (r : ℝ) :
    Set (OuterFactors q o × ConeCoordinates d) :=
  {p | p.2 ∈ boundedConeCoordinates d r}

def outerBoundedHomeomorph (q d : ℕ) (o : Fin q) (r : ℝ) :
    (OuterFactors q o × boundedConeCoordinates d r) ≃ₜ outerConeRegion q d o r where
  toFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
  invFun := fun p => (p.val.1,⟨p.val.2,p.property⟩)
  left_inv := by tauto
  right_inv := by tauto
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop




end GS.UnitaryLocalModel
