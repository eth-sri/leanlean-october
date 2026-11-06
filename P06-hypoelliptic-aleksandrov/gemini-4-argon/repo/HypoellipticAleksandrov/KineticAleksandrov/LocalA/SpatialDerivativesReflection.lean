module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesForward
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderReflection
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource

/-! # Reflection preserves spatial derivative norms and the literal cylinder oscillation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/- The backward source data become exactly the local forward homogeneous solution class. -/
theorem spatial_slice_reflection {d } (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    physicalPositionSlice u P =
      physicalPositionSlice (u ∘ kineticReflection) (kineticReflection P) ∘ Neg.neg := by
  funext x
  simp only [physicalPositionSlice, Function.comp_apply, kineticReflection, neg_neg]

/- The stipulated spatial derivative norm is unchanged by reflection, at every order. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
