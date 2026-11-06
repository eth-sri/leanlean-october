module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import Mathlib.Tactic

/-! # Compact minimum of the positive Bellman image and its global homogeneous bound -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/- Normalizing a punctured point by its literal gauge puts it on the source sphere. -/
def bellmanSpherePoint (q ) (hq : q ∈ bellmanPuncturedSet) : BellmanSphere :=
  ⟨bellmanPlaneDilation (bellmanGauge q)⁻¹ q, by
    rw [bellmanGauge_dilation _ (inv_pos.mpr (bellmanGauge_pos q hq)),
      inv_mul_cancel₀ (bellmanGauge_pos q hq).ne']⟩

/- Dilating the normalized sphere point by its gauge recovers the original point. -/
end HypoellipticAleksandrov.KineticAleksandrov
