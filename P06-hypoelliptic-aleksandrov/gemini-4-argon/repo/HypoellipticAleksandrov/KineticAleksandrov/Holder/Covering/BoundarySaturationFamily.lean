module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DensityDefect
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageVolume
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-! # The literal family of critical cylinders and its measure reduction -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/- Critical cylinders have exactly the prescribed density and lie inside Q. -/
def criticalParameters {d } (E : Set (KineticPoint d)) (eta : ℝ) :
    Set (KineticPoint d × ℝ) :=
  {z | 0 < z.2 ∧ backwardCylinder z.1 z.2 ⊆ unitCylinder d ∧
    (volume (E ∩ backwardCylinder z.1 z.2)).toReal =
      (1-eta)*(volume (backwardCylinder z.1 z.2)).toReal}

/- The open union of all critical cylinders. -/
def criticalUnion {d } (E : Set (KineticPoint d)) (eta : ℝ) : Set (KineticPoint d) :=
  ⋃ z ∈ criticalParameters E eta, backwardCylinder z.1 z.2

/- The critical union is open. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
