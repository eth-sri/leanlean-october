module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityMinimum
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
import Mathlib.Tactic

/-!
# Smooth interior cutoff for the nearly full superlevel estimate

The cutoff is constructed in the existing product coordinates. Its compact support
lies in the literal kinetic cylinder, and it equals one on the closed source cap.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped MatrixOrder

/- The four coefficient conditions of the full kinetic Hölder theorem. -/
abbrev FullElliptic {d } (lam Lam : ℝ) (A : FullKineticCoefficient d) : Prop :=
  Measurable (fullKineticCoefficientAt A) ∧
  (∀ P, (fullKineticCoefficientAt A P).IsSymm) ∧
  (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
    lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) ∧
  (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
    fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))

/- A smooth compactly supported product-coordinate cutoff for the source cap. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
