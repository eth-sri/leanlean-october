module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Separability of the spatial `H¹₀` Hilbert realization

This module provides a local-use separability construction for the established
spatial `H¹₀` Hilbert carrier.  It deliberately exports neither a global
instance nor a chosen dense sequence.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped ENNReal

/-- The spatial `H¹₀` Hilbert realization is separable on every open domain. -/
noncomputable def h10HilbertGraphSeparableSpace
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) :
    TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) := by
  letI : MeasureTheory.SFinite (PDE.volumeOn Ω) := inferInstance
  letI : MeasurableSpace.CountablyGenerated (PDE.Vec d) := inferInstance
  letI : MeasureTheory.IsSeparable (PDE.volumeOn Ω) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (PDE.ScalarLp Ω (2 )) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (PDE.HilbertVectorLp Ω (2 )) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (PDE.H1HilbertAmbient Ω) :=
    WithLp.secondCountableTopology 2 _ _
  letI : SecondCountableTopology (PDE.H1HilbertGraph Ω) := inferInstance
  letI : SecondCountableTopology (H10HilbertGraph hΩ) := inferInstance
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

end HypoellipticAleksandrov.Parabolic.Dirichlet
