/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingMass
public import DOZZ.FourPoint.Fusion.MovingRootExterior
public import DOZZ.FourPoint.Fusion.MovingRootSmallBall
import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # Measurability and finiteness of the moving-mass pieces -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Exterior domination holds before taking expectations. -/
theorem fusionRootedGoodMass_le (γ α₁ α₂ α₃ : ℝ) (w u : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hw : ‖w‖ ≤ δ) (hu : ‖u‖ ≤ δ / 2) (hu1 : ‖u‖ ≤ 1) (μ : Measure ℂ) :
    fusionRootedGoodMass γ α₁ α₂ α₃ w u δ μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2))) * fusionRootedGoodMass γ α₁ α₂ α₃ 0 0 δ μ := by
  unfold fusionRootedGoodMass
  rw [← lintegral_const_mul _ (fusionRootedKernel_measurable γ α₁ α₂ α₃ 0 0)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
  exact fusionRootedKernel_exterior_le γ α₁ α₂ α₃ w u x
    (norm_ne_zero_iff.mp (hδ.trans_le hx).ne') (hw.trans hx) (by linarith) hu1

/-- A finite positive moment implies almost-sure finiteness of an extended mass. -/
theorem fusion_mass_finite_of_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {p : ℝ} (hp : 0 < p)
    (hfin : (∫⁻ ω, f ω ^ p ∂P) < ⊤) : ∀ᵐ ω ∂P, f ω ≠ ⊤ := by
  filter_upwards [ae_lt_top' (hf.pow_const p) hfin.ne] with ω hω
  intro he
  rw [he, ENNReal.top_rpow_of_pos hp] at hω
  exact lt_irrefl _ hω

end DOZZ.Proofs
