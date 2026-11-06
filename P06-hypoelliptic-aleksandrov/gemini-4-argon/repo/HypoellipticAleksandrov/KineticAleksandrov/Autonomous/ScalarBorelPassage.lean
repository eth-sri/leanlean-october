module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarBorelInnerErrorLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelBoundary
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDEFoundation.Measure.OneDimensionalCoordinate

/-! # The source smooth-to-Borel passage for autonomous scalar coefficient class (b) -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic MeasureTheory Set
open Filter ContinuousLinearMap
open scoped Convolution Topology

/- Source lemma `l:borel#autonomous`, class (b), with C₀ fixed before all coefficient and
  solution data. -/
theorem autonomous_abp_smooth_to_borel
    (lam Lam ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmoothEstimate :
      ∀ a : ℝ → ℝ → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
        (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
        ∀ (P₀ : Point) (R : ℝ), 0 < R →
        ∀ u f : Point → ℝ,
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        Measurable f → MemLp (fun P => max (f P) 0)
          (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
          sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C₀ * R ^ alpha * (eLpNorm (borelSource localised u f)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (P₀ : Point) (R : ℝ) (hR : 0 < R)
    (u f : Point → ℝ)
    (hcont : ContinuousOn u (closure (backwardCylinder P₀ R)))
    (hreg : IsKineticC112On u (backwardCylinder P₀ R))
    (hf : Measurable f) (hLp : MemLp (fun P => max (f P) 0)
      (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      autonomousScalarOperator a u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C,hC,hc⟩ : ∃ C : ℕ → ℝ → ℝ → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
        ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam) ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2)) := by
      have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
        Measure.prod.instIsAddHaarMeasure volume volume
      let C := fun j => scalarBorelConvolution (scalarBorelBump j) a
      refine ⟨C, fun j => scalarBorelConvolution_spec hlam a ha hb _, ?_⟩
      have hr : Tendsto (fun j => (scalarBorelBump j).rOut) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hratio : ∀ᶠ j in atTop, (scalarBorelBump j).rOut ≤ 2 * (scalarBorelBump j).rIn := by
        filter_upwards with j
        dsimp only [scalarBorelBump]
        linarith
      exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hratio
        (scalar_borel_locallyIntegrable hlam a ha hb)

    /- Tonelli lifts position-velocity null sets to physical spacetime. -/
  apply borel_boundary_limit p hp alpha C₀ localised P₀ R hR u f hcont hLp
  intro n P hP
  have hk := isCompact_closure_reflected_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  have hKD := closure_reflected_innerCylinder_subset P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
  rw [kineticReflection_image_innerCylinder] at hk hKD
  have hμ := Measure.restrict_mono_set volume (subset_closure.trans hKD)
  exact scalar_borel_smooth_inner_limit lam Lam hlam hLam p hp alpha C₀ localised hsmoothEstimate
    a ha hb C hC hc u f hreg (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
    (borelInnerRadius_pos R hR n) hk hKD hf (hLp.mono_measure hμ)
    (hsub.filter_mono (ae_mono hμ)) P hP

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
