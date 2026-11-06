module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyPointwise
import Mathlib.MeasureTheory.Group.Measure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Pointwise source bounds for classical energy representatives

The sharp affine variational envelope transfers through time reflection and the product
representative. Interior continuity promotes the resulting almost-everywhere bound.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic
open MeasureTheory Set
open HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- A continuous classical representative of the zero-initial energy correction has
the sharp source-amplitude time bound at every interior point. -/
theorem classical_abs_le_source_time_withDrift {d : ℕ}
    {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T lam : ℝ) (haT : a < T) (hlam : 0 < lam)
    (A : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (hb : ContDiff ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2))
    (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A)
    (F : HypoellipticAleksandrov.Parabolic.ScalarField d) (hF : ContDiff ℝ PDE.smoothOrder F)
    (M : ℝ) (hM : 0 ≤ M)
    (hFM : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |F z| ≤ M)
    (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
    (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g)
    (hu : IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hwslice : ∀ᵐ t ∂volume.restrict (Ioo a T),
      (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1) := by




  have henv := hu.abs_reverseTimeHilbertRepresentative_le_affine a T lam haT hlam
    hΩ hΩb A b (fun _ _ => 0) (fun t y => F (t, y)) (⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩) (⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩) (⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩) (⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩)
    (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl) 0 M le_rfl hM hFM 0
    (by filter_upwards [Lp.coeFn_zero ℝ 2 _] with y hy
        rw [hy]; simp only [Pi.zero_apply, abs_zero, le_refl]) u g hdu



  exact abs_le_source_time_of_continuousOn_of_ae_slices hΩ a T M w hw (by
      filter_upwards [hwslice, ((sourceTimeReflection_measurePreserving a T).quasiMeasurePreserving.ae (show ∀ᵐ τ ∂reverseTimeVolume (T - a),
      ∀ hτ : τ ∈ Ioo 0 (T - a),
        ∀ᵐ y ∂PDE.volumeOn Ω, |valueCLM hΩ (u τ) y| ≤ M * τ by
          filter_upwards [(reverseTimeHilbertRepresentative_spec hΩ (T - a)
            (sub_pos.mpr haT) u g hdu).1] with τ hrep hτ
          have hb := henv τ ⟨hτ.1.le, hτ.2.le⟩
          rw [hrep hτ] at hb
          simpa only [zero_add, mul_comm] using hb)), ae_restrict_mem measurableSet_Ioo] with t hs hr ht

      filter_upwards [hs, hr (⟨by linarith [ht.2], by linarith [ht.1]⟩)] with y hy hb
      rw [hy]
      exact hb)

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
