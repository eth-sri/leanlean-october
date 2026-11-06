module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonRepresentative
import Mathlib.MeasureTheory.Group.Measure

/-! # Pointwise source bounds for classical energy representatives

The sharp affine variational envelope transfers through time reflection and the product
representative. Interior continuity promotes the resulting almost-everywhere bound.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise

/-- Original-time reflection preserves the literal restricted reverse-time volume. -/
theorem sourceTimeReflection_measurePreserving (a T : ℝ) :
    MeasurePreserving (fun t : ℝ => T - t)
      (volume.restrict (Ioo a T)) (reverseTimeVolume (T - a)) := by
  have hm : MeasurePreserving (fun t : ℝ => T - t) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left _ T).comp
        (Measure.measurePreserving_neg _)
  have hpre : (fun t : ℝ => T - t) ⁻¹' Ioo 0 (T - a) = Ioo a T := by
    simp
  rw [← hpre]
  exact hm.restrict_preimage isOpen_Ioo.measurableSet

/-- A continuous classical representative of the zero-initial energy correction has
the sharp source-amplitude time bound at every interior point. -/
theorem classicalEnergyRepresentative_abs_le_source_time {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T lam : ℝ) (haT : a < T) (hlam : 0 < lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (M : ℝ) (hM : 0 ≤ M)
    (hFM : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |F z| ≤ M)
    (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
    (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g)
    (hu : IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu)
    (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hwslice : ∀ᵐ t ∂volume.restrict (Ioo a T),
      (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1) := by
  have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  have hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  have henv := hu.abs_reverseTimeHilbertRepresentative_le_affine a T lam haT hlam
    hΩ hΩb A _ _ _ hAs hbs hcs hFs
    (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl) 0 M le_rfl hM hFM 0
    (by filter_upwards [Lp.coeFn_zero ℝ 2 _] with y hy
        simp_all) u g hdu
  have hraw : ∀ᵐ τ ∂reverseTimeVolume (T - a),
      ∀ hτ : τ ∈ Ioo 0 (T - a),
        ∀ᵐ y ∂PDE.volumeOn Ω, |valueCLM hΩ (u τ) y| ≤ M * τ := by
    filter_upwards [(reverseTimeHilbertRepresentative_spec hΩ (T - a)
      _ u g hdu).1] with τ hrep hτ
    have hb := henv τ ⟨hτ.1.le, hτ.2.le⟩
    rw [hrep hτ] at hb
    simpa only [zero_add, mul_comm] using hb
  have horig := (sourceTimeReflection_measurePreserving a T).quasiMeasurePreserving.ae hraw
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ M * (T - t) := by
    filter_upwards [hwslice, horig, ae_restrict_mem measurableSet_Ioo] with t hs hr ht
    have ht' : T - t ∈ Ioo 0 (T - a) := ⟨by simp_all, by simp_all⟩
    filter_upwards [hs, hr ht'] with y hy hb
    simp_all
  exact abs_le_source_time_of_continuousOn_of_ae_slices hΩ a T M w hw hbound

end HypoellipticAleksandrov.Parabolic.LocalHolder
