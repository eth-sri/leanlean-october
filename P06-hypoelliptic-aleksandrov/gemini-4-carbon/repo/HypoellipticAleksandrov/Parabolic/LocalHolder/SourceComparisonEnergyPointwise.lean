module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import PDEFoundation.Measure.RestrictedVolume
import HypoellipticAleksandrov.Parabolic.WeakDerivatives
import Mathlib.Topology.Order.Lattice
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
import Mathlib.MeasureTheory.Group.Measure

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise

/-- A continuous envelope bounding almost every slice bounds every interior point. -/
theorem abs_le_of_continuousOn_of_ae_slices {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (a T : ℝ) (w b : TimeVelocity d → ℝ)
    (hbc : Continuous b)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hb : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ b (t, y)) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ b z := by
  classical
  let U := scalarParabolicOpenCylinder a T Ω
  have hU : MeasurableSet U := (isOpen_Ioo.prod hΩ).measurableSet
  let w₀ := U.piecewise w (fun _ => 0)
  have hw₀ : Measurable w₀ := hw.measurable_piecewise continuousOn_const hU
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w₀ (t, y)| ≤ b (t, y) := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioo] with t ht hti
    filter_upwards [ht, ae_restrict_mem hΩ.measurableSet] with y hy hyo
    change |U.piecewise w (fun _ => 0) (t, y)| ≤ _
    rw [piecewise_eq_of_mem U w (fun _ => 0) (show (t, y) ∈ U from ⟨hti, hyo⟩)]
    exact hy
  have hprod : (volume.restrict (Ioo a T)).prod (PDE.volumeOn Ω) =
      timeVelocityVolumeOn (Ioo a T ×ˢ Ω) := by
    rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
    exact Measure.prod_restrict (Ioo a T) Ω
  have hae := (Measure.ae_prod_iff_ae_ae (measurableSet_le (continuous_abs.measurable.comp hw₀) hbc.measurable)).2 hbound
  rw [hprod] at hae
  have heq : (fun z => min (|w z|) (b z)) =ᵐ[
      volume.restrict (scalarParabolicOpenCylinder a T Ω)] fun z => |w z| := by
    filter_upwards [hae, ae_restrict_mem hU] with z hz hzu
    change |U.piecewise w (fun _ => 0) z| ≤ _ at hz
    rw [piecewise_eq_of_mem U w (fun _ => 0) hzu] at hz
    exact min_eq_left hz
  intro z hz
  exact min_eq_left_iff.mp ((Measure.eqOn_open_of_ae_eq heq (isOpen_Ioo.prod hΩ) (hw.abs.inf hbc.continuousOn) hw.abs) hz)

/-- An almost-everywhere time bound holds pointwise for a continuous interior representative. -/
theorem abs_le_source_time_of_continuousOn_of_ae_slices {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (a T M : ℝ) (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hb : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ M * (T - t)) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1) :=
  abs_le_of_continuousOn_of_ae_slices hΩ a T w (fun z => M * (T - z.1))
    (continuous_const.mul (continuous_const.sub continuous_fst)) hw hb


/-- Original-time reflection preserves the literal restricted reverse-time volume. -/
theorem sourceTimeReflection_measurePreserving (a T : ℝ) :
    MeasurePreserving (fun t : ℝ => T - t)
      (volume.restrict (Ioo a T)) (reverseTimeVolume (T - a)) := by
  have hm : MeasurePreserving (fun t => T - t) (volume : Measure ℝ) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℝ) T).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpre : (fun t => T - t) ⁻¹' Ioo 0 (T - a) = Ioo a T := by
    rw [preimage_const_sub_Ioo]
    congr 1 <;> ring
  rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpre]
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
  have hAs : IsSmoothOnNeighborhood (fun z => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  have hbs : IsSmoothOnNeighborhood (fun _ => (0 : PDE.Vec d))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hcs : IsSmoothOnNeighborhood (fun _ => (0 : ℝ))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  have henv := hu.abs_reverseTimeHilbertRepresentative_le_affine a T lam haT hlam
    hΩ hΩb A (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y)) hAs hbs hcs hFs
    (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl) 0 M le_rfl hM hFM 0
    (by filter_upwards [Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω)] with y hy
        rw [hy]; simp) u g hdu
  have hraw : ∀ᵐ τ ∂reverseTimeVolume (T - a),
      ∀ hτ : τ ∈ Ioo 0 (T - a),
        ∀ᵐ y ∂PDE.volumeOn Ω, |valueCLM hΩ (u τ) y| ≤ M * τ := by
    filter_upwards [(reverseTimeHilbertRepresentative_spec hΩ (T - a)
      (sub_pos.mpr haT) u g hdu).1] with τ hrep hτ
    have hb := henv τ ⟨hτ.1.le, hτ.2.le⟩
    rw [hrep hτ] at hb
    simpa [mul_comm] using hb
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ M * (T - t) := by
    filter_upwards [hwslice, ((sourceTimeReflection_measurePreserving a T).quasiMeasurePreserving.ae hraw), ae_restrict_mem measurableSet_Ioo] with t hs hr ht
    have ht' : T - t ∈ Ioo 0 (T - a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    filter_upwards [hs, hr ht'] with y hy hb
    rw [hy]
    exact hb
  exact abs_le_source_time_of_continuousOn_of_ae_slices hΩ a T M w hw hbound

end HypoellipticAleksandrov.Parabolic.LocalHolder

