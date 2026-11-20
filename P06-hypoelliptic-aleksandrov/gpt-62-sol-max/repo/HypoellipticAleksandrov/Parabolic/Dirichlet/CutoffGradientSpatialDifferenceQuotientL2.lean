module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import HypoellipticAleksandrov.Measure.LpZeroExtension
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientL2
public import PDEFoundation.Measure.AffineVolume

/-!
# Cutoff-gradient spatial difference quotients on restricted `L²`

This module constructs the representative-independent scalar restricted-`L²`
operator `(D_j η) Δ_{k,h}` using ambient zero extension, global translation,
restriction, and the bounded scalar multiplier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d)

/-- A cutoff gradient coordinate is measurable for restricted volume. -/
theorem cutoffGradient_aestronglyMeasurable :
    AEStronglyMeasurable (fun y => PDE.classicalGradient η.toFun y j)
      (PDE.volumeOn Ω) := by
  have hcontinuous : Continuous (fun y => PDE.classicalGradient η.toFun y j) := by
    simpa only [PDE.classicalGradient_apply] using
      (η.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hcontinuous.aestronglyMeasurable

/-- A cutoff gradient coordinate obeys the cutoff bound almost everywhere. -/
theorem cutoffGradient_norm_le :
    ∀ᵐ y ∂PDE.volumeOn Ω, ‖PDE.classicalGradient η.toFun y j‖ ≤ K :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]
    exact η.abs_classicalGradient_apply_le y j

end

theorem cutoffGradient_eq_zero_of_not_mem_tsupport
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (j : Fin d)
    {y : PDE.Vec d} (hy : y ∉ tsupport η.toFun) :
    PDE.classicalGradient η.toFun y j = 0 := by
  rw [PDE.classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hy]
  exact ContinuousLinearMap.zero_apply _

/-- The cutoff-coordinate-gradient times forward spatial difference quotient
on restricted-volume scalar `L²`, totalized at zero increment. -/
noncomputable def cutoffGradientSpatialDifferenceQuotientL2
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : MeasurableSet Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (j k : Fin d) (h : ℝ) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  weightedSpatialDifferenceQuotientL2 hΩ k h (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg (cutoffGradient_norm_le η j)

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : MeasurableSet Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (j k : Fin d) (h : ℝ)
  (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))

/-- The cutoff-gradient quotient uses the canonical global zero extension. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_ae :
    ⇑(cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        PDE.classicalGradient η.toFun y j *
          ((⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f)
              (y + h • PDE.basisVec k) -
            ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ f) y) / h) :=
  weightedSpatialDifferenceQuotientL2_apply_ae hΩ k h (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg (cutoffGradient_norm_le η j) f

/-- A supplied representative gives the literal cutoff-gradient quotient
under the forward active-support collar. -/
theorem cutoffGradientSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    (g : PDE.Vec d → ℝ)
    (hfg : ⇑f =ᵐ[PDE.volumeOn Ω] g)
    (hηshift : η.ShiftMapsInto k h Ω) :
    ⇑(cutoffGradientSpatialDifferenceQuotientL2 hΩ η j k h f)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        PDE.classicalGradient η.toFun y j *
          ((g (y + h • PDE.basisVec k) - g y) / h) :=
  weightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq hΩ k h (fun y => PDE.classicalGradient η.toFun y j)
    (cutoffGradient_aestronglyMeasurable η j) K η.gradient_bound_nonneg (cutoffGradient_norm_le η j) f g hfg
      (fun y hy => hηshift (not_not.mp (fun h => hy (cutoffGradient_eq_zero_of_not_mem_tsupport η j h))))

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
