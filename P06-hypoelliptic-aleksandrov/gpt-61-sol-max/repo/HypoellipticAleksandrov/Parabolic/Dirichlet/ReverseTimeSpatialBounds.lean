module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Local reverse-time spatial bounds

This module derives the compact-cylinder bounds on the reverse-time
coefficient, drift, scalar coefficient, and source slices required by the
Dirichlet data layer.  All regularity hypotheses are local to the indicated
closed cylinder.
-/

 public section



open scoped ENNReal Matrix.Norms.Elementwise
open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A scalar parabolic closed cylinder is compact when its spatial base is bounded. -/
theorem isCompact_scalarParabolicClosedCylinder
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (scalarParabolicClosedCylinder r₀ r₁ Ω) := (id (IsCompact.prod isCompact_Icc (Bornology.IsBounded.isCompact_closure hΩbounded)))

variable {d : ℕ}

/-- The derivative of a fixed-time spatial coefficient slice is the joint
derivative in a purely spatial direction. -/
theorem fderiv_scalarSpatialSlice_apply
     (a : CoefficientField d) (r : ℝ)
    (y v : PDE.Vec d) (i j : Fin d)
    (ha : DifferentiableAt ℝ
      (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)) :
    (fderiv ℝ (fun x  => a r x i j) y) v =
      (fderiv ℝ (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)) (0, v) := by
  have hslice : HasFDerivAt (fun x  => a r x i j)
      ((fderiv ℝ (fun z : TimeVelocity d => a z.1 z.2 i j) (r, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) y := by
    simpa only [Function.comp_def] using ha.hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right  r y)
  rw [hslice.fderiv]
  rfl

variable {Ω : PDE.VelocityRegion d}

/-- Joint smoothness near the closed cylinder makes the literal fixed-time
spatial coefficient divergence continuous there. -/
theorem continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood

    (r₀ r₁ : ℝ) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (scalarSpatialCoefficientDivergence a)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  apply continuousOn_pi.2
  intro j
  change ContinuousOn (fun z : TimeVelocity d => ∑ i : Fin d,
    (fderiv ℝ (fun y : PDE.Vec d => a z.1 y i j) z.2) (PDE.basisVec i))
    (scalarParabolicClosedCylinder r₀ r₁ Ω)
  apply continuousOn_finset_sum
  intro i _hi

  have hentry  := (contDiffOn_apply ℝ ℝ j Set.univ).comp ((contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV (by
        intro z hz
        exact Set.mem_univ _)) (by
      intro z hz
      exact Set.mem_univ _)
  have hderiv : ContinuousOn (fun z  =>
      (fderiv ℝ (fun w : TimeVelocity d => a w.1 w.2 i j) z) (0, PDE.basisVec i)) V :=
    (hentry.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
      continuousOn_const
  refine (hderiv.mono hKV).congr ?_
  intro z hz
  rcases z with ⟨r, y⟩
  simpa using fderiv_scalarSpatialSlice_apply a r y (PDE.basisVec i) i j
    ((hentry.contDiffAt (hVopen.mem_nhds (hKV hz))).differentiableAt (by simp))

/-- A smooth scalar coefficient near the closed cylinder restricts to a
continuous reverse-time spatial slice. -/
theorem continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood

    (r₀ r₁ τ : ℝ) (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ContinuousOn (fun y  =>
      reverseTimeScalarCoefficient r₁ c τ y) Ω := by

  rcases hc with ⟨V, hVopen, hKV, hV⟩



  simpa only [reverseTimeScalarCoefficient_apply, Function.comp_def] using
    (hV.continuousOn.mono hKV).comp (Continuous.prodMk_right _).continuousOn (by
        intro y hy
        exact ⟨(by
            constructor <;> linarith [hτ.1, hτ.2]), subset_closure hy⟩)

/-- Smooth scalar coefficients near a bounded closed cylinder have one
uniform bound for all reverse-time spatial slices. -/
theorem exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood

    (r₀ r₁ : ℝ) (hΩbounded : Bornology.IsBounded Ω)
    (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ : ℝ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ y : PDE.Vec d, y ∈ Ω →
        |reverseTimeScalarCoefficient r₁ c τ y| ≤ M := by
  rcases hc with ⟨V, hVopen, hKV, hV⟩
  obtain ⟨C, hC⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hV.continuousOn.mono hKV)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro τ hτ y hy


  exact (hC (r₁ - τ, y) (⟨(by
      constructor <;> linarith [hτ.1, hτ.2]), subset_closure hy⟩)).trans (le_max_left _ _)

/-- A smooth source near the closed cylinder is a.e.-strongly measurable on
each reverse-time slice with respect to the restricted spatial volume. -/
theorem aestronglyMeasurable_reverseTimeSourceSlice_of_smoothOnNeighborhood

    (r₀ r₁ τ : ℝ) (hΩ : IsOpen Ω)
    (F : PDE.TimeScalarField d)
    (hF : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    MeasureTheory.AEStronglyMeasurable
      (fun y  => F (r₁ - τ) y) (PDE.volumeOn Ω) := (ContinuousOn.aestronglyMeasurable
  (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood r₀ r₁ τ F hF hτ) (IsOpen.measurableSet hΩ))

variable (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (F : PDE.TimeScalarField d) (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

include hΩ hΩbounded hF
/-- A smooth source near a bounded closed cylinder belongs to `L²` on every
reverse-time slice. -/
theorem reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood


    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    MemLp
      (fun y  => F (r₁ - τ) y)
      (2 ) (PDE.volumeOn Ω) := by
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn Ω) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  obtain ⟨C, hC0, hC⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded F hF
  have hmeas  :=
    aestronglyMeasurable_reverseTimeSourceSlice_of_smoothOnNeighborhood
      r₀ r₁ τ hΩ F hF hτ
  refine MemLp.of_bound hmeas C ?_
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
  exact hC τ hτ y hy

/-- Smooth source data near a bounded closed cylinder have one uniform `L²`
bound for all reverse-time slices. -/
theorem exists_reverseTimeSourceSlice_L2_bound_of_smoothOnNeighborhood

     :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ τ : ℝ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MemLp
        (fun y  => F (r₁ - τ) y)
        (2 ) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y  => F (r₁ - τ) y)‖ ≤ M := by
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn Ω) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  obtain ⟨C, hC0, hC⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded F hF

  refine ⟨(MeasureTheory.measureUnivNNReal (PDE.volumeOn Ω)) ^
      ((2 : ℝ≥0∞).toReal)⁻¹ * (max C 0), mul_nonneg (by positivity) (le_max_right _ _), ?_⟩
  intro τ hτ hτLp
  apply MeasureTheory.Lp.norm_le_of_ae_bound (le_max_right _ _)
  filter_upwards [hτLp.coeFn_toLp, ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
  rw [hy]
  exact (hC τ hτ y hyΩ).trans (le_max_left _ _)

end HypoellipticAleksandrov.Parabolic.Dirichlet
