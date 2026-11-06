module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Local L² assembly of the Hessian-derived time derivative

This module proves local square-integrability of the literal reverse-time
equation carrier assembled from a Hessian, gradient, value, and source.
-/

 public section

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Elementwise



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

private theorem memLp_mul_of_continuousOn_of_bound
     {S : HypoellipticAleksandrov.Parabolic.Region d} {f g : HypoellipticAleksandrov.Parabolic.ScalarField d} {M : ℝ}
    (hS : MeasurableSet S) (hf : ContinuousOn f S)
    (hbound : ∀ z ∈ S, |f z| ≤ M)
    (hg : ParabolicMemLpOn S (2 ) g) :
    ParabolicMemLpOn S (2 ) (fun z => f z * g z) := by
  refine MemLp.of_le_mul (c := M) hg ?_ ?_
  · exact (hf.aestronglyMeasurable hS).mul hg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hS] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound z hz) (abs_nonneg _)

/-- The literal coefficient--Hessian, drift--gradient, zeroth-order, and source
combination in the reverse-time equation is locally square-integrable. -/
theorem hessianTimeDerivative_memLp
     {Ω O : PDE.VelocityRegion d}
    (r₀ r₁ τ₁ τ₂ : ℝ)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀))
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (U : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU : ParabolicMemLpOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) (2 ) U)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hG : ∀ j, ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
      (2 ) (G j))
    (H : TimeVelocity d → PDE.Mat d)
    (hH : ∀ j i, ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O)
      (2 ) (fun z => H z j i)) :
    ParabolicMemLpOn (Set.Ioo τ₁ τ₂ ×ˢ O) (2 )
      (fun z =>
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) +
        (∑ j : Fin d,
          reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z -
        reverseTimeScalarCoefficient r₁ F z.1 z.2) := by
  let Qin  := Set.Ioo τ₁ τ₂ ×ˢ O
  have hQin : MeasurableSet Qin := measurableSet_Ioo.prod hO.measurableSet
  let rev : TimeVelocity d → TimeVelocity d := fun z => (r₁ - z.1, z.2)
  have hrev : Continuous rev :=
    (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hrevMaps : MapsTo rev Qin (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro z hz
    have ht := htime hz.1
    refine ⟨?_, subset_closure (hOΩ hz.2)⟩
    constructor <;> linarith [ht.1, ht.2]
  rcases haSmooth with ⟨VA, _hVAopen, hKVA, hVA⟩
  rcases hbSmooth with ⟨VB, _hVBopen, hKVB, hVB⟩
  rcases hcSmooth with ⟨VC, _hVCopen, hKVC, hVC⟩
  rcases hFSmooth with ⟨VF, _hVFopen, hKVF, hVF⟩




  obtain ⟨MC, hMC⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hVC.continuousOn.mono hKVC)
  obtain ⟨MF, hMF⟩ :=
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hVF.continuousOn.mono hKVF)
  have hAH (i j : Fin d) : ParabolicMemLpOn Qin (2 )
      (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) := by
    obtain ⟨MA, hMA⟩ :=
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
        ((continuous_apply j).comp_continuousOn
          ((continuous_apply i).comp_continuousOn (hVA.continuousOn.mono hKVA)))
    apply memLp_mul_of_continuousOn_of_bound (M := MA) hQin
      ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn ((hVA.continuousOn.mono hKVA).comp hrev.continuousOn hrevMaps))) _ (hH j i)
    intro z hz
    change |a (r₁ - z.1) z.2 i j| ≤ MA
    have h := hMA _ (hrevMaps hz)
    change |a (r₁ - z.1) z.2 i j| ≤ MA at h
    exact h
  have hBG (j : Fin d) : ParabolicMemLpOn Qin (2 )
      (fun z => reverseTimeVectorCoefficient r₁ b z.1 z.2 j * G j z) := by
    obtain ⟨MB, hMB⟩ :=
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
        ((continuous_apply j).comp_continuousOn (hVB.continuousOn.mono hKVB))
    apply memLp_mul_of_continuousOn_of_bound (M := MB) hQin
      ((continuous_apply j).comp_continuousOn ((hVB.continuousOn.mono hKVB).comp hrev.continuousOn hrevMaps)) _ (hG j)
    intro z hz
    change |b (r₁ - z.1) z.2 j| ≤ MB
    simpa only [Real.norm_eq_abs, Function.comp_def, rev] using hMB _ (hrevMaps hz)


  letI : IsFiniteMeasure (timeVelocityVolumeOn Qin) :=
    isFiniteMeasure_restrict.mpr ((Metric.isBounded_Ioo τ₁ τ₂).prod (hΩbounded.subset hOΩ)).measure_lt_top.ne

  have hsumAH : ParabolicMemLpOn Qin (2 )
      (fun z => ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * H z j i) := by
    exact memLp_finset_sum Finset.univ fun i _ =>
      memLp_finset_sum Finset.univ fun j _ => hAH i j

  exact ((hsumAH.add (memLp_finset_sum Finset.univ fun j _ => hBG j)).add (by
      apply memLp_mul_of_continuousOn_of_bound (M := MC) hQin ((hVC.continuousOn.mono hKVC).comp hrev.continuousOn hrevMaps) _ hU
      intro z hz
      exact hMC _ (hrevMaps hz))).sub (by
      refine MemLp.of_bound (((hVF.continuousOn.mono hKVF).comp hrev.continuousOn hrevMaps).aestronglyMeasurable hQin) MF ?_
      filter_upwards [ae_restrict_mem hQin] with z hz
      exact hMF _ (hrevMaps hz))

end HypoellipticAleksandrov.Parabolic.Dirichlet
