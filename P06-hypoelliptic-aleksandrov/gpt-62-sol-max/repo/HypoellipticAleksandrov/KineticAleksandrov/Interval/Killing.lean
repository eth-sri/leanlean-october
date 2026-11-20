module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingMass
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels
import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionCurve

/-! # The error-function killing estimate on a bounded interval

Both endpoint comparisons are proved from smooth terminal data. Evolution clauses
for a supplied kernel are obtained from the two analytic hypotheses by uniqueness.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- Scalar marginal mass equals the ambient master mass of the same query. -/
theorem interval_parabolic_mass_eq_master {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    P K hJ (scalarQuery σ τ hστ v hv) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  obtain ⟨Q, hfirst, _⟩ := hp (fun _ _ _ _ => rfl)
  unfold P parabolicMarginalAmbientMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
  exact _root_.HypoellipticAleksandrov.KineticAleksandrov.Decay.master_mass_eq_marginal_mass hJ K σ τ hστ v z hv (hfirst σ τ hστ ⟨v, hv⟩ z)

/-- The positive marginal is bounded by the half-line barrier at the nearer endpoint. -/
theorem interval_killing
    {lam Lam m Lb : ℝ} (E : IntervalEvolution lam Lam m Lb)
    (σ τ : ℝ) (hστ : σ < τ) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (E.domain) stationary σ) :
    (P E.kernel E.measurableSet (scalarQuery σ τ hστ.le v hv)).real univ ≤
      intervalErf (min (v 0 - E.left) (E.right - v 0) / (2 * Real.sqrt (lam * (τ - σ)))) := by
  have hp := (E.clauses).2.1
  have hleft := interval_endpoint_mass_bound E.lt hστ E.setting.1.1
    (s := 1) (e := E.left) (by norm_num) E.coefficient E.setting.1 E.measurableSet E.kernel hp
    (fun w hw => by
      have h := PDE.mem_oneDimensionalAxisBox_iff.mp hw
      simpa only [one_mul, PDE.vecOneCoordinate] using sub_pos.mpr h.1)
    (fun w hw => by
      simpa only [one_mul] using sub_nonneg.mpr (interval_coordinate_closure hw).1) v hv
  have hright := interval_endpoint_mass_bound E.lt hστ E.setting.1.1
    (s := -1) (e := E.right) (by norm_num) E.coefficient E.setting.1 E.measurableSet E.kernel hp
    (fun w hw => by
      have h := PDE.mem_oneDimensionalAxisBox_iff.mp hw
      change 0 < -1 * (w 0 - E.right)
      have hc : w 0 < E.right := h.2
      linarith)
    (fun w hw => by
      have h := (interval_coordinate_closure hw).2
      linarith) v hv
  rcases le_total (v 0 - E.left) (E.right - v 0) with hl | E.realizes
  · rw [min_eq_left hl]
    simpa only [intervalHeat, one_mul] using hleft
  · rw [min_eq_right E.realizes]
    convert hright using 1
    unfold intervalHeat
    congr 2
    ring

/-- Fourier total variation is bounded by scalar marginal mass on the same kernel. -/
theorem interval_fourier_tv_le_mass {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z ξ : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
    (ν : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection K (movingQuery σ τ hστ v z hv) ξ ν) :
    TV ν ≤ (P K hJ (scalarQuery σ τ hστ v hv)).real univ := by
  have h := (Measure.le_iff.mp (fourierProjection_variation_le K _ ξ ν hν))
    univ MeasurableSet.univ
  have hm : K.firstMarginal (movingQuery σ τ hστ v z hv) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
    rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  rw [hm, ← interval_parabolic_mass_eq_master hJ K B hp σ τ hστ v z hv] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

end HypoellipticAleksandrov.KineticAleksandrov.Interval
