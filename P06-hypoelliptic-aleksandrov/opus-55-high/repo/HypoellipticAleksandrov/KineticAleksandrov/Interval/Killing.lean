module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingMass
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels

/-! # The error-function killing estimate on a bounded interval

Both endpoint comparisons are proved from smooth terminal data. Evolution clauses
for a supplied kernel are obtained from the two analytic hypotheses by uniqueness.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

private theorem master_mass_eq_marginal_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d) (hv : v ∈ movingDomain Ω γ σ)
    (hfirst : (parabolicMarginalKernel K hΩ σ τ hστ) ⟨v, hv⟩ =
      (K.fiberFirstMarginal hΩ σ τ hστ) (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)) :
    (parabolicMarginalKernel K hΩ σ τ hστ ⟨v, hv⟩) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hΩ σ τ hστ
    (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)
  rw [← hfirst] at hmap
  have hq : evolutionQueryOfState Ω γ σ τ hστ
      (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z) = movingQuery σ τ hστ v z hv := rfl
  rw [hq] at hmap
  have h := congrArg (fun μ : Measure _ => μ univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simp_all


variable {a c : ℝ} (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary) (B : CoefficientField 1)

/-- Scalar marginal mass equals the ambient master mass of the same query. -/
theorem interval_parabolic_mass_eq_master 
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    P K hJ (scalarQuery σ τ hστ v hv) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  obtain ⟨Q, hfirst, _⟩ := hp (fun _ _ _ _ => rfl)
  unfold P parabolicMarginalAmbientMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  exact master_mass_eq_marginal_mass hJ K σ τ hστ v z hv (hfirst σ τ hστ _ z)

/-- The positive marginal is bounded by the half-line barrier at the nearer endpoint. -/
theorem interval_killing
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hsetting : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K)
    (σ τ : ℝ) (hστ : σ < τ) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (P K hJ (scalarQuery σ τ hστ.le v hv)).real univ ≤
      intervalErf (min (v 0 - a) (c - v 0) / (2 * Real.sqrt (lam * (τ - σ)))) := by
  have hp := (interval_evolution_clauses hH hLE hac B b hsetting hJ S K hr).2.1
  have hleft := interval_endpoint_mass_bound hac hστ hsetting.1.1
    (s := 1) (e := a) (by norm_num) B hsetting.1 hJ K hp
    (fun w hw => by
      aesop)
    (fun w hw => by
      simpa only [one_mul] using sub_nonneg.mpr (interval_coordinate_closure hw).1) v hv
  have hright := interval_endpoint_mass_bound hac hστ hsetting.1.1
    (s := -1) (e := c) (by norm_num) B hsetting.1 hJ K hp
    (fun w hw => by
      aesop)
    (fun w hw => by
      have h := (interval_coordinate_closure hw).2
      linarith) v hv
  rcases le_total (v 0 - a) (c - v 0) with hl | hr
  · aesop
  aesop

/-- Fourier total variation is bounded by scalar marginal mass on the same kernel. -/
theorem interval_fourier_tv_le_mass 
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
  rw [hm, ← interval_parabolic_mass_eq_master hJ K B hp] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

end HypoellipticAleksandrov.KineticAleksandrov.Interval
