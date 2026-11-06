module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBarrierSmooth
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Finite-measure passage for bounded source barriers

Smooth source bounds control the total mass of the literal source-action measure.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal

/-- Uniform bounds on smooth compact tests control the mass of a finite measure supported in U. -/
theorem boundedSource_measure_mass_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    {U : Set E} (hU : IsOpen U) (hμ : μ Uᶜ = 0) (C : ℝ) (hC : 0 ≤ C)
    (ht : ∀ φ : E → ℝ, ContDiff ℝ PDE.smoothOrder φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ C) :
    μ.real univ ≤ C := by
  have hbound : μ U ≤ ENNReal.ofReal C := by
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
    obtain ⟨φ, hφ, hφc, hφU, hφb, hφone⟩ := exists_smooth_cutoff hK hU hKU



    have hKreal : μ.real K ≤ C := by
      rw [← integral_indicator_one hK.measurableSet]
      refine (integral_mono ((integrable_const (1 : ℝ)).indicator hK.measurableSet) (hφ.continuous.integrable_of_hasCompactSupport hφc) (fun x => ?_)).trans (ht φ hφ hφc hφU hφb)
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, Pi.one_apply, hφone x hx, le_refl]
      · simpa only [indicator_of_notMem hx] using (hφb x).1

    exact hrK.trans_le (by
        apply (ENNReal.toReal_le_toReal (measure_ne_top μ K) ENNReal.ofReal_ne_top).mp
        simpa only [Measure.real, ENNReal.toReal_ofReal hC] using hKreal)
  have heq : μ U = μ univ := by

    simpa only [hμ, add_zero] using (measure_add_measure_compl hU.measurableSet (μ := μ))
  rw [heq] at hbound
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hC)

variable (hH : HormanderHypoellipticityStatement) {d : ℕ} (hd : 0 < d) {c : PDE.Vec d} {R : ℝ} (hR : 0 < R) {lam Lam m Lb : ℝ} (hlam : 0 < lam) (hm : 0 < m) (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B) (b : PDE.VectorField d) (hb : IsSmoothDrift b) (hbounds : HasTransportBounds m Lb b) (S : TerminalOperatorFamily (PDE.euclideanBall c R) (fun _ => 0)) (K : MovingFiberKernel (PDE.euclideanBall c R) (fun _ => 0)) (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) (fun _ => 0) (PDE.isOpen_euclideanBall c R).measurableSet B b S K)

include hH hd hR hlam hm hB hBs hell hb hbounds hreal in
/-- The source-action measure from one starting point has quadratically controlled mass. -/
theorem boundedSourceActionMeasure_dirac_mass_le_quadratic

    (T : ℝ) (p : KineticPoint d)
    (hp : p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T) :
    (boundedSourceActionMeasure K (Measure.dirac p) p.time T).real univ ≤
      boundedSourceQuadratic c R lam p := by
  let μ := boundedSourceActionMeasure K (Measure.dirac p) p.time T
  have hΩm := (PDE.isOpen_euclideanBall c R).measurableSet
  have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec d)) := continuous_const



  apply boundedSource_measure_mass_le μ (isOpen_boundedSourcePast (PDE.isOpen_euclideanBall c R) hγ T) (boundedSourceActionMeasure_compl_past K hΩm hγ (Measure.dirac p) p.time T) _ (by
      apply boundedSourceQuadratic_nonneg hlam c R
      simpa only [boundedSource_stationary_domain] using hp.2)
  intro φ hφ hφc hφU hφb
  let g := φ ∘ KineticPoint.equivProd d
  have hg : Continuous g := hφ.continuous.comp (KineticPoint.homeomorphProd d).continuous


  have hgn : ∀ q, 0 ≤ g q := fun q => (hφb _).1
  have hgb : ∀ q, g q ≤ 1 := fun q => (hφb _).2


  have hi := integral_boundedSourceActionMeasure K hΩm hγ (Measure.dirac p) p.time T
    g hg.measurable 1 zero_le_one (fun q => by rw [abs_of_nonneg (hgn q)]; exact hgb q)
  change (∫ q, φ q ∂μ) =
    ∫ q, (∫ r in Ioo p.time T, duhamelIntegrand K g q r) ∂Measure.dirac p at hi
  rw [integral_dirac, ← duhamelPotential_eq_integral_window K g p le_rfl] at hi
  rw [hi]
  exact duhamel_smooth_le_boundedSourceQuadratic hH hd hR hlam hm B hB hBs hell
    b hb hbounds S K hreal g hg (hφc.comp_homeomorph (KineticPoint.homeomorphProd d)) hφ hgn hgb T (by
        rw [boundedSourceTest_support]
        intro q hq
        exact hφU hq) p hp

variable (g : HypoellipticAleksandrov.KineticScalarField d) (hg : Measurable g) (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ q, |g q| ≤ M) (T : ℝ) (p : KineticPoint d) (hp : p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T)

include hH hd hR hlam hm hB hBs hell hb hbounds hreal hg hM hgb hp
/-- Signed bounded Borel potentials inherit the uniform quadratic barrier. -/
theorem abs_duhamelPotential_le_boundedSourceQuadratic

     :
    |duhamelPotential K T g p| ≤ boundedSourceQuadratic c R lam p * M := by
  let μ := boundedSourceActionMeasure K (Measure.dirac p) p.time T


  have hi := integral_boundedSourceActionMeasure K ((PDE.isOpen_euclideanBall c R).measurableSet) continuous_const (Measure.dirac p) p.time T
    g hg M hM hgb
  change (∫ q, g ⟨q.1, q.2.1, q.2.2⟩ ∂μ) =
    ∫ q, (∫ r in Ioo p.time T, duhamelIntegrand K g q r) ∂Measure.dirac p at hi
  rw [integral_dirac, ← duhamelPotential_eq_integral_window K g p le_rfl] at hi
  have hnorm := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun q => g ⟨q.1, q.2.1, q.2.2⟩) (C := M)
    (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hgb _)
  rw [Real.norm_eq_abs, hi] at hnorm
  have hmass := boundedSourceActionMeasure_dirac_mass_le_quadratic hH hd hR hlam hm
    B hB hBs hell b hb hbounds S K hreal T p hp
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hmass hM).trans_eq (mul_comm _ _))

/-- The two independent barriers give the source-needed minimum with exact normalization. -/
theorem abs_duhamelPotential_le_time_min_quadratic

     :
    |duhamelPotential K T g p| ≤
      min (T - p.time) (boundedSourceQuadratic c R lam p) * M := by
  rw [min_mul_of_nonneg _ _ hM]
  exact le_min (abs_duhamelPotential_le K g M hM hgb p T hp.1)
    (abs_duhamelPotential_le_boundedSourceQuadratic hH hd hR hlam hm B hB hBs hell
      b hb hbounds S K hreal g hg M hM hgb T p hp)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
