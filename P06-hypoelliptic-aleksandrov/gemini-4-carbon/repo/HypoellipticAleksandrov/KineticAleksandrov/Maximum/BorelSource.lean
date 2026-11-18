module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter Set HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal

/-- The Lp triangle inequality with finite real-valued norms. -/
theorem borel_real_norm_add_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 1 ≤ p) {f g : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (eLpNorm (f + g) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal +
      (eLpNorm g (ENNReal.ofReal p) μ).toReal := by
  simpa only [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,hg.eLpNorm_ne_top⟩) (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)))

/-- Vanishing nonnegative error implies convergence of the actual perturbed source norms. -/
theorem borel_source_norm_tendsto {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 1 ≤ p) (F : E → ℝ) (G e : ℕ → E → ℝ)
    (hF : MemLp F (ENNReal.ofReal p) μ)
    (he : ∀ j, MemLp (e j) (ENNReal.ofReal p) μ)
    (hGm : ∀ j, AEStronglyMeasurable (G j) μ)
    (hFn : ∀ᵐ z ∂μ, 0 ≤ F z) (hGn : ∀ j, ∀ᵐ z ∂μ, 0 ≤ G j z)
    (hen : ∀ j, ∀ᵐ z ∂μ, 0 ≤ e j z)
    (hclose : ∀ j, ∀ᵐ z ∂μ, |G j z - F z| ≤ e j z)
    (ht : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun j => (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal) atTop
      (𝓝 (eLpNorm F (ENNReal.ofReal p) μ).toReal) := by
  have hdom j : ∀ᵐ z ∂μ, ‖G j z‖ ≤ ‖(F + e j) z‖ := by
    filter_upwards [hFn,hGn j,hen j,hclose j] with z hFz hGz hez hcl
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg hGz,Real.norm_of_nonneg (add_nonneg hFz hez)]
    have hab := (abs_le.mp hcl).2
    exact by linarith only [hab]
  have hGp j : MemLp (G j) (ENNReal.ofReal p) μ :=
    (hF.add (he j)).of_le (hGm j) (hdom j)
  have hu j : (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm F (ENNReal.ofReal p) μ).toReal +
      (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal := by
    apply (ENNReal.toReal_mono (hF.add (he j)).eLpNorm_ne_top
      (eLpNorm_mono_ae (hGm j) (hdom j))).trans
    exact borel_real_norm_add_le hp hF (he j)
  have hl j : (eLpNorm F (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal +
      (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal := by
    apply (ENNReal.toReal_mono ((hGp j).add (he j)).eLpNorm_ne_top
      (eLpNorm_mono_ae hF.aestronglyMeasurable ?_)).trans
    · exact borel_real_norm_add_le hp (hGp j) (he j)
    · filter_upwards [hFn,hGn j,hen j,hclose j] with z hFz hGz hez hcl
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg hFz,Real.norm_of_nonneg (add_nonneg hGz hez)]
      linarith only [((abs_le.mp hcl).1)]
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := ht ε hε
  refine ⟨N,fun j hj => ?_⟩
  have hb := hN j hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg] at hb
  rw [Real.dist_eq]
  have ha : |(eLpNorm (G j) (ENNReal.ofReal p) μ).toReal -
      (eLpNorm F (ENNReal.ofReal p) μ).toReal| ≤
      (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal := by
    rw [abs_le]
    constructor <;> linarith only [hu j,hl j]
  exact ha.trans_lt hb


/-- Eventual a.e. coverage exhausts the nonnegative finite source norm. -/
theorem borel_indicator_norm_tendsto {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 0 < p) (F : E → ℝ) (hF : MemLp F (ENNReal.ofReal p) μ)
    (hnn : ∀ᵐ z ∂μ, 0 ≤ F z) (S : ℕ → Set E) (hS : ∀ j, MeasurableSet (S j))
    (hcover : ∀ᵐ z ∂μ, ∀ᶠ j in atTop, z ∈ S j) :
    Tendsto (fun j => (eLpNorm ((S j).indicator F) (ENNReal.ofReal p) μ).toReal)
      atTop (𝓝 (eLpNorm F (ENNReal.ofReal p) μ).toReal) := by
  let G := fun j => (S j).indicator F
  have hG j : MemLp (G j) (ENNReal.ofReal p) μ := hF.indicator (hS j)
  have hGn j : ∀ᵐ z ∂μ, 0 ≤ G j z := by
    filter_upwards [hnn] with z hz
    by_cases hs : z ∈ S j
    · simpa only [G,indicator_of_mem hs] using hz
    · simp only [G,indicator_of_notMem hs,le_refl]
  have hmeas j : AEStronglyMeasurable (fun z => ‖G j z‖ ^ p) μ :=
    (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable (hG j).aestronglyMeasurable.norm
  have hi : Integrable (fun z => ‖F z‖ ^ p) μ := by
    have ht := hF.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using ht
  have hb j : ∀ᵐ z ∂μ, ‖‖G j z‖ ^ p‖ ≤ ‖F z‖ ^ p := by
    filter_upwards with z
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    by_cases hs : z ∈ S j
    · simp only [G,indicator_of_mem hs,le_refl]
    · simp only [G,indicator_of_notMem hs,norm_zero,norm_nonneg]
  have hc : ∀ᵐ z ∂μ, Tendsto (fun j => ‖G j z‖ ^ p) atTop (𝓝 (‖F z‖ ^ p)) := by
    filter_upwards [hcover] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [hz] with j hj
    simp only [G,indicator_of_mem hj]
  have hroot := (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / p)).continuousAt.tendsto.comp
    (tendsto_integral_of_dominated_convergence (fun z => ‖F z‖ ^ p) hmeas hi hb hc)
  have heq j : (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal =
      (∫ z, ‖G j z‖ ^ p ∂μ) ^ (1 / p) := by
    rw [abp_eLpNorm_toReal_nonneg hp (hG j) (hGn j)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hGn j] with z hz
    rw [Real.norm_of_nonneg hz]
  have heqF : (eLpNorm F (ENNReal.ofReal p) μ).toReal =
      (∫ z, ‖F z‖ ^ p ∂μ) ^ (1 / p) := by
    rw [abp_eLpNorm_toReal_nonneg hp hF hnn]
    congr 1
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    rw [Real.norm_of_nonneg hz]
  simpa only [Function.comp_def,← heq,← heqF,G] using hroot


/-- The source permits either the full positive part or its positive-solution localisation. -/
abbrev borelSource {d : ℕ} (localised : Bool) (u f : KineticPoint d → ℝ) :
    KineticPoint d → ℝ :=
  if localised then {P | 0 < u P}.indicator (fun P => max (f P) 0)
  else fun P => max (f P) 0

/-- The source smooth estimate, with its constant fixed before coefficient and cylinder. -/
abbrev BorelSmoothEstimate {d : ℕ} (lam Lam p alpha C₀ : ℝ) (localised : Bool) : Prop :=
  ∀ A : CoefficientField d,
    IsSmoothCoefficient A → IsSymmetricCoefficient A →
    HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
    ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
    ∀ u f : KineticPoint d → ℝ,
    ContinuousOn u (closure (backwardCylinder P₀ R)) →
    IsKineticC112On u (backwardCylinder P₀ R) →
    Measurable f → MemLp (fun P => max (f P) 0)
      (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) →
    (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
      C₀ * R ^ alpha * (eLpNorm (borelSource localised u f)
        (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal

/-- Both source variants are nonnegative pointwise. -/
theorem borelSource_nonneg {d : ℕ} (localised : Bool) (u f : KineticPoint d → ℝ)
    (P : KineticPoint d) : 0 ≤ borelSource localised u f P := by
  cases localised
  · exact le_max_right _ _
  · by_cases h : 0 < u P
    · simpa [borelSource, indicator_of_mem (show P ∈ {z | 0 < u z} from h)] using
        (le_max_right (f P) 0)
    · simp [borelSource, indicator_of_notMem (show P ∉ {z | 0 < u z} from h), le_refl]

/-- A nonnegative additive error changes either source variant by at most that error. -/
theorem borelSource_error_le {d : ℕ} (localised : Bool) (u f : KineticPoint d → ℝ)
    {e : KineticPoint d → ℝ} (P : KineticPoint d) (he : 0 ≤ e P) :
    |borelSource localised u (f + e) P - borelSource localised u f P| ≤ e P := by
  have hscalar : |max (f P + e P) 0 - max (f P) 0| ≤ e P := by
    by_cases hf : 0 ≤ f P
    · rw [max_eq_left hf,max_eq_left (add_nonneg hf he)]
      simp only [add_sub_cancel_left,abs_of_nonneg he,le_refl]
    · rw [max_eq_right (le_of_not_ge hf),sub_zero]
      by_cases hfe : 0 ≤ f P + e P
      · rw [max_eq_left hfe,abs_of_nonneg hfe]
        linarith only [hf]
      · simpa [max_eq_right (le_of_not_ge hfe)] using he
  cases localised
  · exact hscalar
  · by_cases h : 0 < u P
    · simpa [borelSource, indicator_of_mem (show P ∈ {z | 0 < u z} from h)] using
        hscalar
    · simp [borelSource, indicator_of_notMem (show P ∉ {z | 0 < u z} from h), he]


/-- Backward cylinders are open in the existing physical coordinate topology. -/
theorem isOpen_backwardCylinder {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    IsOpen (backwardCylinder P₀ R) := by
  have ho := isOpen_forwardCylinder (kineticReflection P₀) R hR
  rw [← kineticReflection_image_backwardCylinder P₀ R hR] at ho
  exact (kineticReflectionHomeomorph d).isOpen_image.mp ho

/-- Local continuity of the solution suffices for its positive-set source localisation. -/
theorem borelSource_memLp {d : ℕ} {D : Set (KineticPoint d)} (hD : IsOpen D)
    (localised : Bool) (u f : KineticPoint d → ℝ) (hu : ContinuousOn u D)
    {p : ℝ≥0∞} (hf : MemLp (fun P => max (f P) 0) p (volume.restrict D)) :
    MemLp (borelSource localised u f) p (volume.restrict D) := by
  cases localised
  · exact hf
  · have hS : MeasurableSet (D ∩ {P | 0 < u P}) :=
      (hu.isOpen_inter_preimage hD isOpen_Ioi).measurableSet
    have heq : (D ∩ {P | 0 < u P}).indicator (fun P => max (f P) 0) =ᵐ[volume.restrict D]
        borelSource true u f := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with P hP
      simp [indicator, hP, borelSource]
    exact (hf.indicator hS).ae_eq heq

/-- The operator change is precisely minus the coefficient Hessian contraction. -/
theorem borel_backwardOperator_sub {d : ℕ} (C A : CoefficientField d)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    backwardOperatorOfTimeVelocityCoefficient C u P -
      backwardOperatorOfTimeVelocityCoefficient A u P =
      -matrixContraction (C P.time P.velocity - A P.time P.velocity)
        (kineticVelocityHessian u P) := by
  rw [backwardOperatorOfTimeVelocityCoefficient_apply,
    backwardOperatorOfTimeVelocityCoefficient_apply]
  unfold matrixContraction
  simp only [Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  ring

end HypoellipticAleksandrov.KineticAleksandrov

