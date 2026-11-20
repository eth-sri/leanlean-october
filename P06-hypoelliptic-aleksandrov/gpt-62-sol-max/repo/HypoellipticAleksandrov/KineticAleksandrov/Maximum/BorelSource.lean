module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelContract
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Source localisation and the perturbed backward operator -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped ENNReal Topology

section
variable {d : ℕ}

/-- Backward cylinders are open in the existing physical coordinate topology. -/
theorem isOpen_backwardCylinder (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    IsOpen (backwardCylinder P₀ R) := by
  have ho := isOpen_forwardCylinder (kineticReflection P₀) R hR
  rw [← kineticReflection_image_backwardCylinder P₀ R hR] at ho
  exact (kineticReflectionHomeomorph d).isOpen_image.mp ho

/-- Local continuity of the solution suffices for its positive-set source localisation. -/
theorem borelSource_memLp {D : Set (KineticPoint d)} (hD : IsOpen D)
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
      simp only [indicator,mem_inter_iff,mem_ofPred_eq,hP,true_and,borelSource,
        ite_true]
    exact (hf.indicator hS).ae_eq heq

/-- An estimate with smooth coefficients passes to the limit when the coefficient error
vanishes in Lp on the closed cylinder. Measurable representatives supply the perturbed sources. -/
theorem borel_estimate_of_defect {Q K : Set (KineticPoint d)}
    (hQ : IsOpen Q) (hQK : Q ⊆ K) {p : ℝ} (hp : 1 ≤ p) (localised : Bool)
    {u f : KineticPoint d → ℝ} (hu : ContinuousOn u Q) (hf : Measurable f)
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p) (volume.restrict Q))
    {e : ℕ → KineticPoint d → ℝ} (he0 : ∀ j P, 0 ≤ e j P)
    (hme : ∀ j, MemLp (e j) (ENNReal.ofReal p) (volume.restrict K))
    (hte : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p) (volume.restrict K)).toReal)
      atTop (𝓝 0)) {B c : ℝ}
    (hest : ∀ j (g : KineticPoint d → ℝ), Measurable g →
      MemLp (fun P => max ((f + g) P) 0) (ENNReal.ofReal p) (volume.restrict Q) →
      g =ᵐ[volume.restrict Q] e j → ∀ P ∈ K, u P ≤ B + c *
        (eLpNorm (borelSource localised u (f + g)) (ENNReal.ofReal p) (volume.restrict Q)).toReal) :
    ∀ P ∈ K, u P ≤ B + c *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p) (volume.restrict Q)).toReal := by
  have hμ := Measure.restrict_mono_set volume hQK
  have hm j := ((hme j).mono_measure hμ).aestronglyMeasurable
  let g j := fun P => max ((hm j).mk (e j) P) 0
  have hg j : g j =ᵐ[volume.restrict Q] e j := by
    filter_upwards [(hm j).ae_eq_mk] with P hP
    simp [g, ← hP, he0 j P]
  have hgm j : Measurable (g j) := (hm j).measurable_mk.sup measurable_const
  have hgp j := ((hme j).mono_measure hμ).ae_eq (hg j).symm
  have ht : Tendsto (fun j => (eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict Q)).toReal)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun j => ?_) hte
    rw [eLpNorm_congr_ae (hg j)]
    exact ENNReal.toReal_mono (hme j).eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  have hpert j : MemLp (fun P => max ((f + g j) P) 0) (ENNReal.ofReal p)
      (volume.restrict Q) := by
    apply (hLp.add (hgp j)).of_le ((hf.add (hgm j)).sup measurable_const).aestronglyMeasurable
    filter_upwards with P
    have hg0 : 0 ≤ g j P := le_max_right _ _
    change ‖max (f P + g j P) 0‖ ≤ ‖max (f P) 0 + g j P‖
    simp only [Real.norm_of_nonneg (le_max_right _ _),
      Real.norm_of_nonneg (add_nonneg (le_max_right _ _) hg0)]
    exact max_le (add_le_add (le_max_left _ _) le_rfl) (by positivity)
  have hconv := borel_source_norm_tendsto hp (borelSource_memLp hQ localised u f hu hLp) hgp
    (fun j => (borelSource_memLp hQ localised u _ hu (hpert j)).aestronglyMeasurable)
    (fun j => .of_forall fun P => (borelSource_error_le localised u f P
      (le_max_right _ _ : 0 ≤ g j P)).trans (le_abs_self _)) ht
  exact fun P hP => ge_of_tendsto (tendsto_const_nhds.add (tendsto_const_nhds.mul hconv))
    (.of_forall fun j => hest j (g j) (hgm j) (hpert j) (hg j) P hP)

/-- The operator change is precisely minus the coefficient Hessian contraction. -/
theorem borel_backwardOperator_sub (C A : CoefficientField d)
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

end

end HypoellipticAleksandrov.KineticAleksandrov
