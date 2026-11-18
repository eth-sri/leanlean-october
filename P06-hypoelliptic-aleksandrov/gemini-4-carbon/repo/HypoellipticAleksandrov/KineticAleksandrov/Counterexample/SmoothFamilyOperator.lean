module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyNativeMeasure
public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Analysis.Matrix.Normed
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySource
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.Evolution Filter MeasureTheory
open scoped Matrix.Norms.Elementwise Topology ENNReal MatrixOrder
section
open MeasureTheory ContinuousLinearMap
open Filter
open scoped MatrixOrder Convolution Matrix.Norms.Elementwise Topology

/-- Use the existing entrywise measurable structure locally. -/
local instance matrixMeasurableSpace (d : ℕ) : MeasurableSpace (PDE.Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

/-- The entrywise measurable structure is Borel. -/
local instance matrixBorelSpace (d : ℕ) : BorelSpace (PDE.Mat d) := by
  change BorelSpace (Fin d → Fin d → ℝ)
  infer_instance

/-- The finite entrywise product topology is second countable. -/
local instance matrixSecondCountable (d : ℕ) : SecondCountableTopology (PDE.Mat d) := by
  change SecondCountableTopology (Fin d → Fin d → ℝ)
  infer_instance

/-- The entrywise topology has its existing finite product metric. -/
local instance matrixPseudoMetrizable (d : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
  infer_instance

/-- The existing entrywise norm is continuous. -/
local instance matrixContinuousENorm (d : ℕ) : ContinuousENorm (PDE.Mat d) := by
  change ContinuousENorm (Fin d → Fin d → ℝ)
  infer_instance

/-- Loewner upper intervals are closed in the entrywise topology. -/
local instance matrixClosedIci (d : ℕ) : ClosedIciTopology (PDE.Mat d) where
  isClosed_Ici A := by
    change IsClosed {B : PDE.Mat d | A ≤ B}
    simp only [Matrix.le_iff]
    exact Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)


/-- Spatial convolution of an autonomous matrix field. -/
def mollifiedMatrix {d : ℕ} (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) :
    (PDE.Vec d × PDE.Vec d) → PDE.Mat d :=
  phi.normed volume ⋆[lsmul ℝ ℝ, volume] A


/-- Positive normalized convolution preserves the exact lower and upper ellipticity
constants; local integrability is the genuine analytic hypothesis for this general lemma. -/
theorem smooth_coefficients_same_bounds_of_locallyIntegrable {d : ℕ}
    (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (hA : LocallyIntegrable A volume)
    (lam Lam : ℝ)
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d))
    (q : PDE.Vec d × PDE.Vec d) :
    lam • (1 : PDE.Mat d) ≤ mollifiedMatrix phi A q ∧
      mollifiedMatrix phi A q ≤ Lam • (1 : PDE.Mat d)  := by
  have matrix_orderedModule :
      IsOrderedModule ℝ (PDE.Mat d) := by
    apply IsOrderedModule.of_smul_nonneg
    intro a ha B hB
    rw [Matrix.le_iff] at hB ⊢
    simpa using (show B.PosSemidef by simpa using hB).smul ha
  have : IsOrderedModule ℝ (PDE.Mat d) := matrix_orderedModule
  have hi := (phi.hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
    (phi.contDiff_normed (n := 0)).continuous hA q
  have hc (c : ℝ) : Integrable (fun y => phi.normed volume y •
      (c • (1 : PDE.Mat d))) volume := phi.integrable_normed.smul_const _
  have he (c : ℝ) : (∫ y, phi.normed volume y • (c • 1)) =
      c • (1 : PDE.Mat d) := by
    rw [integral_smul_const, phi.integral_normed, one_smul]
  constructor
  · rw [← he lam]
    exact @integral_mono _ (PDE.Mat d) _ _ _ volume Matrix.instPartialOrder
      Matrix.instIsOrderedAddMonoid (matrix_orderedModule) (matrixClosedIci d)
      _ _ (hc lam) hi (fun y =>
        smul_le_smul_of_nonneg_left (hbound (q - y)).1 (phi.nonneg_normed y))
  · rw [← he Lam]
    exact @integral_mono _ (PDE.Mat d) _ _ _ volume Matrix.instPartialOrder
      Matrix.instIsOrderedAddMonoid (matrix_orderedModule) (matrixClosedIci d)
      _ _ hi (hc Lam) (fun y =>
        smul_le_smul_of_nonneg_left (hbound (q - y)).2 (phi.nonneg_normed y))


/-- A Borel matrix field in a fixed scalar Loewner interval is locally integrable
on the native spatial carrier, with no continuity assumption. -/
theorem locallyIntegrable_matrix_of_ellipticity {d : ℕ}
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun y => A y i k))
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d)) :
    LocallyIntegrable A volume := by
  have hC : 0 ≤ 3 * (|lam| + |Lam|) := by positivity
  intro q
  obtain ⟨D, hD, hDf⟩ :=
    (volume : Measure (PDE.Vec d × PDE.Vec d)).finiteAt_nhds q
  refine ⟨D, hD, IntegrableOn.of_bound hDf (measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (hA i))).aestronglyMeasurable
    (3 * (|lam| + |Lam|)) ?_⟩
  filter_upwards [] with y
  apply (Matrix.norm_le_iff hC).2
  intro i k
  rw [Real.norm_eq_abs]
  exact HypoellipticAleksandrov.Parabolic.coefficient_entry_abs_le_of_ellipticity
    (hbound y).1 (hbound y).2 i k

/-- Measurable elliptic coefficients can be smoothed without changing either bound. -/
theorem smooth_coefficients_same_bounds {d : ℕ}
    (phi : ContDiffBump (0 : PDE.Vec d × PDE.Vec d))
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun y => A y i k))
    (hbound : ∀ y, lam • (1 : PDE.Mat d) ≤ A y ∧ A y ≤ Lam • (1 : PDE.Mat d)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedMatrix phi A) ∧
      ∀ q, lam • (1 : PDE.Mat d) ≤ mollifiedMatrix phi A q ∧
        mollifiedMatrix phi A q ≤ Lam • (1 : PDE.Mat d)  := by
  have mollifiedMatrix_contDiff (hA : LocallyIntegrable A volume) : ContDiff ℝ (⊤ : ℕ∞) (mollifiedMatrix phi A) :=
    (phi.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (lsmul ℝ ℝ)
        phi.contDiff_normed hA
  have hi := locallyIntegrable_matrix_of_ellipticity A lam Lam hA hbound
  exact ⟨mollifiedMatrix_contDiff hi,
    smooth_coefficients_same_bounds_of_locallyIntegrable phi A hi lam Lam hbound⟩


end

/-- Native joint smoothness supplies all genuine kinetic derivative continuity properties. -/
theorem isKineticC112On_univ_of_joint_smooth {d : ℕ} (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      u ((KineticPoint.equivProd d).symm z))) : IsKineticC112On u univ := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d) := by
    simpa using!
      hu.comp (evolutionProdCLE d).contDiff
  exact TheoremA.isKineticC112On_of_contDiffOn isOpen_univ
    (by simpa using hs.contDiffOn)

/-- Native joint smoothness gives continuity of the actual kinetic velocity Hessian. -/
theorem continuous_kineticVelocityHessian_of_joint_smooth {d : ℕ}
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      u ((KineticPoint.equivProd d).symm z))) : Continuous (kineticVelocityHessian u) :=
  continuousOn_univ.mp
    (isKineticC112On_univ_of_joint_smooth u hu).continuousOn_kineticVelocityHessian

/-- The Hessian of each fixed smooth function is bounded on the entire cylinder.
The bound is chosen after the function and is not claimed uniform across a sequence. -/
theorem kineticVelocityHessian_bound_on_cylinder {d : ℕ}
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      u ((KineticPoint.equivProd d).symm z))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ P ∈ backwardCylinder P₀ R, ∀ i k,
      ‖kineticVelocityHessian u P i k‖ ≤ M := by
  obtain ⟨K, hK, hQK⟩ := backwardCylinder_subset_compact P₀ R hR
  obtain ⟨B, hb⟩ := (hK.image (continuous_kineticVelocityHessian_of_joint_smooth u hu)).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro P hP i k
  apply (Matrix.norm_le_iff (le_max_right B 0)).mp _ i k
  exact (hb _ ⟨P, hQK hP, rfl⟩).trans (le_max_left _ _)



/-- Fixed-function coefficient mollification has vanishing full contraction error in Lp. -/
theorem smooth_coefficient_error_tendsto {d : ℕ}
    (A : XV d → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun q => A q i k))
    (hbound : ∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q)))
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun P => matrixContraction
      (mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) -
        A (P.position, P.velocity)) (kineticVelocityHessian u P))
      p (volume.restrict (backwardCylinder P₀ R))) atTop (𝓝 0)   := by
  have ae_spatial_lift {P : XV d → Prop} (hP : ∀ᵐ q ∂volume, P q) :
      ∀ᵐ z : KineticPoint d ∂volume, P (z.position, z.velocity) := by
    have hs : Measure.QuasiMeasurePreserving Prod.snd
        (volume : Measure (ℝ × XV d)) (volume : Measure (XV d)) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_snd
    exact (hs.comp (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving).ae hP
  have ae_tendsto_mollifiedMatrix :
      ∀ᵐ q ∂volume,
      Tendsto (fun n => mollifiedMatrix (standardMollifierSequence n) A q)
        atTop (𝓝 (A q)) := by
    exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      standardMollifierSequence_rOut_tendsto
      (Filter.Eventually.of_forall standardMollifierSequence_radius_ratio)
      (locallyIntegrable_matrix_of_ellipticity A lam Lam hA hbound)
  let C := 3 * (|lam| + |Lam|)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨M, hM, hH⟩ := kineticVelocityHessian_bound_on_cylinder P₀ R hR u hu
  have hsp : Continuous (fun P : KineticPoint d => (P.position, P.velocity)) :=
    continuous_position.prodMk continuous_velocity
  let : IsFiniteMeasure (volume.restrict (backwardCylinder P₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact backwardCylinder_volume_lt_top P₀ R hR⟩
  have hs n := smooth_coefficients_same_bounds (standardMollifierSequence n)
    A lam Lam hA hbound
  have hc n i k : Continuous
      (fun q => mollifiedMatrix (standardMollifierSequence n) A q i k) :=
    (continuous_apply k).comp ((continuous_apply i).comp (hs n).1.continuous)
  refine bounded_convergence_eLpNorm (volume.restrict (backwardCylinder P₀ R)) p hp0 hp
    (fun n P => matrixContraction
      (mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) -
        A (P.position, P.velocity)) (kineticVelocityHessian u P))
    ?_ ((d : ℝ) * d * (2 * C * M)) ?_ ?_
  · intro n
    apply AEStronglyMeasurable.restrict
    apply Measurable.aestronglyMeasurable
    unfold matrixContraction
    simp
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro k hk
    exact (((hc n i k).measurable.comp hsp.measurable).sub
      ((hA i k).comp hsp.measurable)).mul
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_kineticVelocityHessian_of_joint_smooth u hu))).measurable)
  · intro n
    apply ae_restrict_of_forall_mem ((isOpen_backwardCylinder P₀ R hR).measurableSet)
    intro P hP
    have hb i k : ‖(mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) i k -
        A (P.position, P.velocity) i k) * kineticVelocityHessian u P i k‖ ≤ 2 * C * M := by
      rw [norm_mul]
      apply mul_le_mul _ (hH P hP i k) (norm_nonneg _) (by positivity)
      exact (norm_sub_le _ _).trans (by
        simp
        linarith only [(coefficient_entry_abs_le_of_ellipticity ((hs n).2 (P.position, P.velocity)).1 ((hs n).2 (P.position, P.velocity)).2 i k), (coefficient_entry_abs_le_of_ellipticity (hbound (P.position, P.velocity)).1 (hbound (P.position, P.velocity)).2 i k)])
    unfold matrixContraction
    simp
    calc
      _ ≤ ∑ i : Fin d, ∑ k : Fin d, ‖(mollifiedMatrix (standardMollifierSequence n) A
          (P.position, P.velocity) i k - A (P.position, P.velocity) i k) *
          kineticVelocityHessian u P i k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ _i : Fin d, ∑ _k : Fin d, 2 * C * M :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hb i k))
      _ = _ := by
        simp
        ring
  · filter_upwards [ae_restrict_of_ae (ae_spatial_lift
      (ae_tendsto_mollifiedMatrix))] with P hP
    have he i k : Tendsto (fun n =>
        (mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) i k -
          A (P.position, P.velocity) i k) * kineticVelocityHessian u P i k)
        atTop (𝓝 0) := by
      have h := ((continuous_apply k).comp (continuous_apply i)).continuousAt.tendsto.comp hP
      change Tendsto (fun n => mollifiedMatrix (standardMollifierSequence n) A
        (P.position, P.velocity) i k) atTop (𝓝 (A (P.position, P.velocity) i k)) at h
      simpa using!
        (h.sub_const (A (P.position, P.velocity) i k)).mul_const
          (kineticVelocityHessian u P i k)
    simpa using! (tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun k _ => he i k)))


/-- Entrywise measurable autonomous coefficients and genuine smooth jets
give a measurable operator. -/
theorem measurable_backwardOperator_of_joint_smooth {d : ℕ}
    (A : XV d → PDE.Mat d) (hA : ∀ i k, Measurable (fun q => A q i k))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q))) :
    Measurable (backwardOperator (fun _t x v => A (x, v)) u) := by
  have hr := isKineticC112On_univ_of_joint_smooth u hu
  have hv i k : Measurable (fun P => kineticVelocityHessian u P i k) :=
    ((continuous_apply k).comp ((continuous_apply i).comp
      (continuousOn_univ.mp hr.continuousOn_kineticVelocityHessian))).measurable
  have hsp : Measurable (fun P : KineticPoint d => (P.position, P.velocity)) :=
    (continuous_position.prodMk continuous_velocity).measurable
  have hT : Measurable (fun P => PDE.vecDot P.velocity (kineticPositionGradient u P)) := by
    unfold PDE.vecDot
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp continuous_velocity.measurable).mul
        ((measurable_pi_apply i).comp ((continuousOn_univ.mp hr.continuousOn_kineticPositionGradient).measurable)))
  have hC : Measurable (fun P => matrixContraction (A (P.position, P.velocity))
      (kineticVelocityHessian u P)) := by
    unfold matrixContraction
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun k _ =>
      ((hA i k).comp hsp).mul
        (hv i k)))
  exact (((continuousOn_univ.mp hr.continuousOn_kineticTimeDerivative).measurable).add hT).sub hC

/-- The full backward-operator change is minus the exact coefficient Hessian error. -/
theorem backwardOperator_coefficient_change {d : ℕ} (A B : XV d → PDE.Mat d)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    backwardOperator (fun _t x v => B (x, v)) u P =
      backwardOperator (fun _t x v => A (x, v)) u P -
        matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
          (kineticVelocityHessian u P) := by
  unfold backwardOperator fullKineticCoefficientAt matrixContraction
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The positive source norm increases by at most the full contraction-error norm. -/
theorem positive_source_norm_le_coefficient_error {d : ℕ}
    (A B : XV d → PDE.Mat d)
    (hA : ∀ i k, Measurable (fun q => A q i k))
    (hB : ∀ i k, Measurable (fun q => B q i k))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q)))
    (nu : Measure (KineticPoint d)) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (fun P => max (backwardOperator (fun _t x v => B (x, v)) u P) 0) p nu ≤
      eLpNorm (fun P => max (backwardOperator (fun _t x v => A (x, v)) u P) 0) p nu +
      eLpNorm (fun P => matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
        (kineticVelocityHessian u P)) p nu := by
  let E := fun P => matrixContraction (B (P.position, P.velocity) - A (P.position, P.velocity))
    (kineticVelocityHessian u P)
  have hmb := measurable_backwardOperator_of_joint_smooth B hB u hu
  have he : Measurable E := by
    have h := (measurable_backwardOperator_of_joint_smooth A hA u hu).sub hmb
    convert h using 1
    funext P
    simp only [Pi.sub_apply]
    rw [backwardOperator_coefficient_change A B u P]
    ring
  have hm := eLpNorm_mono_ae_real (p := p) (hmb.max (measurable_const (a := 0))).aestronglyMeasurable (μ := nu)
    (Filter.Eventually.of_forall (fun P => show
      ‖max (backwardOperator (fun _t x v => B (x, v)) u P) 0‖ ≤
        max (backwardOperator (fun _t x v => A (x, v)) u P) 0 + ‖E P‖ from by
      rw [Real.norm_of_nonneg (le_max_right _ _), backwardOperator_coefficient_change A B u P]
      simpa using!
        positive_part_add_le (backwardOperator (fun _t x v => A (x, v)) u P)
          (max (backwardOperator (fun _t x v => A (x, v)) u P) 0) (-(E P))
          (le_max_right _ _) (le_max_left _ _)))
  exact hm.trans ((eLpNorm_add_le hp).trans_eq
    (by rw [eLpNorm_norm E he.aestronglyMeasurable]))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

