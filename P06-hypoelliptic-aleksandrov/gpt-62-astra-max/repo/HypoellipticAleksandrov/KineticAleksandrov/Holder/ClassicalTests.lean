module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Tactic

/-! # Smooth tests for full measurable coefficients

On a compact cylinder the classical jet is bounded and each entry of the coefficient
is essentially bounded. Thus the positive part of the operator is in every finite Lp.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open HypoellipticAleksandrov Parabolic Evolution TheoremA Set MeasureTheory
open scoped ENNReal MatrixOrder
variable {d : ℕ} {A : FullKineticCoefficient d} {lam Lam : ℝ}

theorem IsSmoothNear.regular {ψ : KineticPoint d → ℝ} {E : Set (KineticPoint d)}
    (h : IsSmoothNear ψ E) : IsKineticC112On ψ E := by
  obtain ⟨U, hU, hEU, hs⟩ := h
  apply comparison_regular_mono (D := U) _ hEU
  exact isKineticC112On_of_contDiffOn hU (hs.comp (evolutionProdCLE d).contDiff.contDiffOn
    (fun x hx => ⟨evolutionHomeomorph d x, hx, rfl⟩))

/-- Local source data for comparison with a smooth test. -/
theorem classical_test_source (hA : FullElliptic lam Lam A) (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) {ψ : KineticPoint d → ℝ}
    (hψ : IsKineticC112On ψ (closure (backwardCylinder P₀ R))) (p : ℝ≥0∞) :
    Measurable (fun P : backwardCylinder P₀ R => backwardOperator A ψ P) ∧
    MemLp (fun P => max (backwardOperator A ψ P) 0) p
      (volume.restrict (backwardCylinder P₀ R)) := by
  let Q := backwardCylinder P₀ R
  let μ := volume.restrict Q
  have hmQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  have hk := isCompact_closure_backwardCylinder P₀ R hR
  let : IsFiniteMeasure μ := ⟨by simpa [μ, Q] using volume_backwardCylinder_lt_top P₀ hR⟩
  have htransport : ContinuousOn (fun P => kineticTimeDerivative ψ P +
      PDE.vecDot P.velocity (kineticPositionGradient ψ P)) (closure Q) := by
    apply hψ.continuousOn_kineticTimeDerivative.add
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_velocity).continuousOn.mul
      ((continuous_apply i).comp_continuousOn hψ.continuousOn_kineticPositionGradient)
  have hH (i j : Fin d) : ContinuousOn (fun P => kineticVelocityHessian ψ P i j) (closure Q) :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn
      hψ.continuousOn_kineticVelocityHessian)
  have hB (i j : Fin d) : Measurable (fun P => fullKineticCoefficientAt A P i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA.1)
  constructor
  · apply (htransport.mono subset_closure).domRestrict.measurable.sub
    exact Finset.measurable_fun_sum _ fun i _ => Finset.measurable_fun_sum _ fun j _ =>
      ((hB i j).comp measurable_subtype_coe).mul ((hH i j).mono subset_closure).domRestrict.measurable
  have hcont {f : KineticPoint d → ℝ} (hf : ContinuousOn f (closure Q)) : MemLp f p μ := by
    obtain ⟨B, hB⟩ := hk.bddAbove_image hf.norm
    exact MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable hmQ) B
      ((ae_restrict_mem hmQ).mono fun P hP => hB (mem_image_of_mem _ (subset_closure hP)))
  have hcoef (i j : Fin d) : MemLp (fun P => fullKineticCoefficientAt A P i j) ∞ μ := by
    apply MemLp.of_bound (hB i j).aestronglyMeasurable _
    filter_upwards [ae_restrict_of_ae hA.2.2.1, ae_restrict_of_ae hA.2.2.2] with P hl hu
    exact coefficient_entry_abs_le_of_ellipticity hl hu i j
  apply MemLp.sup _ (MemLp.zero : MemLp (0 : KineticPoint d → ℝ) p μ)
  apply (hcont htransport).sub
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (hcoef i j).mul (hcont (hH i j))

end HypoellipticAleksandrov.KineticAleksandrov.Holder
