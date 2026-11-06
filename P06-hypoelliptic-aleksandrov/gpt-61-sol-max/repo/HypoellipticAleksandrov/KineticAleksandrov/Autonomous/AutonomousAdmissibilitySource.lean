module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilityGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import Mathlib.Tactic

/-! # Finite Borel comparison sources on compactly contained cylinders -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Parabolic Holder Set MeasureTheory

/-- Smooth-near tests have measurable and finite positive operator sources on a cylinder. -/
theorem autonomous_test_source {a : ℝ → ℝ → ℝ} {lam Lam : ℝ}
    (hlam : 0 < lam)
    (ha : Measurable (Function.uncurry a)) (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (P₀ : Point) (R : ℝ) (hR : 0 < R) {psi : Point → ℝ}
    (hpsi : IsSmoothNear psi (closure (backwardCylinder P₀ R))) :
    Measurable (fun P : backwardCylinder P₀ R => autonomousScalarOperator a psi P) ∧
      MemLp (fun P => max (autonomousScalarOperator a psi P) 0) (ENNReal.ofReal 6)
        (volume.restrict (backwardCylinder P₀ R)) := by

  let Q := backwardCylinder P₀ R
  obtain ⟨U, _hU, hQU, hs⟩ := smoothNear_regular hpsi
  have ht := hs.continuousOn_kineticTimeDerivative.mono hQU


  have hv : ContinuousOn (fun P : Point => P.velocity 0) (closure Q) :=
    ((continuous_apply 0).comp continuous_velocity).continuousOn
  have hx0  :=
    (continuous_apply 0).comp_continuousOn (hs.continuousOn_kineticPositionGradient.mono hQU)
  have hh0  :=
    (continuous_apply 0).comp_continuousOn ((continuous_apply 0).comp_continuousOn (hs.continuousOn_kineticVelocityHessian.mono hQU))
  have hq : Q ⊆ closure Q := subset_closure
  have hm : Measurable (fun P : Q => autonomousScalarOperator a psi P) := by
    have hcoef : Measurable (fun P : Point => a (P.position 0) (P.velocity 0)) := ha.comp
      (((continuous_apply 0).comp continuous_position).measurable.prodMk
        (((continuous_apply 0).comp continuous_velocity).measurable))
    exact ((ht.mono hq).domRestrict.measurable.add
      ((hv.mono hq).domRestrict.measurable.mul
        (hx0.mono hq).domRestrict.measurable)).sub
      ((hcoef.comp measurable_subtype_coe).mul (hh0.mono hq).domRestrict.measurable)
  refine ⟨hm, ?_⟩
  let F  := fun P => |kineticTimeDerivative psi P| +
    |P.velocity 0 * kineticPositionGradient psi P 0| + Lam *
      |kineticVelocityHessian psi P 0 0|
  have hF : ContinuousOn F (closure Q) := ht.abs.add (hv.mul hx0).abs |>.add
    (continuousOn_const.mul hh0.abs)

  obtain ⟨B, hB⟩ := ((isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image hF).exists_ge (0 )
  have hbound (P : Point) (hP : P ∈ Q) : |autonomousScalarOperator a psi P| ≤ B := by


    exact (show |autonomousScalarOperator a psi P| ≤ F P by
        unfold autonomousScalarOperator F
        exact (abs_sub _ _).trans (add_le_add
          (abs_add_le _ _) (by simpa only [abs_mul] using
            mul_le_mul_of_nonneg_right (by
                rw [abs_of_nonneg (hlam.le.trans (hb _ _).1)]
                exact (hb _ _).2) (abs_nonneg (kineticVelocityHessian psi P 0 0))))).trans (hB.2 _ (mem_image_of_mem F (hq hP)))

  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using volume_backwardCylinder_lt_top P₀ hR⟩
  apply MemLp.of_bound (by
      have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
      have hz := TheoremA.measurable_source_indicator hQ
        (((fun P => max (autonomousScalarOperator a psi P) 0))) (hm.max measurable_const)
      apply hz.aestronglyMeasurable.restrict.congr
      exact TheoremA.source_indicator_ae_eq hQ _) B
  filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P hP
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (hbound P hP)) hB.1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
