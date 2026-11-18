module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityCalculus
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory Evolution TheoremA
open scoped MatrixOrder

/-- The scalar autonomous lift is Borel on the literal kinetic carrier. -/
theorem autonomous_lift_measurable {a : ℝ → ℝ → ℝ}
    (ha : Measurable (Function.uncurry a)) :
    Measurable (fullKineticCoefficientAt (autonomousCoefficient a)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact ha.comp (((continuous_apply 0).comp continuous_position).measurable.prodMk
    (((continuous_apply 0).comp continuous_velocity).measurable))

/-- The one-dimensional lift is symmetric at every point. -/
theorem autonomous_lift_symm (a : ℝ → ℝ → ℝ) (P : Point) :
    (fullKineticCoefficientAt (autonomousCoefficient a) P).IsSymm := by
  ext i j
  rfl

/-- The scalar range gives pointwise matrix ellipticity without an exceptional set. -/
theorem autonomous_lift_elliptic {a : ℝ → ℝ → ℝ} {lam Lam : ℝ}
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (P : Point) :
    lam • (1 : PDE.Mat 1) ≤ fullKineticCoefficientAt (autonomousCoefficient a) P ∧
      fullKineticCoefficientAt (autonomousCoefficient a) P ≤ Lam • (1 : PDE.Mat 1) := by
  have he : fullKineticCoefficientAt (autonomousCoefficient a) P =
      a (P.position 0) (P.velocity 0) • 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [fullKineticCoefficientAt, autonomousCoefficient]
  rw [he]
  have hI : (0 : PDE.Mat 1) ≤ 1 :=
    Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one
  exact ⟨smul_le_smul_of_nonneg_right (hb _ _).1 hI,
    smul_le_smul_of_nonneg_right (hb _ _).2 hI⟩

/-- Source-near smooth tests have the existing anisotropic classical regularity. -/
theorem smoothNear_regular {psi : Point → ℝ} {E : Set Point}
    (hpsi : IsSmoothNear psi E) : ∃ U : Set Point,
      IsOpen U ∧ E ⊆ U ∧ IsKineticC112On psi U := by
  obtain ⟨U, hU, hEU, hs⟩ := hpsi
  refine ⟨U, hU, hEU, isKineticC112On_of_contDiffOn hU ?_⟩
  have h := hs.comp (evolutionProdCLE 1).contDiff.contDiffOn (by
    intro x hx
    exact ⟨evolutionHomeomorph 1 x, hx, rfl⟩)
  exact h

/-- The full backward operator is additive on the existing C112 class. -/
theorem autonomous_operator_add {u v : Point → ℝ} {D : Set Point}
    (hu : IsKineticC112On u D) (hv : IsKineticC112On v D)
    (a : ℝ → ℝ → ℝ) {P : Point} (hP : P ∈ D) :
    autonomousScalarOperator a (fun Q => u Q + v Q) P =
      autonomousScalarOperator a u P + autonomousScalarOperator a v P := by
  rw [autonomousScalarOperator_apply,
    comparison_time_add (hu.timeSlice_differentiableAt hP) (hv.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => u Q + v Q) P =
      kineticPositionGradient u P + kineticPositionGradient v P from classicalGradient_add
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
        ((hv.positionSlice_contDiffAt hP).differentiableAt (by norm_num)),
    comparison_hessian_add (hu.velocitySlice_contDiffAt hP) (hv.velocitySlice_contDiffAt hP)]
  simp
  ring

/-- Scalar multiplication commutes with the autonomous operator on C112 functions. -/
theorem autonomous_operator_const_mul {u : Point → ℝ} {D : Set Point}
    (hu : IsKineticC112On u D) (c : ℝ) (a : ℝ → ℝ → ℝ)
    {P : Point} (hP : P ∈ D) :
    autonomousScalarOperator a (fun Q => c * u Q) P = c * autonomousScalarOperator a u P := by
  rw [autonomousScalarOperator_apply,
    show kineticTimeDerivative (fun Q => c * u Q) P = c * kineticTimeDerivative u P from
      deriv_const_mul c (hu.timeSlice_differentiableAt hP),
    show kineticPositionGradient (fun Q => c * u Q) P = c • kineticPositionGradient u P from
      classicalGradient_const_mul c
        ((hu.positionSlice_contDiffAt hP).differentiableAt (by norm_num))]
  have hh : kineticVelocityHessian (fun Q => c * u Q) P = c • kineticVelocityHessian u P := by
    simp only [kineticVelocityHessian_eq_sliceHessian]
    exact sliceHessian_const_mul c (hu.velocitySlice_contDiffAt hP)
  rw [hh]
  simp
  ring


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
  have hv : ContinuousOn (fun P => P.velocity 0) (closure Q) :=
    ((continuous_apply 0).comp continuous_velocity).continuousOn
  have hx0 :=
    (continuous_apply 0).comp_continuousOn (hs.continuousOn_kineticPositionGradient.mono hQU)
  have hh0 :=
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
  let F : Point → ℝ := fun P => |kineticTimeDerivative psi P| +
    |P.velocity 0 * kineticPositionGradient psi P 0| + Lam *
      |kineticVelocityHessian psi P 0 0|
  have hF : ContinuousOn F (closure Q) := ht.abs.add (hv.mul hx0).abs |>.add
    (continuousOn_const.mul hh0.abs)
  obtain ⟨B, hB⟩ := ((isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image hF).exists_ge 0
  have hbound (P : Point) (hP : P ∈ Q) : |autonomousScalarOperator a psi P| ≤ B := by
    have hab : |a (P.position 0) (P.velocity 0)| ≤ Lam := by
      rw [abs_of_nonneg (hlam.le.trans (hb _ _).1)]
      exact (hb _ _).2
    have he : |autonomousScalarOperator a psi P| ≤ F P := by
      unfold autonomousScalarOperator F
      exact (abs_sub _ _).trans (add_le_add
        (abs_add_le _ _) (by simpa using
          mul_le_mul_of_nonneg_right hab (abs_nonneg (kineticVelocityHessian psi P 0 0))))
    exact he.trans (hB.2 _ (mem_image_of_mem F (hq hP)))
  have hmmax : AEStronglyMeasurable (fun P => max (autonomousScalarOperator a psi P) 0)
      (volume.restrict Q) := by
    have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
    apply (TheoremA.measurable_source_indicator hQ (fun P => max (autonomousScalarOperator a psi P) 0) (hm.max measurable_const)).aestronglyMeasurable.restrict.congr
    exact TheoremA.source_indicator_ae_eq hQ _
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa using volume_backwardCylinder_lt_top P₀ hR⟩
  apply MemLp.of_bound hmmax B
  filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P hP
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (hbound P hP)) hB.1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

