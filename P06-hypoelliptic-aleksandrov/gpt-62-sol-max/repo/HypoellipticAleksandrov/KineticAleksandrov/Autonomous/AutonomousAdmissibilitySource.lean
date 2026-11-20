module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilityGeometry
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import Mathlib.Tactic

/-! # Finite Borel comparison sources on compactly contained cylinders -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory

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
  have hx := hs.continuousOn_kineticPositionGradient.mono hQU
  have hh := hs.continuousOn_kineticVelocityHessian.mono hQU
  have hv : ContinuousOn (fun P : Point => P.velocity 0) (closure Q) :=
    ((continuous_apply 0).comp continuous_velocity).continuousOn
  have hx0 : ContinuousOn (fun P => kineticPositionGradient psi P 0) (closure Q) :=
    (continuous_apply 0).comp_continuousOn hx
  have hh0 : ContinuousOn (fun P => kineticVelocityHessian psi P 0 0) (closure Q) :=
    (continuous_apply 0).comp_continuousOn ((continuous_apply 0).comp_continuousOn hh)
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
  have hk := isCompact_closure_backwardCylinder P₀ R hR
  obtain ⟨B, hB⟩ := (hk.bddAbove_image hF).exists_ge (0 : ℝ)
  have hbound (P : Point) (hP : P ∈ Q) : |autonomousScalarOperator a psi P| ≤ B := by
    have hab : |a (P.position 0) (P.velocity 0)| ≤ Lam := by
      rw [abs_of_nonneg (hlam.le.trans (hb _ _).1)]
      exact (hb _ _).2
    have he : |autonomousScalarOperator a psi P| ≤ F P := by
      unfold autonomousScalarOperator F
      exact (abs_sub _ _).trans (add_le_add
        (abs_add_le _ _) (by simpa only [abs_mul] using
          mul_le_mul_of_nonneg_right hab (abs_nonneg (kineticVelocityHessian psi P 0 0))))
    exact he.trans (hB.2 _ (mem_image_of_mem F (hq hP)))
  have hmmax : AEStronglyMeasurable (fun P => max (autonomousScalarOperator a psi P) 0)
      (volume.restrict Q) := by
    have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
    have hz := TheoremA.measurable_source_indicator hQ
      (fun P => max (autonomousScalarOperator a psi P) 0) (hm.max measurable_const)
    apply hz.aestronglyMeasurable.restrict.congr
    exact TheoremA.source_indicator_ae_eq hQ _
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using volume_backwardCylinder_lt_top P₀ hR⟩
  apply MemLp.of_bound hmmax B
  filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P hP
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (hbound P hP)) hB.1

/-- The coefficient-fixed, cylinder-local Aleksandrov bound on the positivity set. -/
abbrev AutonomousLocalABP (a : ℝ → ℝ → ℝ) (P₀ : Point) (R p C : ℝ) : Prop :=
  ∀ (f u : Point → ℝ),
    Measurable (fun P : backwardCylinder P₀ R => f P) →
    ContinuousOn u (closure (backwardCylinder P₀ R)) →
    IsKineticC112On u (backwardCylinder P₀ R) →
    (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      autonomousScalarOperator a u P ≤ f P) →
    MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R)) →
    ∀ P ∈ closure (backwardCylinder P₀ R),
      u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
        C * R ^ (2 - 6 / p) *
          (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
            (volume.restrict (backwardCylinder P₀ R))).toReal

/-- A localized Aleksandrov estimate makes homogeneous autonomous solutions admissible. -/
theorem autonomous_admissible_of_localised {a : ℝ → ℝ → ℝ} {lam Lam C_A : ℝ}
    (hlam : 0 < lam) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (hestimate : ∀ P₀ R, 0 < R → AutonomousLocalABP a P₀ R 6 C_A)
    {Omega : Set Point} (hOmega : IsOpen Omega) {u : Point → ℝ}
    (hu : IsKineticC112On u Omega)
    (heq : ∀ᵐ P ∂volume.restrict Omega, autonomousScalarOperator a u P = 0) :
    IsAdmissibleSolution (autonomousCoefficient a) Omega 6 C_A u := by
  have hsup (w : Point → ℝ) (hw : IsKineticC112On w Omega)
      (heqw : ∀ᵐ P ∂volume.restrict Omega, autonomousScalarOperator a w P = 0) :
      IsAdmissibleSupersolution (autonomousCoefficient a) Omega 6 C_A w := by
    refine ⟨hw.continuousOn, ?_⟩
    intro P₀ R hR hQ psi hpsi
    obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular hpsi
    have hQQ : backwardCylinder P₀ R ⊆ Omega := subset_closure.trans hQ
    have hpr := _root_.HypoellipticAleksandrov.Parabolic.IsKineticC112On.mono hps (subset_closure.trans hUQ)
    have hwr := _root_.HypoellipticAleksandrov.Parabolic.IsKineticC112On.mono hw hQQ
    have hneg := comparison_regular_const_mul hwr (-1)
    have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
    have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator a (fun Q => psi Q - w Q) P ≤
          autonomousScalarOperator a psi P := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
        ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
      have hadd := autonomous_operator_add hpr hneg a hP
      have hmul := autonomous_operator_const_mul hwr (-1) a hP
      simp only [neg_one_mul, ← sub_eq_add_neg] at hadd hmul
      rw [hadd, hmul, he]
      simp only [neg_zero, add_zero, le_refl]
    obtain ⟨hmeas, hLp⟩ := autonomous_test_source hlam ha hb P₀ R hR hpsi
    have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
      ext P
      exact sub_pos
    have hbnd := hestimate P₀ R hR (autonomousScalarOperator a psi)
      (fun P => psi P - w P) hmeas
      (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hop hLp
    have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
        sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
          C_A * R ^ (2 - (4 * (1 : ℝ) + 2) / 6) *
            (eLpNorm (localizedSource (autonomousCoefficient a) psi w) (ENNReal.ofReal 6)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
      simpa only [hn, localizedSource, backwardOperator_autonomous,
        show 4 * (1 : ℝ) + 2 = 6 by norm_num] using hbnd
    apply csSup_le
    · exact (backwardCylinder_nonempty P₀ hR).closure.image _
    · rintro y ⟨P, hP, rfl⟩
      simpa only [Nat.cast_one] using hbnd' P hP
  refine ⟨hsup u hu heq, ?_⟩
  have hneg : IsKineticC112On (fun P => -u P) Omega := by
    simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
  apply hsup (fun P => -u P) hneg
  filter_upwards [heq, ae_restrict_mem hOmega.measurableSet] with P he hP
  have hm := autonomous_operator_const_mul hu (-1) a hP
  simpa only [neg_one_mul, he, neg_zero] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
