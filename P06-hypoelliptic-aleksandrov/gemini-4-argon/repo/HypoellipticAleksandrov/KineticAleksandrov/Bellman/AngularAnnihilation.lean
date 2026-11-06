module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationPositive
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationNegative
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationNegativeMoments
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationTailReflection
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailGrowth
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationMoments
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationOrigin
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegrated
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTail
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailLimitCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTail
import Mathlib.MeasureTheory.Group.Integral
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesComparison
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesFlux
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegration
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationComparison
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquation
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationProductIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationRadialIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationRadialTest
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSeparated
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTest
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestDerivatives
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestSupport
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationVelocity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTailDensity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeDensity
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeFunctionals
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveWeak
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact

/-! # Vanishing of both angular measures and the positive-position part -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open Filter
open scoped Topology

/- At degree at least three every angular pair with actual densities and finite tails
vanishes. -/
theorem bellmanAdjointPair_positive_position_zero (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    μ {q | 0 < q.val.1} = 0 ∧ η {q | 0 < q.val.1} = 0 := by
  obtain ⟨F, H, f, h, J, hrep, hd, ht⟩ : ∃ (F H : Measure ℝ) (f h J : ℝ → ℝ),
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      (
      F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
      LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
      (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
      (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
      (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y)) ∧
      IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
    obtain ⟨F, H, hrep, hang⟩ : ∃ F H : Measure ℝ,
        (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
          η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
        IsBellmanAngularAdjointPair 1 R β F H := by
      obtain ⟨F, H, hrep, hF, hFi, hH, hHi, hlo, hhi⟩ : ∃ F H : Measure ℝ,
          (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
            η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
          IsFiniteMeasureOnCompacts F ∧ Measure.InnerRegular F ∧
          IsFiniteMeasureOnCompacts H ∧ Measure.InnerRegular H ∧ F ≤ H ∧
          H ≤ ENNReal.ofReal R • F := by
        refine ⟨bellmanAngularMeasure β μ, bellmanAngularMeasure β η, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨bellmanAngularMeasure_representation β μ hp.1.1 hp.2.2.2.2.2.2.1,
            bellmanAngularMeasure_representation β η hp.2.1.1 hp.2.2.2.2.2.2.2⟩
        · exact bellmanAngularMeasure_finiteOnCompacts β μ hp.1.1
        · exact bellmanAngularMeasure_innerRegular β μ hp.1.1
        · exact bellmanAngularMeasure_finiteOnCompacts β η hp.2.1.1
        · exact bellmanAngularMeasure_innerRegular β η hp.2.1.1
        · apply bellmanAngularMeasure_mono
          simpa only [ENNReal.ofReal_one, one_smul] using hp.2.2.2.1
        · rw [← bellmanAngularMeasure_smul]
          exact bellmanAngularMeasure_mono β hp.2.2.2.2.1
      let : IsFiniteMeasureOnCompacts F := hF
      let : IsFiniteMeasureOnCompacts H := hH
      refine ⟨F, H, hrep, hF, hFi, hH, hHi, ?_, hhi, ?_⟩
      · simpa only [ENNReal.ofReal_one, one_smul] using hlo
      intro φ hφ hcφ
      obtain ⟨ζ, hζ, hcζ, hsζ, hK, hrel⟩ : ∃ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
          tsupport ζ ⊆ Ioo (1 : ℝ) 3 ∧
          0 < (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) ∧
          (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) =
            (β - 2) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
        let ζ : ContDiffBump (2 : ℝ) :=
          { rIn := 1 / 4
            rOut := 1 / 2
            rIn_pos := by norm_num
            rIn_lt_rOut := by norm_num }
        have hs : tsupport (ζ : ℝ → ℝ) ⊆ Ioo (1 : ℝ) 3 := by
          rw [ζ.tsupport_eq]
          intro s hs
          rw [Metric.mem_closedBall, Real.dist_eq] at hs
          change |s - 2| ≤ 1 / 2 at hs
          constructor <;> linarith [abs_le.mp hs]
        have hsp : tsupport (ζ : ℝ → ℝ) ⊆ Ioi (0 : ℝ) :=
          fun s hsζ => lt_trans (by norm_num : (0 : ℝ) < 1) (hs hsζ).1
        have hc : HasCompactSupport (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2) := by
          convert! (bellmanRadialTest_compact ζ ζ.hasCompactSupport hsp).mul_right
            (f' := fun s : BellmanPositiveTime => (s.val ^ 2)⁻¹) using 1
        have hcont : Continuous (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2) :=
          (ζ.continuous.comp continuous_subtype_val).div (continuous_subtype_val.pow 2)
            (fun s => pow_ne_zero 2 s.property.ne')
        have hn : ∀ s : BellmanPositiveTime, 0 ≤ ζ s.val / s.val ^ 2 :=
          fun s => div_nonneg ζ.nonneg (sq_nonneg _)
        have hself : ζ (2 : ℝ) = 1 := ζ.one_of_mem_closedBall (Metric.mem_closedBall_self
          (by norm_num : (0 : ℝ) ≤ 1 / 4))
        have hp : 0 < (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
          apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hc hn
            (x := ⟨2, by norm_num⟩)
          change ζ (2 : ℝ) / 2 ^ 2 ≠ 0
          rw [hself]
          norm_num
        exact ⟨ζ, ζ.contDiff, ζ.hasCompactSupport, hs, hp,
          bellmanRadialWeight_deriv_relation β 1 3 (by norm_num) (by norm_num) ζ ζ.contDiff hs⟩
      have hsζp : tsupport ζ ⊆ Ioi (0 : ℝ) :=
        fun s hs => lt_trans (by norm_num : (0 : ℝ) < 1) (hsζ hs).1
      have ht : ContDiff ℝ (⊤ : ℕ∞) (bellmanAngularTest ζ φ) := by
        apply contDiff_iff_contDiffAt.mpr
        intro q
        by_cases hq : 0 < q.1
        · have _h_xinl_0 : ContDiffAt ℝ (⊤ : ℕ∞) (bellmanSeparatedExpression ζ φ) q := by
            have hr : ContDiffAt ℝ (⊤ : ℕ∞) bellmanTestRadius q :=
              contDiffAt_fst.rpow_const_of_ne hq.ne'
            have hn : bellmanTestRadius q ≠ 0 :=
              (Real.rpow_pos_of_pos hq _).ne'
            exact (hζ.contDiffAt.comp q hr).mul (hφ.contDiffAt.comp q (contDiffAt_snd.div hr hn))
          exact ContDiffAt.congr_of_eventuallyEq
            _h_xinl_0
            (bellmanAngularTest_eventuallyEq_positive ζ φ q hq)
        · by_cases hn : q.1 = 0
          · have hz : (0 : ℝ) ∉ tsupport ζ := fun h => (lt_irrefl 0) (hsζp h)
            have he := notMem_tsupport_iff_eventuallyEq.mp hz
            have hr : ContinuousAt bellmanTestRadius q :=
              continuousAt_fst.rpow_const (Or.inr (by norm_num : 0 ≤ (3 : ℝ)⁻¹))
            have hr0 : bellmanTestRadius q = 0 := by simp [bellmanTestRadius, hn]
            have hec : ∀ᶠ z in 𝓝 q, ζ (bellmanTestRadius z) = 0 := by
              have ht : Tendsto bellmanTestRadius (𝓝 q) (𝓝 0) := hr0 ▸ hr
              exact ht.eventually he
            apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
            filter_upwards [hec] with z hz
            simp only [bellmanAngularTest, bellmanSeparatedExpression, hz, zero_mul, ite_self]
          · have hneg : q.1 < 0 := lt_of_le_of_ne (le_of_not_gt hq) hn
            have ho : IsOpen {q : ℝ × ℝ | q.1 < 0} := isOpen_lt continuous_fst continuous_const
            apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
            filter_upwards [ho.mem_nhds hneg] with z hz
            exact ite_eq_right (not_lt_of_gt hz)
      have hc := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).1
      have hs : tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} := by
        intro q hq he
        have hx := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).2 hq
        rw [he] at hx
        change (0 : ℝ) < 0 at hx
        exact lt_irrefl 0 hx
      have he := hp.2.2.2.2.2.1 (bellmanAngularTest ζ φ) ht hc hs
      let fx : ℝ × ℝ → ℝ :=
        fun q => q.2 * fderiv ℝ (bellmanAngularTest ζ φ) q (1, 0)
      let fv : ℝ × ℝ → ℝ :=
        fun q => fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1)) q (0, 1)
      have hts := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).2
      have hsx : tsupport fx ⊆ {q : ℝ × ℝ | 0 < q.1} :=
        tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hts)
      have hsv : tsupport fv ⊆ {q : ℝ × ℝ | 0 < q.1} :=
        (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
          ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hts)
      change (∫ q, fx q.val ∂μ) + (∫ q, fv q.val ∂η) = 0 at he
      rw [← bellman_integral_positive_restrict μ fx hsx,
        ← bellman_integral_positive_restrict η fv hsv, hrep.1, hrep.2] at he
      change (∫ q, q.val.2 * fderiv ℝ (bellmanAngularTest ζ φ) q.val (1, 0)
        ∂bellmanAngularRep β F) +
        (∫ q, fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
          q.val (0, 1) ∂bellmanAngularRep β H) = 0 at he
      have _h_xinl_1 : (∫ q, q.val.2 * fderiv ℝ (bellmanAngularTest ζ φ) q.val (1, 0)
          ∂bellmanAngularRep β F) =
          (1 / 3 : ℝ) * (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) *
            (∫ y, y * φ y ∂F) -
          (1 / 3 : ℝ) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
            (∫ y, y ^ 2 * deriv φ y ∂F) := by
          have hζd := (contDiff_infty_iff_deriv.mp hζ).2
          have hφd := (contDiff_infty_iff_deriv.mp hφ).2
          have hr1 : Integrable (fun s : BellmanPositiveTime => deriv ζ s.val / s.val)
              (bellmanRadialWeight β) := by
            simpa only [pow_one] using bellmanRadialTest_integrable β (deriv ζ)
              hζd.continuous hcζ.deriv (tsupport_deriv_subset.trans hsζp) 1
          have hr2 := bellmanRadialTest_integrable β ζ hζ.continuous hcζ hsζp 2
          have ha1 : Integrable (fun y => y * φ y) F := by
            simpa only [pow_one] using bellmanAngularTestFactor_integrable F φ
              hφ.continuous hcφ 1
          have ha2 := bellmanAngularTestFactor_integrable F (deriv φ) hφd.continuous hcφ.deriv 2
          rw [bellmanAngularRep,
            isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.integral_map]
          have hfun : (fun w : BellmanPositiveTime × ℝ => (bellmanAngularPoint w).val.2 *
              fderiv ℝ (bellmanAngularTest ζ φ) (bellmanAngularPoint w).val (1, 0)) =
              (fun w : BellmanPositiveTime × ℝ =>
                (1 / 3 : ℝ) * (deriv ζ w.1.val / w.1.val * (w.2 * φ w.2)) -
                (1 / 3 : ℝ) * (ζ w.1.val / w.1.val ^ 2 * (w.2 ^ 2 * deriv φ w.2))) := by
            funext w
            have _h_xinl_0 : (bellmanAngularPoint w).val.2 *
          fderiv ℝ (bellmanAngularTest ζ φ) (bellmanAngularPoint w).val (1, 0) =
          w.2 / (3 * w.1.val) * deriv ζ w.1.val * φ w.2 -
            w.2 ^ 2 / (3 * w.1.val ^ 2) * ζ w.1.val * deriv φ w.2 := by
                have he := bellmanAngularTest_eventuallyEq_positive ζ φ (bellmanAngularPoint w).val
                  (pow_pos w.1.property 3)
                rw [he.fderiv_eq]
                exact bellmanSeparatedExpression_transport ζ φ w
                  (hζ.differentiable (by simp) _) (hφ.differentiable (by simp) _)

              /- The second velocity derivative of the zero extension is exactly ζ(s)φ''(y)/s². -/
            rw [_h_xinl_0]
            ring
          rw [hfun, integral_sub ((hr1.mul_prod ha1).const_mul (1 / 3 : ℝ))
            ((hr2.mul_prod ha2).const_mul (1 / 3 : ℝ)), integral_const_mul, integral_const_mul,
            integral_prod_mul (fun s : BellmanPositiveTime => deriv ζ s.val / s.val)
              (fun y : ℝ => y * φ y),
            integral_prod_mul (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2)
              (fun y : ℝ => y ^ 2 * deriv φ y)]
          ring

        /- The second velocity integral factors with the same radial multiplier as the angular
        equation. -/
      have _h_xinl_0 : (∫ q, fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1)) q.val (0, 1) ∂bellmanAngularRep β H) = (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) * (∫ y, deriv (deriv φ) y ∂H) := by
        rw [bellmanAngularRep,
          isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.integral_map]
        have hfun : (fun w : BellmanPositiveTime × ℝ =>
            fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
              (bellmanAngularPoint w).val (0, 1)) =
            (fun w : BellmanPositiveTime × ℝ =>
              (ζ w.1.val / w.1.val ^ 2) * deriv (deriv φ) w.2) := by
          funext w
          have _h_xinl_0 : fderiv ℝ (fun q => fderiv ℝ (bellmanAngularTest ζ φ) q (0, 1))
            (bellmanAngularPoint w).val (0, 1) =
            ζ w.1.val * deriv (deriv φ) w.2 / w.1.val ^ 2 := by
            have he := bellmanAngularTest_eventuallyEq_positive ζ φ (bellmanAngularPoint w).val
              (pow_pos w.1.property 3)
            have hf : (fun q => fderiv ℝ (bellmanAngularTest ζ φ) q (0, 1)) =ᶠ[
                𝓝 (bellmanAngularPoint w).val]
                (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1)) := by
              filter_upwards [he.fderiv (𝕜 := ℝ)] with q hq
              exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hq
            rw [hf.fderiv_eq]
            have hφd := (contDiff_infty_iff_deriv.mp hφ).2
            have hs := bellmanSeparatedExpression_hasFDerivAt ζ (deriv φ) w
              (hζ.differentiable (by simp) _) (hφd.differentiable (by simp) _)
            have hn : bellmanTestRadius (bellmanAngularPoint w).val ≠ 0 := by
              rw [bellmanTestRadius_angularPoint]
              exact w.1.property.ne'
            have hi := (hasDerivAt_inv hn).comp_hasFDerivAt (bellmanAngularPoint w).val
              (bellmanTestRadius_hasFDerivAt w)
            have hd := hs.mul hi
            have he : (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1)) =ᶠ[
                𝓝 (bellmanAngularPoint w).val]
                (bellmanSeparatedExpression ζ (deriv φ) * (fun y => y⁻¹) ∘ bellmanTestRadius) := by
              have ho : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
              have hq : (bellmanAngularPoint w).val ∈ {q : ℝ × ℝ | 0 < q.1} :=
                pow_pos w.1.property 3
              filter_upwards [ho.mem_nhds hq] with q hqp
              have _h_xinl_0 : fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1) =
            bellmanSeparatedExpression ζ (deriv φ) q / bellmanTestRadius q := by
                have hζ := (hζ.differentiable (by simp))
                have hφ := (hφ.differentiable (by simp))
                let w := bellmanAngularHomeomorph.symm ⟨q, hqp⟩
                have he := bellmanAngularPoint_inverse q hqp
                rw [← he]
                rw [bellmanSeparatedExpression_velocity ζ φ w (hζ _) (hφ _)]
                rw [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
                  bellmanTestAngle_angularPoint]
              rw [_h_xinl_0]
              rfl
            rw [(hd.congr_of_eventuallyEq he).fderiv]
            simp only [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
              bellmanTestAngle_angularPoint, Function.comp_apply]
            change (ζ w.1.val * deriv φ w.2) *
                (-(w.1.val ^ 2)⁻¹ * (1 / (3 * w.1.val ^ 2) * 0)) +
              w.1.val⁻¹ * ((ζ w.1.val * deriv (deriv φ) w.2) *
                (w.1.val⁻¹ * 1 - w.2 / (3 * w.1.val ^ 3) * 0) +
                (deriv φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 0)) = _
            field_simp [w.1.property.ne']
            ring
          rw [_h_xinl_0]
          ring
        rw [hfun]
        exact integral_prod_mul (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2)
          (deriv (deriv φ))
      rw [_h_xinl_1,
        _h_xinl_0, hrel] at he
      have hzero : (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
          ((∫ y, deriv (deriv φ) y ∂H) - (1 / 3 : ℝ) * (∫ y, y ^ 2 * deriv φ y ∂F) +
            ((β - 2) / 3) * (∫ y, y * φ y ∂F)) = 0 := by
        linear_combination he
      exact (mul_eq_zero.mp hzero).resolve_left hK.ne'
    obtain ⟨f, h, J, hd⟩ : ∃ f h J : ℝ → ℝ,
        F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
        H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
        LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
        (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
        (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
        (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
        (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
        (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y) := by
      let : IsFiniteMeasureOnCompacts F := hang.1
      let : IsFiniteMeasureOnCompacts H := hang.2.2.1
      obtain ⟨j, hj⟩ : ∃ j : ℝ, ∀ φ : BellmanRealTest,
          (∫ x, deriv φ x ∂H) =
            (1 / 3 : ℝ) * (∫ x, x ^ 2 * φ x ∂F) -
              (∫ x, φ x * (j - ((β - 2) / 3) * bellmanMeasurePrimitive F id 0 x)) := by
        let : IsFiniteMeasureOnCompacts F := hang.1
        let : IsFiniteMeasureOnCompacts H := hang.2.2.1
        let A := bellmanMeasurePrimitive F id 0
        have hA : LocallyIntegrable A volume :=
          bellmanMeasurePrimitive_locallyIntegrable F id continuous_id
        have h1H : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) H :=
          continuous_const.locallyIntegrable
        have h2F : LocallyIntegrable (fun x : ℝ => x ^ 2) F :=
          (continuous_id.pow 2).locallyIntegrable
        let L : BellmanRealTest →ₗ[ℝ] ℝ :=
          (bellmanWeightedTestIntegral H (fun _ => 1)).comp bellmanTestDerivativeLinearMap -
            (1 / 3 : ℝ) • bellmanWeightedTestIntegral F (fun x => x ^ 2) -
            ((β - 2) / 3) • bellmanWeightedTestIntegral volume A
        have hL (φ : BellmanRealTest) : L φ = (∫ x, deriv φ x ∂H) -
            (1 / 3 : ℝ) * (∫ x, φ x * x ^ 2 ∂F) -
            ((β - 2) / 3) * (∫ x, φ x * A x) := by
          change bellmanWeightedTestIntegral H (fun _ => 1) (bellmanTestDerivative φ) -
            (1 / 3 : ℝ) * bellmanWeightedTestIntegral F (fun x => x ^ 2) φ -
            ((β - 2) / 3) * bellmanWeightedTestIntegral volume A φ = _
          rw [bellmanWeightedTestIntegral_apply H _ h1H,
            bellmanWeightedTestIntegral_apply F _ h2F,
            bellmanWeightedTestIntegral_apply volume A hA]
          simp only [bellmanTestDerivative, mul_one]
          rfl
        have hzero : ∀ φ : BellmanRealTest, L (bellmanTestDerivative φ) = 0 := by
          intro φ
          rw [hL]
          change (∫ x, deriv (deriv φ) x ∂H) -
            (1 / 3 : ℝ) * (∫ x, deriv φ x * x ^ 2 ∂F) -
            ((β - 2) / 3) * (∫ x, deriv φ x * A x) = 0
          have he := hang.2.2.2.2.2.2 φ φ.contDiff φ.hasCompactSupport
          have hw := bellmanMeasurePrimitive_weak F id continuous_id φ
            φ.contDiff φ.hasCompactSupport
          have hswap : (∫ x, deriv φ x * A x) = -∫ x, x * φ x ∂F := by
            rw [show (fun x => deriv φ x * A x) = (fun x => A x * deriv φ x) by
              funext x; ring]
            exact hw
          have hswap2 : (∫ x, deriv φ x * x ^ 2 ∂F) = ∫ x, x ^ 2 * deriv φ x ∂F := by
            apply integral_congr_ae
            exact ae_of_all _ fun x => mul_comm _ _
          rw [hswap, hswap2]
          linear_combination he
        obtain ⟨k, hk⟩ := bellman_test_derivative_kernel L hzero
        refine ⟨-k, ?_⟩
        intro φ
        have he := hk φ
        rw [hL] at he
        have hiA : Integrable (fun x => φ x * A x) volume := by
          simpa only [smul_eq_mul] using
            hA.integrable_smul_left_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
        have hiφ : Integrable (fun x => φ x) volume :=
          φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
        have hJI : (∫ x, φ x * (-k - ((β - 2) / 3) * A x)) =
            -k * (∫ x, φ x) - ((β - 2) / 3) * (∫ x, φ x * A x) := by
          rw [show (fun x => φ x * (-k - ((β - 2) / 3) * A x)) =
              (fun x => -k * φ x - ((β - 2) / 3) * (φ x * A x)) by funext x; ring,
            integral_sub (hiφ.const_mul (-k)) (hiA.const_mul _),
            integral_const_mul, integral_const_mul]
        change (∫ x, deriv φ x ∂H) =
          (1 / 3 : ℝ) * (∫ x, x ^ 2 * φ x ∂F) -
            (∫ x, φ x * (-k - ((β - 2) / 3) * A x))
        rw [hJI, show (fun x => x ^ 2 * φ x) = (fun x => φ x * x ^ 2) by funext x; ring]
        linarith
      let A := bellmanMeasurePrimitive F id 0
      let J := fun x => j - ((β - 2) / 3) * A x
      have hA :=
        bellmanMeasurePrimitive_locallyIntegrable F id continuous_id
      have hJ : LocallyIntegrable J volume := by
        convert! (continuous_const : Continuous (fun _ : ℝ => j)).locallyIntegrable.sub
          (hA.smul ((β - 2) / 3)) using 1
      obtain ⟨c, hH, hnH⟩ := bellman_measure_density_of_flux F H (fun x => x ^ 2) J
        (continuous_id.pow 2) hJ (1 / 3) hj
      let h := fun x => c + (∫ z in 0..x, J z) -
        (1 / 3 : ℝ) * bellmanMeasurePrimitive F (fun z => z ^ 2) 0 x
      have hFH : F ≤ H := by simpa only [ENNReal.ofReal_one, one_smul] using hang.2.2.2.2.1
      have hFvol : F ≪ volume := hFH.absolutelyContinuous.trans (by
        rw [hH]; exact withDensity_absolutelyContinuous _ _)
      let f := fun x => (F.rnDeriv volume x).toReal
      have hfm : Measurable f := (Measure.measurable_rnDeriv F volume).ennreal_toReal
      have hf := bellman_rnDeriv_locallyIntegrable F volume
      have hfn : ∀ᵐ x ∂volume, 0 ≤ f x := ae_of_all _ fun _ => ENNReal.toReal_nonneg
      have hF : F = volume.withDensity (fun x => ENNReal.ofReal ((F.rnDeriv volume x).toReal)) := by
          calc
            F = volume.withDensity (F.rnDeriv volume) :=
              (Measure.withDensity_rnDeriv_eq F volume hFvol).symm
            _ = _ := by
              apply withDensity_congr_ae
              filter_upwards [Measure.rnDeriv_lt_top F volume] with x hx
              exact (ENNReal.ofReal_toReal hx.ne).symm

        /- A weighted measure primitive becomes a literal moment of its Radon–Nikodym density. -/
      have hJeq : J = fun y => j - ((β - 2) / 3) * (∫ z in 0..y, z * f z) := by
        funext y
        dsimp [J, A]
        rw [bellmanMeasurePrimitive_eq_rnMoment F hFvol]
        rfl
      have hheq : h = fun y => c + (∫ z in 0..y, J z) -
          (1 / 3 : ℝ) * (∫ z in 0..y, z ^ 2 * f z) := by
        funext y
        dsimp [h]
        rw [bellmanMeasurePrimitive_eq_rnMoment F hFvol]
      have hhac : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b := by
        intro a b hab
        rw [hheq]
        have _h_xinl_0 : AbsolutelyContinuousOnInterval (fun x => ∫ z in 0..x, z ^ 2 * f z) a b := by
            exact (
          bellman_lebesguePrimitive_locallyAC _ (bellman_polynomial_locallyIntegrable f hf 2) a b hab
          )
        convert! ((bellman_const_locallyAC c a b).add
          (bellman_lebesguePrimitive_locallyAC J hJ a b hab)).sub
          (_h_xinl_0.const_mul (1 / 3)) using 1
      have hJac : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b := by
        intro a b hab
        rw [hJeq]
        have hi : LocallyIntegrable (fun x => x * f x) volume := by
          simpa only [pow_one] using bellman_polynomial_locallyIntegrable f hf 1
        convert! (bellman_const_locallyAC j a b).sub
          ((bellman_lebesguePrimitive_locallyAC _ hi a b hab).const_mul ((β - 2) / 3)) using 1
      have hhm : Measurable h := (bellman_locallyAC_continuous hhac).measurable
      have hhn := hnH
      have hfH :=
        bellman_density_le_of_measure_le f h hfm hfn hhn (by rw [← hF, ← hH]; exact hFH)
      have hRf : ∀ᵐ x ∂volume, 0 ≤ R * f x := by
        filter_upwards [hfn] with x hx
        exact mul_nonneg (by linarith) hx
      have hHR : ∀ᵐ x ∂volume, h x ≤ R * f x := by
        apply bellman_density_le_of_measure_le h (fun x => R * f x) hhm hhn hRf
        have he : volume.withDensity (fun x => ENNReal.ofReal (R * f x)) =
            ENNReal.ofReal R • F := by
          rw [show (fun x => ENNReal.ofReal (R * f x)) =
            ENNReal.ofReal R • (fun x => ENNReal.ofReal (f x)) by
              funext x; exact ENNReal.ofReal_mul (by linarith),
            withDensity_smul _ hfm.ennreal_ofReal, ← hF]
        rw [← hH, he]
        exact hang.2.2.2.2.2.1
      refine ⟨f, h, J, hF, hH, hf, hfn, hhac, hJac, ?_, ?_, ?_⟩
      · filter_upwards [hfH, hHR] with x hx hy
        exact ⟨hx, hy⟩
      · rw [hheq]
        have hi := bellman_polynomial_locallyIntegrable f hf 2
        filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hJ,
          _root_.LocallyIntegrable.ae_hasDerivAt_integral hi] with x hx hix
        have hd := ((hasDerivAt_const x c).add (hx 0)).sub ((hix 0).const_mul (1 / 3))
        convert hd.deriv using 1; ring
      · rw [hJeq]
        filter_upwards [bellman_momentFlux_deriv f hf j ((β - 2) / 3)] with x hx
        rw [hx]
        ring
    let : IsFiniteMeasureOnCompacts μ := hp.1.1
    let : IsFiniteMeasureOnCompacts F := hang.1
    exact ⟨F, H, f, h, J, hrep, hd,
      bellmanAngularDensity_tail β μ F hrep.1 f hd.1 hd.2.2.1 hd.2.2.2.1⟩
  have he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y * bellmanAngularFirstMoment f y +
      ((β - 3) / 3) * bellmanAngularSecondMoment f y := by
    have hf := hd.2.2.1
    have hh := hd.2.2.2.2.1
    have hJ := hd.2.2.2.2.2.1
    have hdh := hd.2.2.2.2.2.2.2.1
    have hdJ := hd.2.2.2.2.2.2.2.2
    intro y
    have hJa := bellman_locallyAC_oriented hJ 0 y
    have hha := bellman_locallyAC_oriented hh 0 y
    have hid : AbsolutelyContinuousOnInterval (fun z : ℝ => z) 0 y :=
      (contDiff_id : ContDiff ℝ 1 (fun z : ℝ => z)).contDiffOn.absolutelyContinuousOnInterval
    have hip := hJa.integral_mul_deriv_eq_deriv_mul hid
    simp only [deriv_id'', mul_one, mul_zero, sub_zero] at hip
    have hm : (∫ z in 0..y, deriv J z * z) =
        -((β - 2) / 3) * bellmanAngularSecondMoment f y := by
      calc
        _ = ∫ z in 0..y, -((β - 2) / 3) * (z ^ 2 * f z) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hdJ] with z hz
          intro _
          rw [hz]
          ring
        _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
    have _h_inl_13 : J y = J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y := by
        have he := (bellman_locallyAC_oriented hJ 0 y).integral_deriv_eq_sub
        have hc : (∫ z in 0..y, deriv J z) =
            -((β - 2) / 3) * bellmanAngularFirstMoment f y := by
          calc
            _ = ∫ z in 0..y, -((β - 2) / 3) * (z * f z) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards [hdJ] with z hz
              intro _
              rw [hz]
              ring
            _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
        rw [hc] at he
        linarith

      /- Two source interval integrations yield the exact angular identity. -/
    rw [hm, _h_inl_13] at hip
    have hjInt : IntervalIntegrable J volume 0 y := hJa.continuousOn.intervalIntegrable
    have hmInt := bellmanAngularMoment_intervalIntegrable hf 0 y 2
    have hhe := hha.integral_deriv_eq_sub
    have hhInt : (∫ z in 0..y, deriv h z) =
        (∫ z in 0..y, J z) - bellmanAngularSecondMoment f y / 3 := by
      calc
        _ = ∫ z in 0..y, J z - (z ^ 2 * f z) / 3 := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hdh] with z hz
          intro _
          exact hz
        _ = _ := by
          rw [intervalIntegral.integral_sub hjInt (hmInt.div_const 3),
            intervalIntegral.integral_div]
          rfl
    rw [hhInt, hip] at hhe
    linear_combination -hhe
  obtain ⟨hF, hH⟩ : F = 0 ∧ H = 0 := by
      obtain ⟨h0, hj0, hpos, _⟩ : h 0 = 0 ∧ J 0 = 0 ∧ (∀ᵐ y ∂volume.restrict (Ioi 0), f y = 0) ∧
      (∀ y : ℝ, 0 < y → h y = 0) := by
        have htail := ht
        have hf := hd.2.2.1
        have hn := hd.2.2.2.1
        have hac := hd.2.2.2.2.1
        have hfh := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1)
        have hcomp := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)
        have hh := bellmanAngularDensity_nonneg hac hn hfh
        obtain ⟨L, _, hI, _, hj, hlower⟩ : ∃ L : ℝ, 0 ≤ L ∧ Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 L) ∧
            Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) ∧
            J 0 = ((β - 2) / 3) * L ∧ ∀ y : ℝ, 0 < y → h 0 ≤ h y := by
          have hh := bellmanAngularDensity_nonneg hd.2.2.2.2.1 hd.2.2.2.1
            (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1))
          exact bellmanAngularPositiveTail_limit R β hR hβ f h J hd.2.2.1 hd.2.2.2.1 hh
            (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)) he htail
        have h0 : h 0 = 0 := by
          have hh := (hh 0)
          by_contra hn
          have hp : 0 < h 0 := lt_of_le_of_ne hh (Ne.symm hn)
          have hRp : 0 < R := by linarith
          apply bellmanAngularTail_not_power_lower_bound f β 2 (h 0 / R) (β - 4)
            htail le_rfl (div_pos hp hRp) (by linarith)
          filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcomp] with y hy hc
          have h0y := hlower y (by have : 2 < y := hy; linarith)
          have hf : h 0 / R ≤ f y := (div_le_iff₀ hRp).mpr (by simpa only [mul_comm] using h0y.trans hc)
          exact mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg (by have : 2 < y := hy; linarith) _)
        have hj0 : J 0 = 0 := by
          have hI := bellmanAngularFirstMoment_tendsto_zero f hf
          have hM : Tendsto (fun y => bellmanAngularSecondMoment f y / y) (𝓝 (0 : ℝ)) (𝓝 0) := by
              apply squeeze_zero_norm
                (fun y => bellmanAngularSecondMoment_div_norm_le hf hn y)
                (bellmanAngularFirstMoment_tendsto_zero f hf)

            /- Nonnegativity on both sides and the integrated identity force the flux at zero to vanish. -/
          have ht : Tendsto (fun y => J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y +
              ((β - 3) / 3) * (bellmanAngularSecondMoment f y / y)) (𝓝 (0 : ℝ)) (𝓝 (J 0)) := by
            simpa only [mul_zero, sub_zero, add_zero] using
              (tendsto_const_nhds.sub (hI.const_mul ((β - 2) / 3))).add
                (hM.const_mul ((β - 3) / 3))
          have heq (y : ℝ) (hy : y ≠ 0) : h y / y =
              J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y +
                ((β - 3) / 3) * (bellmanAngularSecondMoment f y / y) := by
            rw [he y, h0]
            field_simp
            ring
          have hp : 0 ≤ J 0 := by
            apply ge_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
            filter_upwards [self_mem_nhdsWithin] with y hy
            rw [← heq y hy.ne']
            exact div_nonneg (hh y) hy.le
          have hm : J 0 ≤ 0 := by
            apply le_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ))))
            filter_upwards [self_mem_nhdsWithin] with y hy
            rw [← heq y hy.ne]
            exact div_nonpos_of_nonneg_of_nonpos (hh y) hy.le
          exact le_antisymm hm hp
        have hL0 : L = 0 := by
          have hc : 0 < (β - 2) / 3 := by linarith
          rw [hj0] at hj
          nlinarith
        have hi := bellmanAngularFirstMoment_integrable β f h J hβ hf hn hh he
        have htotal : (∫ z in Ioi 0, z * f z) = 0 := by
          have heq := tendsto_nhds_unique hI (bellmanAngularFirstMoment_tendsto f hi)
          linarith
        have hzn : ∀ᵐ z ∂volume.restrict (Ioi 0), 0 ≤ z * f z := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hnz
          exact mul_nonneg hz.le hnz
        have hz := (integral_eq_zero_iff_of_nonneg_ae hzn hi).mp htotal
        have hfzero : ∀ᵐ z ∂volume.restrict (Ioi 0), f z = 0 := by
          filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with z hz hpos
          exact (mul_eq_zero.mp hz).resolve_left hpos.ne'
        have hhzero : h =ᵐ[volume.restrict (Ioi 0)] (fun _ => 0) := by
          filter_upwards [hfzero, ae_restrict_of_ae hcomp] with z hz hc
          rw [hz, mul_zero] at hc
          exact le_antisymm hc (hh z)
        have heq := Measure.eqOn_open_of_ae_eq hhzero isOpen_Ioi
          (bellman_locallyAC_continuous hac).continuousOn continuous_const.continuousOn
        exact ⟨h0, hj0, hfzero, fun y hy => heq hy⟩
      have hf := hd.2.2.1
      have hn := hd.2.2.2.1
      have hcomp := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)
      have hIneg : ∀ a : ℝ, a < 0 → bellmanAngularFirstMoment f a = 0 := by
          intro a ha
          have hnI := bellmanAngularFirstMoment_nonneg_negative hn ha.le
          by_contra hne
          have hIp : 0 < bellmanAngularFirstMoment f a := lt_of_le_of_ne hnI (Ne.symm hne)
          have hRp : 0 < R := by linarith
          let b := max 2 (-a)
          have hb : 2 ≤ b := le_max_left _ _
          have hc : 0 < bellmanAngularFirstMoment f a / (3 * R) := div_pos hIp (by positivity)
          apply bellmanAngularTail_not_power_lower_bound (fun y => f (-y)) β b
            (bellmanAngularFirstMoment f a / (3 * R)) (β - 3)
            (bellmanAngularTail_reflect β f ht) hb hc (by linarith)
          have href : ∀ᵐ y ∂volume, h (-y) ≤ R * f (-y) := by
              exact (
            (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hcomp
            )
          filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae href] with y hy hcy
          have hyp : 0 < y := by have : 2 < y := hb.trans_lt hy; linarith
          have hya : -y ≤ a := by have := (le_max_right 2 (-a)).trans hy.le; linarith
          have hm : bellmanAngularFirstMoment f a ≤ bellmanAngularFirstMoment f (-y) := by
            let y := (-y)
            have ha := ha.le
            have hi (u v : ℝ) : IntervalIntegrable (fun z => z * f z) volume u v := by
              simpa only [pow_one] using bellmanAngularMoment_intervalIntegrable hf u v 1
            have he := intervalIntegral.integral_add_adjacent_intervals (hi y a) (hi a 0)
            have hnon : (∫ z in y..a, z * f z) ≤ 0 := by
              rw [intervalIntegral.integral_of_le hya]
              apply integral_nonpos_of_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hn] with z hz hfz
              exact mul_nonpos_of_nonpos_of_nonneg (hz.2.trans ha) hfz
            rw [bellmanAngularFirstMoment, bellmanAngularFirstMoment,
              intervalIntegral.integral_symm (a := a) (b := 0),
              intervalIntegral.integral_symm (a := y) (b := 0)]
            linarith
          have hl := bellmanAngularDensity_negative_lower β f h J hβ hf hn h0 hj0 he (-y)
            (by linarith)
          have hfy : (bellmanAngularFirstMoment f a / (3 * R)) * y ≤ f (-y) := by
            have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ y / 3)
            simp only [neg_neg] at hl
            have hl' : (y / 3) * bellmanAngularFirstMoment f a ≤ h (-y) := by
              simpa only [neg_neg] using hm'.trans hl
            apply le_of_mul_le_mul_left (a := R) _ hRp
            have heq : R * ((bellmanAngularFirstMoment f a / (3 * R)) * y) =
                (y / 3) * bellmanAngularFirstMoment f a := by field_simp
            rw [heq]
            exact hl'.trans hcy
          have hm := mul_le_mul_of_nonneg_right hfy (Real.rpow_nonneg hyp.le (β - 4))
          have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
            calc
              y * y ^ (β - 4) = y ^ (1 : ℝ) * y ^ (β - 4) := by rw [Real.rpow_one]
              _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
              _ = y ^ (β - 3) := by congr 1; ring
          calc
            (bellmanAngularFirstMoment f a / (3 * R)) * y ^ (β - 3) =
                ((bellmanAngularFirstMoment f a / (3 * R)) * y) * y ^ (β - 4) := by
              rw [mul_assoc, hp]
            _ ≤ _ := hm

        /- A vanishing first moment on the negative half-line forces its density to vanish there. -/
      have hneg : ∀ᵐ y ∂volume.restrict (Iio 0), f y = 0 := by
        have hi : LocallyIntegrable (fun z => z * f z) volume := by
          simpa only [pow_one] using bellman_polynomial_locallyIntegrable f hf 1
        have hd := _root_.LocallyIntegrable.ae_hasDerivAt_integral hi
        filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Iio] with y hdy hy
        have he : bellmanAngularFirstMoment f =ᶠ[𝓝 y] (fun _ => 0) := by
          filter_upwards [isOpen_Iio.mem_nhds hy] with z hz'
          exact hIneg z hz'
        have heder := he.deriv_eq
        rw [deriv_const] at heder
        have hder : deriv (bellmanAngularFirstMoment f) y = y * f y := (hdy 0).deriv
        rw [hder] at heder
        exact (mul_eq_zero.mp heder).resolve_left hy.ne
      have hfn : ∀ᵐ y ∂volume, f y = 0 := by
        have hp := (ae_restrict_iff' measurableSet_Ioi).mp hpos
        have hm := (ae_restrict_iff' measurableSet_Iio).mp hneg
        have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := Measure.ae_ne volume 0
        filter_upwards [hp, hm, hne] with y hypos hyneg hyne
        rcases lt_or_gt_of_ne hyne with hy | hy
        · exact hyneg hy
        · exact hypos hy
      have hh := bellmanAngularDensity_nonneg hd.2.2.2.2.1 hn
        (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1))
      have hhn : ∀ᵐ y ∂volume, h y = 0 := by
        filter_upwards [hfn, hcomp] with y hy hc
        rw [hy, mul_zero] at hc
        exact le_antisymm hc (hh y)
      constructor
      · rw [hd.1]
        calc
          _ = volume.withDensity (fun _ => (0 : ENNReal)) := by
            apply withDensity_congr_ae
            filter_upwards [hfn] with y hy
            rw [hy, ENNReal.ofReal_zero]
          _ = 0 := withDensity_zero
      · rw [hd.2.1]
        calc
          _ = volume.withDensity (fun _ => (0 : ENNReal)) := by
            apply withDensity_congr_ae
            filter_upwards [hhn] with y hy
            rw [hy, ENNReal.ofReal_zero]
          _ = 0 := withDensity_zero

    /- A homogeneous stationary pair of degree at least three has no mass on positive position. -/
  have hμ : μ.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.1, hF, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  have hη : η.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.2, hH, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  constructor
  · simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hμ
  · simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hη

end HypoellipticAleksandrov.KineticAleksandrov
