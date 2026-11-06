module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalGradientBound
public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.Coefficients.Ellipticity
import HypoellipticAleksandrov.Measure.TimeVelocity
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCoercivity
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalEnergyRow
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialIntegrability
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSlices
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSpacetime
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeBound
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeEnergy
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalValueEnergy
import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

/-! # Uniform gradient energy on smaller collars

A compact interior plateau removes the cutoff weight on the smaller carrier. The resulting
constant is fixed before choosing the classical solution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Topology
open scoped Matrix.Norms.Elementwise

/- Every compactly contained carrier has a uniform gradient bound from outer value energy. -/
theorem exists_local_gradient_collar_constant {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (hUc : IsCompact (closure (Ioo a T ×ˢ O)))
    (V ) (hVm : MeasurableSet V)
    (hVc : IsCompact (closure V)) (hVU : closure V ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ z ∈ Ioo a T ×ˢ O, lam • (1 : PDE.Mat d) ≤ coefficientAt A z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TimeVelocity d → ℝ,
      IsScalarC12On u (Ioo a T ×ˢ O) →
      IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ O) →
      (∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) →
      (∫ z in V, ∑ j, scalarSpatialGradient u z j ^ 2) ≤
        C * ∫ z in Ioo a T ×ˢ O, u z ^ 2 := by
  classical
  let U := Ioo a T ×ˢ O
  have hU : IsOpen U := isOpen_Ioo.prod hO
  obtain ⟨ρ, hρ, hρone, hρsub⟩ := exists_smooth_cutoff_tsupport_subset hVc hU hVU
  have hc : HasCompactSupport ρ :=
    hasCompactSupport_of_tsupport_subset_of_isCompact_closure hρsub hUc
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TimeVelocity d → ℝ,
      IsScalarC12On u (Ioo a T ×ˢ O) →
      IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ O) →
      (∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) →
      (lam / 2) * (∫ z in Ioo a T ×ˢ O,
        ρ z ^ 2 * ∑ j, scalarSpatialGradient u z j ^ 2) ≤
        C * ∫ z in Ioo a T ×ˢ O, u z ^ 2 := by
    obtain ⟨K, hK, hrow⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ z j, |localValueEnergyErrorRow A ρ z j| ≤ K := by
      have hcont := continuous_localValueEnergyErrorRow A hA ρ hρ
      have _h_xinl_0 : HasCompactSupport (localValueEnergyErrorRow A ρ) := by
        apply HasCompactSupport.of_support_subset_isCompact hc
        intro z hz
        by_contra hnot
        apply hz
        ext j
        have hzero := image_eq_zero_of_notMem_tsupport hnot
        simp only [localValueEnergyErrorRow, scalarSpatialGradient_eq_zero_of_notMem_tsupport
          ρ z _ hnot, hzero, mul_zero, zero_mul, add_zero, Finset.sum_const_zero, Pi.zero_apply]
      obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
        _h_xinl_0
      refine ⟨max C 0, le_max_right _ _, fun z j => ?_⟩
      calc
        _ = ‖localValueEnergyErrorRow A ρ z j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖localValueEnergyErrorRow A ρ z‖ := norm_le_pi_norm _ j
        _ ≤ C := hC z
        _ ≤ max C 0 := le_max_left _ _
    obtain ⟨Kt, hKt, ht⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ z, |timeDerivative (fun y => ρ y ^ 2) z| ≤ K := by
        have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ z ^ 2) := hρ.pow 2
        have hsc : HasCompactSupport (fun z => ρ z ^ 2) := by
          rw [show (fun z => ρ z ^ 2) = ρ * ρ by funext z; exact pow_two _]
          exact HasCompactSupport.mul_left hc
        have hdc : Continuous (timeDerivative (fun z => ρ z ^ 2)) :=
          (hs.continuous_fderiv (by simp)).clm_apply continuous_const
        have hds : HasCompactSupport (timeDerivative (fun z => ρ z ^ 2)) :=
          hsc.fderiv_apply (𝕜 := ℝ) (1, 0)
        obtain ⟨K, hK⟩ := hdc.bounded_above_of_compact_support hds
        exact ⟨max K 0, le_max_right _ _, fun z =>
          (Real.norm_eq_abs _).symm.le.trans ((hK z).trans (le_max_left _ _))⟩

      /- One cutoff-dependent constant bounds every homogeneous solution's gradient energy. -/
    refine ⟨Kt / 2 + (d : ℝ) * K ^ 2 / (2 * lam), by positivity, ?_⟩
    intro u hu hq heq
    exact integral_local_gradient_energy_le a T O hO u ρ hu hρ hc hρsub A hA
      lam K Kt hlam hK hell (fun z _ j => hrow z j) (fun z _ => ht z) hq heq
  refine ⟨2 * C / lam, by positivity, ?_⟩
  intro u hu hq heq
  let f (z : TimeVelocity d) := ∑ j, scalarSpatialGradient u z j ^ 2
  have hcont : ContinuousOn f U := by
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp_continuousOn
      hu.continuousOn_scalarSpatialGradient).pow 2
  have hfi : IntegrableOn (fun z => ρ z ^ 2 * f z) U := by
    apply ((integrable_local_cutoff_square_mul hU f ρ hcont
      hρ.continuous hc hρsub).restrict (s := U)).congr
    exact Eventually.of_forall (fun z => mul_comm _ _)
  have hmono := setIntegral_mono_set hfi
    (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg (ρ z))
      (Finset.sum_nonneg (fun j _ => sq_nonneg _))))
    (Eventually.of_forall (fun z hz => hVU (subset_closure hz)))
  have hsame : (∫ z in V, ρ z ^ 2 * f z) = ∫ z in V, f z := by
    apply setIntegral_congr_fun hVm
    intro z hz
    obtain ⟨W, hW, hVW, hρW⟩ := eventually_nhdsSet_iff_exists.mp hρone
    change ρ z ^ 2 * f z = f z
    rw [hρW z (hVW (subset_closure hz)), one_pow, one_mul]
  rw [hsame] at hmono
  have hb := hbound u hu hq heq
  have hmul := mul_le_mul_of_nonneg_left hmono (show 0 ≤ lam / 2 by positivity)
  dsimp only [f] at hmul
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlam).mpr
  nlinarith only [hmul, hb]

end HypoellipticAleksandrov.Parabolic.LocalHolder
