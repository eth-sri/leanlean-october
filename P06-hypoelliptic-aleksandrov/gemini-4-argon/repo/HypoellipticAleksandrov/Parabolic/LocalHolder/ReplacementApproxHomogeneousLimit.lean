module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxLimitRegularity
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxClassicalEquation
import HypoellipticAleksandrov.Coefficients.Ellipticity
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakLimit
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakTestingTools
import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex
import Mathlib.Tactic.Ring

/-! # Classical homogeneous limits of controlled approximation families

The common derivative subsequence simultaneously supplies classical regularity and
preserves the homogeneous equation. No regularity theorem is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology
open scoped BigOperators Matrix.Norms.Elementwise

/- Controlled higher families and strong root convergence give the actual classical equation. -/
theorem scalarC12_homogeneous_of_strongL2_limit {d }
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (M ) (hAb : ∀ z ∈ U, ∀ i j, |A z.1 z.2 i j| ≤ M)
    (u : ℕ → TimeVelocity d → ℝ)
    (D : ∀ n, ParabolicWeakDerivativeFamily d (2 * (d + 4)) U (u n))
    (hu : ∀ n, ParabolicMemLpOn U 2 (u n))
    (v : TimeVelocity d → ℝ) (hv : ParabolicMemLpOn U 2 v)
    (hvcont : ContinuousOn v U)
    (hstrong : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)))
    (C ) (hC : 0 ≤ C) (hb : ∀ n, (D n).squaredL2Norm ≤ C ^ 2)
    (hzero : ∀ n, homogeneousWeakFamilyResidual (by omega : 2 ≤ 2 * (d + 4)) A (D n)
      =ᵐ[timeVelocityVolumeOn U] 0) :
    IsScalarC12On v U ∧ ∀ z ∈ U, scalarTimeDerivative v z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian v z) = 0 := by
  obtain ⟨E, σ, hσ, htest⟩ := exists_weakDerivativeFamily_testing_limit_of_tendsto_toLp
    U u D hu v hv hstrong C hC hb
  have hv12 := scalarC12On_of_continuousOn_higher_weak_family hU hvcont E
  have hEq : homogeneousWeakFamilyResidual (by omega : 2 ≤ 2 * (d + 4)) A E =ᵐ[timeVelocityVolumeOn U] 0 := by
    let hL := (by omega : 2 ≤ 2 * (d + 4))
    let u := (fun n => u (σ n))
    let D := (fun n => D (σ n))
    have hzero := (fun n => hzero (σ n))
    classical
    have hRm : ParabolicMemLpOn U 2 (homogeneousWeakFamilyResidual hL A E) := by
      apply (E.memLp _).add
      apply memLp_finsetSum
      intro i _
      apply memLp_finsetSum
      intro j _
      have ha :=
        (continuous_apply j).comp ((continuous_apply i).comp hA.continuous)
      exact memLp_two_mul_of_bound hU.measurableSet _ _ ha (E.memLp _) M
        (fun z hz => hAb z hz i j)
    apply ae_eq_zero_of_weak_pairings hU _ hRm
    intro φ hφ hc hs
    have ht := htest (ParabolicDerivativeIndex.castLE hL
      (ParabolicDerivativeIndex.timeOne d)) φ hφ hc hs
    have hij (i j : Fin d) := by
      have ha :=
        (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
      exact htest (ParabolicDerivativeIndex.castLE hL
        (ParabolicDerivativeIndex.velocityTwo j i))
        (fun z => A z.1 z.2 i j * φ z) (ha.mul hφ)
        (HasCompactSupport.mul_left hc) (tsupport_mul_subset_right.trans hs)
    have hsum := ht.add (tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hij i j)))
    have hn (n : ℕ) : (∫ z in U, homogeneousWeakFamilyResidual hL A (D n) z * φ z) = 0 := by
      have hz := hzero n
      rw [timeVelocityVolumeOn] at hz
      calc
        _ = ∫ z in U, (0 : ℝ) := integral_congr_ae (hz.mono fun z hz => by rw [hz]; simp)
        _ = 0 := integral_zero _ _
    have hvpair := integral_homogeneousWeakFamilyResidual_mul hL A hA E φ hφ hc
    have hseq : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop
        (𝓝 (∫ z in U, homogeneousWeakFamilyResidual hL A E z * φ z)) := by
      rw [hvpair]
      apply hsum.congr'
      exact Eventually.of_forall (fun n =>
        (integral_homogeneousWeakFamilyResidual_mul hL A hA (D n) φ hφ hc).symm.trans (hn n))
    exact tendsto_nhds_unique hseq tendsto_const_nhds
  exact ⟨hv12, classical_homogeneous_equation_of_weak_family hU
    (by omega : 2 ≤ 2 * (d + 4)) v hv12 A hA E hEq⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
