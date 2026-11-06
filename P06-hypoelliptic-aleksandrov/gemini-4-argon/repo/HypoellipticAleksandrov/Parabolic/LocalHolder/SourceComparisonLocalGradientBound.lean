module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalValueEnergy
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeBound
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCoercivity
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalEnergyRow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeEnergy
import HypoellipticAleksandrov.Coefficients.Ellipticity
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSpacetime
import HypoellipticAleksandrov.Measure.TimeVelocity
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialIntegrability
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSlices
import Mathlib.MeasureTheory.Integral.Prod

/-! # A local gradient bound from solution values

The bound combines actual quadratic testing, ellipticity, and the complete coefficient
error row. Its constants do not involve derivatives of the solution or its boundary data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

/- Localized gradient energy is bounded by value energy for a homogeneous classical solution. -/
theorem integral_local_gradient_energy_le {d : ℕ}
    (a T : ℝ) (O ) (hO : IsOpen O)
    (u ρ : TimeVelocity d → ℝ) (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam K Kt ) (hlam : 0 < lam) (hK : 0 ≤ K)
    (hell : ∀ z ∈ Ioo a T ×ˢ O, lam • (1 : PDE.Mat d) ≤ coefficientAt A z)
    (hrow : ∀ z ∈ Ioo a T ×ˢ O, ∀ j, |localValueEnergyErrorRow A ρ z j| ≤ K)
    (ht : ∀ z ∈ Ioo a T ×ˢ O, |timeDerivative (fun y => ρ y ^ 2) z| ≤ Kt)
    (hq : IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ O))
    (heq : ∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) :
    (lam / 2) * (∫ z in Ioo a T ×ˢ O,
      ρ z ^ 2 * ∑ j, scalarSpatialGradient u z j ^ 2) ≤
      (Kt / 2 + (d : ℝ) * K ^ 2 / (2 * lam)) *
        ∫ z in Ioo a T ×ˢ O, u z ^ 2 := by
  classical
  let U := Ioo a T ×ˢ O
  have hU : IsOpen U := isOpen_Ioo.prod hO
  let G (z : TimeVelocity d) := scalarSpatialGradient u z
  let P (z : TimeVelocity d) := ∑ i, ∑ j, A z.1 z.2 i j * G z j * G z i
  let B (z : TimeVelocity d) := localValueEnergyErrorRow A ρ z
  let E (z : TimeVelocity d) := ρ z ^ 2 * P z +
    u z * ρ z * ∑ j, B z j * G z j
  have hG (j : Fin d) : ContinuousOn (fun z => G z j) U :=
    (continuous_apply j).comp_continuousOn hu.continuousOn_scalarSpatialGradient
  have hP : ContinuousOn P U := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have hcoeff :=
      (continuous_apply j).comp ((continuous_apply i).comp hA.continuous)
    exact (hcoeff.continuousOn.mul (hG j)).mul (hG i)
  have hB : Continuous B := continuous_localValueEnergyErrorRow A hA ρ hρ
  have hBG : ContinuousOn (fun z => ∑ j, B z j * G z j) U := by
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp hB).continuousOn.mul (hG j)
  have hEi : IntegrableOn E U := by
    have hcont : ContinuousOn (fun z => ρ z * P z + u z * ∑ j, B z j * G z j) U :=
      (hρ.continuous.continuousOn.mul hP).add (hu.continuousOn.mul hBG)
    have hi := (integrable_local_cutoff_mul hU
      (fun z => ρ z * P z + u z * ∑ j, B z j * G z j) ρ
      hcont hρ.continuous hc hsub).restrict (s := U)
    apply hi.congr
    exact Eventually.of_forall (fun z => by dsimp [E]; ring)
  have hgrad : IntegrableOn (fun z => ρ z ^ 2 * ∑ j, G z j ^ 2) U := by
    have hcont : ContinuousOn (fun z => ∑ j, G z j ^ 2) U := by
      apply continuousOn_finsetSum
      intro j _
      exact (hG j).pow 2
    have hi := (integrable_local_cutoff_square_mul hU
      (fun z => ∑ j, G z j ^ 2) ρ hcont hρ.continuous hc hsub).restrict (s := U)
    apply hi.congr
    exact Eventually.of_forall (fun z => mul_comm _ _)
  let c := (d : ℝ) * K ^ 2 / (2 * lam)
  have hcpoint : ∀ᵐ z ∂volume.restrict U,
      (lam / 2) * (ρ z ^ 2 * ∑ j, G z j ^ 2) ≤ E z + c * u z ^ 2 := by
    apply ae_restrict_of_forall_mem hU.measurableSet
    intro z hz
    have hp := local_value_energy_flux_coercivity lam (ρ z) (u z) K hlam hK
      (coefficientAt A z) (G z) (B z) (hell z hz) (hrow z hz)
    convert hp using 1 <;> (try dsimp [E, P, c, coefficientAt]) <;> ring
  have hb := integral_mono_ae (hgrad.const_mul (lam / 2))
    (hEi.add (hq.const_mul c)) hcpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add hEi (hq.const_mul c), integral_const_mul,
    integral_const_mul] at hb
  have hEeq : (∫ z in U, E z) =
      ∫ z in U, scalarTimeDerivative u z * u z * ρ z ^ 2 := by
    have _h_xinl_0 : (∫ z in Ioo a T ×ˢ O, ∑ i, ∑ j,
      (A z.1 z.2 i j * scalarSpatialGradient u z j *
        (ρ z ^ 2 * scalarSpatialGradient u z i +
          2 * ρ z * scalarSpatialGradient ρ z i * u z) +
        spatialPartial i (fun y => A z.1 y i j) z.2 *
          scalarSpatialGradient u z j * u z * ρ z ^ 2)) =
    ∫ z in Ioo a T ×ˢ O, scalarTimeDerivative u z * u z * ρ z ^ 2 := by
      classical
      let U := Ioo a T ×ˢ O
      have hU : IsOpen U := isOpen_Ioo.prod hO
      let L (i j : Fin d) (z : TimeVelocity d) :=
        A z.1 z.2 i j * scalarSpatialGradient u z j *
          (ρ z ^ 2 * scalarSpatialGradient u z i +
            2 * ρ z * scalarSpatialGradient ρ z i * u z)
      let R (i j : Fin d) (z : TimeVelocity d) :=
        (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
          A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)
      let E (i j : Fin d) (z : TimeVelocity d) :=
        spatialPartial i (fun y => A z.1 y i j) z.2 *
          scalarSpatialGradient u z j * u z * ρ z ^ 2
      let W (z : TimeVelocity d) := scalarTimeDerivative u z * u z * ρ z ^ 2
      have hL (i j : Fin d) : IntegrableOn (L i j) U :=
        (integrable_scalar_local_spatial_value_energy_terms hU u ρ hu hρ hc hsub A hA i j).1.restrict
      have hR (i j : Fin d) : IntegrableOn (R i j) U :=
        (integrable_scalar_local_spatial_value_energy_terms hU u ρ hu hρ hc hsub A hA i j).2.restrict
      have hE (i j : Fin d) : IntegrableOn (E i j) U := by
        have hcoeff :=
          (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
        have hcoeff12 := isScalarC12On_of_contDiff_two (hcoeff.of_le (by simp)) univ
        have hdA : Continuous (fun z : TimeVelocity d =>
            spatialPartial i (fun y => A z.1 y i j) z.2) :=
          (continuous_apply i).comp
            (continuousOn_univ.mp hcoeff12.continuousOn_scalarSpatialGradient)
        exact (integrable_local_cutoff_square_mul hU
          (fun z => spatialPartial i (fun y => A z.1 y i j) z.2 *
            scalarSpatialGradient u z j * u z) ρ
          ((hdA.continuousOn.mul ((continuous_apply j).comp_continuousOn
            hu.continuousOn_scalarSpatialGradient)).mul hu.continuousOn)
          hρ.continuous hc hsub).restrict
      have hW : IntegrableOn W U :=
        (integrable_local_cutoff_square_mul hU
          (fun z => scalarTimeDerivative u z * u z) ρ
          (hu.continuousOn_scalarTimeDerivative.mul hu.continuousOn) hρ.continuous hc hsub).restrict
      have hLs : IntegrableOn (fun z => ∑ i, ∑ j, L i j z) U :=
        integrable_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hL i j))
      have hRs : IntegrableOn (fun z => ∑ i, ∑ j, R i j z) U :=
        integrable_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hR i j))
      have hEs : IntegrableOn (fun z => ∑ i, ∑ j, E i j z) U :=
        integrable_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hE i j))
      have hflux : (∫ z in U, ∑ i, ∑ j, L i j z) = -(∫ z in U, ∑ i, ∑ j, R i j z) := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hL i j))]
        simp_rw [integral_finsetSum Finset.univ (fun j _ => hL _ j)]
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hR i j))]
        simp_rw [integral_finsetSum Finset.univ (fun j _ => hR _ j),
          ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        let left : TimeVelocity d → ℝ := fun z =>
          A z.1 z.2 i j * scalarSpatialGradient u z j *
            (ρ z ^ 2 * scalarSpatialGradient u z i +
              2 * ρ z * scalarSpatialGradient ρ z i * u z)
        let right : TimeVelocity d → ℝ := fun z =>
          (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
            A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)
        have hint := integrable_scalar_local_spatial_value_energy_terms (isOpen_Ioo.prod hO)
          u ρ hu hρ hc hsub A hA i j
        have hprod : (volume.restrict (Ioo a T)).prod (volume.restrict O) =
            volume.restrict (Ioo a T ×ˢ O : Set (TimeVelocity d)) := by
          rw [volume_timeVelocity_eq_prod]
          exact Measure.prod_restrict (Ioo a T) O
        have hl : Integrable left ((volume.restrict (Ioo a T)).prod (volume.restrict O)) := by
          rw [hprod]
          exact hint.1.restrict
        have hr : Integrable right ((volume.restrict (Ioo a T)).prod (volume.restrict O)) := by
          rw [hprod]
          exact hint.2.restrict
        change (∫ z in Ioo a T ×ˢ O, left z) = -(∫ z in Ioo a T ×ˢ O, right z)
        rw [← hprod, integral_prod left hl, integral_prod right hr, ← integral_neg]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
          (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
        have hslice : ContDiffOn ℝ 1 (fun y => A t y i j) O :=
          ((hcoeff.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffOn
        exact integral_scalar_local_spatial_value_energy_slice a T O hO u ρ hu hρ hc hsub
          A t ht i j hslice
      have hRval : (∫ z in U, ∑ i, ∑ j, R i j z) =
          (∫ z in U, ∑ i, ∑ j, E i j z) - ∫ z in U, W z := by
        rw [← integral_sub hEs hW]
        apply setIntegral_congr_fun hU.measurableSet
        intro z hz
        dsimp only
        have hpde := heq z hz
        change scalarTimeDerivative u z +
          (∑ i, ∑ j, A z.1 z.2 i j * scalarSpatialHessian u z i j) = 0 at hpde
        simp only [R, E, W, add_mul, Finset.sum_add_distrib,
          ← Finset.sum_mul]
        rw [show (∑ i, ∑ j, A z.1 z.2 i j * scalarSpatialHessian u z i j) =
          -scalarTimeDerivative u z by linarith only [hpde]]
        ring
      change (∫ z in U, ∑ i, ∑ j, (L i j z + E i j z)) = ∫ z in U, W z
      simp_rw [Finset.sum_add_distrib]
      rw [integral_add hLs hEs]
      linarith only [hflux, hRval]
    rw [← _h_xinl_0]
    apply setIntegral_congr_fun hU.measurableSet
    intro z _
    exact (local_value_energy_flux_eq (ρ z) (u z) (coefficientAt A z)
      (fun i j => spatialPartial i (fun y => A z.1 y i j) z.2)
      (G z) (scalarSpatialGradient ρ z)).symm
  rw [hEeq] at hb
  have htime : (∫ z in U, scalarTimeDerivative u z * u z * ρ z ^ 2) ≤
      (Kt / 2) * ∫ z in U, u z ^ 2 := by
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ z ^ 2) := hρ.pow 2
    have hχeq : (fun z => ρ z ^ 2) = ρ * ρ := by
      funext z
      exact pow_two _
    have hcχ : HasCompactSupport (fun z => ρ z ^ 2) := by
      rw [hχeq]
      exact HasCompactSupport.mul_left hc
    have hsχ : tsupport (fun z => ρ z ^ 2) ⊆ U := by
      simpa only [pow_two] using
        (tsupport_mul_subset_left (f := ρ) (g := ρ)).trans hsub
    have hw : IntegrableOn
        (fun z => scalarTimeDerivative u z * u z * ρ z ^ 2) U :=
      (integrable_local_cutoff_square_mul hU
        (fun z => scalarTimeDerivative u z * u z) ρ
        (hu.continuousOn_scalarTimeDerivative.mul hu.continuousOn)
        hρ.continuous hc hsub).restrict
    have htest := integral_square_mul_timeDerivative_eq hu
      (fun z => ρ z ^ 2) hχ hcχ hsχ
    have hdt : IntegrableOn
        (fun z => u z ^ 2 * timeDerivative (fun y => ρ y ^ 2) z) U := by
      have hdcont := hχ.continuous_fderiv (by simp)
      have hd : Continuous (timeDerivative (fun y => ρ y ^ 2)) :=
        hdcont.clm_apply continuous_const
      exact hq.mul_bdd hd.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem hU.measurableSet
          (fun z hz => by simpa only [Real.norm_eq_abs] using ht z hz))
    have hpoint : ∀ᵐ z ∂volume.restrict U,
        -(u z ^ 2 * timeDerivative (fun y => ρ y ^ 2) z) ≤ Kt * u z ^ 2 := by
      apply ae_restrict_of_forall_mem hU.measurableSet
      intro z hz
      have hd := (neg_le_abs (timeDerivative (fun y => ρ y ^ 2) z)).trans (ht z hz)
      convert mul_le_mul_of_nonneg_right hd (sq_nonneg (u z)) using 1
      ring
    have hb := integral_mono_ae hdt.neg (hq.const_mul Kt) hpoint
    have htval : (∫ z in U, 2 * u z * scalarTimeDerivative u z * ρ z ^ 2) =
        2 * ∫ z in U, scalarTimeDerivative u z * u z * ρ z ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    simp only [Pi.neg_apply] at hb
    rw [integral_neg, integral_const_mul, htest, htval] at hb
    linarith only [hb]
  dsimp only [G, c] at hb
  linarith only [hb, htime]

/- The smooth compact cutoff has a finite bound on the time derivative of its square. -/
end HypoellipticAleksandrov.Parabolic.LocalHolder
