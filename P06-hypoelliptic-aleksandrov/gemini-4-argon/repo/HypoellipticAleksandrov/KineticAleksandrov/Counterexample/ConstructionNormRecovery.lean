module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyGeometry
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifyBound
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformExtended
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformTime
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSecondBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceIdentity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJointSource
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifiedJets
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionOperator
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceBound
import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # Positive-source norm recovery on the one fixed kinetic cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal
open scoped Convolution

/- Spatial smoothing of each fixed flattened cutoff recovers the positive source in
finite-exponent norm on the fixed cylinder, without an analytic premise. -/
theorem construction_positiveSource_error_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun P =>
      max (backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P) 0 -
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0)
      p (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)))
      atTop (𝓝 0) := by
  let Q := backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S
  let nu := volume.restrict Q
  have hQm : MeasurableSet Q := (isOpen_backwardCylinder _ _ hS).measurableSet
  have : IsFiniteMeasure nu := ⟨by
    simpa only [nu, Measure.restrict_apply_univ] using
      (backwardCylinder_volume_lt_top (⟨T, 0, 0⟩ : KineticPoint d) S hS)⟩
  let F := fun n P => backwardOperator (fun _t x v => profileMatrix h (x, v))
    (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P
  let g := fun P => constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)
  have hA := (selectedProfile_spec h).2.2.2.2.1
  have hF (n : ℕ) : Measurable (F n) :=
    measurable_backwardOperator_of_joint_smooth (profileMatrix h) hA _
      (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
        (fun q hq => (hmargin q hq).trans hm) (standardMollifierSequence n))
  have hg : Measurable g := (construction_indicatorSource_measurable h r mu R).comp
    (KineticPoint.measurable_equivProd d)
  let AC := 3 * (|profileLowerEllipticity h| + |profileUpperEllipticity h|)
  have hAC : 0 ≤ AC := mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hAb q i k : |profileMatrix h q i k| ≤ AC :=
    coefficient_entry_abs_le_of_ellipticity
      ((selectedProfile_spec h).2.2.2.2.2.1 q).1
      ((selectedProfile_spec h).2.2.2.2.2.1 q).2 i k
  obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ phi : ContDiffBump (0 : XV d), ∀ P : KineticPoint d,
      P.time ∈ Icc (T - S ^ 2) T → (∀ i, |P.velocity i| ≤ S) →
      |backwardOperator (fun _t x v => (profileMatrix h) (x, v))
        (smoothedZeroExtendedProfile h r mu R phi) P| ≤ C := by
    let a := (T - S ^ 2)
    have hS := hS.le
    let A := (profileMatrix h)
    have hg (i : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a T,
      ∀ᵐ q ∂volume, |constructionExtendedNativeGradient h r mu R m t q (Fin.castAdd d i)| ≤ C := by
      let i := (Fin.castAdd d i)
      let K := (spatialCoordinateCLE d).symm '' {q | profileFunction h q ≤ 1}
      have hK : IsCompact K := (isCompact_profile_unit_sublevel ha h).image
        (spatialCoordinateCLE d).symm.continuous
      obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a T, ∀ x ∈ K,
          |spatialPackedCutoffGradient h r mu R t x i| ≤ C := by
          let D := Icc a T ×ˢ K
          have hD : IsCompact D := isCompact_Icc.prod hK
          obtain ⟨C, hC, hb⟩ := construction_packedGradient_compact_bound h r hr i K hK
          have hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
              |spatialPackedGradient (flatProfilePositionJet h r)
                (flatProfileVelocityJet h r) z.2 i| ≤ C :=
            ⟨C, hC, fun z hz => hb z.2 hz.2⟩
          have hg := construction_compact_scalar_bound D hD _
            (construction_barrier_gradient_joint_continuous d mu R i)
          obtain ⟨N, hN, hbN⟩ := construction_scalar_bound_sub D _ _ hf hg
          refine ⟨N, hN, fun t ht x hx => ?_⟩
          have htheta := timeCutoffTheta_deriv_bounds
            (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x)
          rw [spatialPackedCutoffGradient, abs_mul, abs_of_nonneg htheta.1]
          exact (mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)).trans
            (by simpa only [one_mul] using hbN (t, x) ⟨ht, hx⟩)


      refine ⟨C, hC, fun t ht => ?_⟩
      have hz := construction_ae_native _
        (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm
          hscale (fun q hq => (hmargin q hq).le) t)
      filter_upwards [hz] with q hq
      let x := (spatialCoordinateCLE d).symm q
      by_cases hp : profileFunction h q < 1
      · have hp' : profileFunction h (spatialCoordinateCLE d x) < 1 := by
          simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp
        rw [constructionExtendedNativeGradient,
          (construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin x hp').1 i]
        exact hb t ht x ⟨q, hp.le, rfl⟩
      · have hp' : 1 ≤ profileFunction h (spatialCoordinateCLE d x) := by
          simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using not_lt.mp hp
        change |constructionExtendedPackedGradient h r mu R m t x i| ≤ C
        rw [(hq hp').1 i, abs_zero]
        exact hC
    have hh (i k : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a T,
      ∀ᵐ q ∂volume, |constructionExtendedNativeHessian h r mu R m t q i k| ≤ C := by
      let K := (spatialCoordinateCLE d).symm '' {q | profileFunction h q ≤ 1}
      have hK : IsCompact K := (isCompact_profile_unit_sublevel ha h).image
        (spatialCoordinateCLE d).symm.continuous
      obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a T, ∀ x ∈ K,
          |spatialPackedCutoffVelocityHessian h r mu R t x i k| ≤ C := by
        let D := Icc a T ×ˢ K
        have hD : IsCompact D := isCompact_Icc.prod hK
        obtain ⟨M, hM, hbM⟩ := flatProfile_jets_compact_bound_of_profile h r hr
          ((spatialCoordinateCLE d) '' K) (hK.image (spatialCoordinateCLE d).continuous)
        have hh : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
            |flatProfileHessian h r (spatialCoordinateCLE d z.2) i k| ≤ C :=
          ⟨M, hM, fun z hz => (hbM _ ⟨z.2, hz.2, rfl⟩).2.2 i k⟩
        have hg (j : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
            |flatProfileVelocityJet h r (spatialCoordinateCLE d z.2) j -
              PDE.classicalGradient (spatialPackedBarrier d mu R z.1) z.2 (Fin.natAdd d j)|
              ≤ C := by
          have hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
              |flatProfileVelocityJet h r (spatialCoordinateCLE d z.2) j| ≤ C :=
            ⟨M, hM, fun z hz => by
              simpa only [Real.norm_eq_abs] using
                (norm_le_pi_norm _ j).trans (hbM _ ⟨z.2, hz.2, rfl⟩).2.1⟩
          exact construction_scalar_bound_sub D _ _ hf
            (construction_compact_scalar_bound D hD _
              (construction_barrier_gradient_joint_continuous d mu R (Fin.natAdd d j)))
        have _h_xinl_0 : Continuous (fun z : ℝ × PDE.Vec (d + d) => PDE.classicalGradient (fun y => PDE.classicalGradient (spatialPackedBarrier d mu R z.1) y (Fin.natAdd d k)) z.2 (Fin.natAdd d i)) := by
          simp only [spatialPackedBarrier_velocityHessian]
          exact (((continuous_const.mul (continuous_const.mul continuous_fst).rexp).div_const
            (R ^ 2)).neg).mul continuous_const
        obtain ⟨N, hN, hbN⟩ := construction_scalar_bound_sub D _ _ hh
          (construction_compact_scalar_bound D hD _
            _h_xinl_0)
        obtain ⟨C, hC, hbC⟩ := construction_scalar_bound_mul D _ _ (hg i) (hg k)
        obtain ⟨L, hL, hbL⟩ := timeCutoffTheta_deriv2_abs_bound
        refine ⟨N + L * C, add_nonneg hN (mul_nonneg hL.le hC), fun t ht x hx => ?_⟩
        have htheta := timeCutoffTheta_deriv_bounds
          (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x)
        unfold spatialPackedCutoffVelocityHessian
        apply (abs_add_le _ _).trans
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg htheta.1]
          exact (mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)).trans
            (by simpa only [one_mul] using hbN (t, x) ⟨ht, hx⟩)
        · rw [mul_assoc, abs_mul]
          exact mul_le_mul (hbL _) (hbC (t, x) ⟨ht, hx⟩) (abs_nonneg _) hL.le
      refine ⟨C, hC, fun t ht => ?_⟩
      have hz := construction_ae_native _
        (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm
          hscale (fun q hq => (hmargin q hq).le) t)
      filter_upwards [hz] with q hq
      let x := (spatialCoordinateCLE d).symm q
      by_cases hp : profileFunction h q < 1
      · have hp' : profileFunction h (spatialCoordinateCLE d x) < 1 := by
          simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp
        rw [constructionExtendedNativeHessian,
          (construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin x hp').2 i k]
        exact hb t ht x ⟨q, hp.le, rfl⟩
      · have hp' : 1 ≤ profileFunction h (spatialCoordinateCLE d x) := by
          simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using not_lt.mp hp
        change |constructionExtendedPackedHessian h r mu R m t x i k| ≤ C
        rw [(hq hp').2 i k, abs_zero]
        exact hC
    choose G hG hbG using hg
    choose H hH hbH using hh
    obtain ⟨CT, hCT, hbCT⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a T, ∀ q,
      |constructionExtendedTimeJet h r mu R t q| ≤ C := by
      let K := Icc a T ×ˢ {q | profileFunction h q ≤ 1}
      have hK : IsCompact K := isCompact_Icc.prod (isCompact_profile_unit_sublevel ha h)
      obtain ⟨C, hC, hb⟩ := construction_compact_scalar_bound K hK _
        (construction_rawTimeJet_joint_continuous h r mu R)
      refine ⟨C, hC, fun t ht q => ?_⟩
      by_cases hp : profileFunction h q < 1
      · have hq : q ∈ {y | profileFunction h y < 1} := hp
        rw [constructionExtendedTimeJet, indicator_of_mem hq]
        exact hb (t, q) ⟨ht, hp.le⟩
      · have hq : q ∉ {y | profileFunction h y < 1} := hp
        rw [constructionExtendedTimeJet, indicator_of_notMem hq, abs_zero]
        exact hC
    let C := CT + (∑ i : Fin d, S * G i) + ∑ i : Fin d, ∑ k : Fin d, AC * H i k
    have hC : 0 ≤ C := add_nonneg
      (add_nonneg hCT (Finset.sum_nonneg (fun i _ => mul_nonneg hS (hG i))))
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
        (fun k _ => mul_nonneg hAC (hH i k))))
    refine ⟨C, hC, fun phi P ht hv => ?_⟩
    have htg := construction_spatialMollify_norm_le_ae phi
      (constructionExtendedTimeJet h r mu R P.time)
      (construction_extendedTimeJet_locallyIntegrable h r mu R P.time).aestronglyMeasurable
      CT hCT (Filter.Eventually.of_forall (hbCT P.time ht)) (P.position, P.velocity)
    have hgg (i : Fin d) := construction_spatialMollify_norm_le_ae phi
      (fun q => constructionExtendedNativeGradient h r mu R m P.time q (Fin.castAdd d i))
      (construction_locallyIntegrable_native _
        (construction_extendedGradient_locallyIntegrable h r hr mu R m P.time
          (Fin.castAdd d i))).aestronglyMeasurable
      (G i) (hG i) (hbG i P.time ht) (P.position, P.velocity)
    have hhh (i k : Fin d) := construction_spatialMollify_norm_le_ae phi
      (fun q => constructionExtendedNativeHessian h r mu R m P.time q i k)
      (construction_locallyIntegrable_native _

          (construction_extendedHessian_locallyIntegrable h r hr mu R
            m P.time i k)).aestronglyMeasurable
      (H i k) (hH i k) (hbH i k P.time ht) (P.position, P.velocity)
    rw [construction_smoothed_operator_eq hd ha ha1 h r mu R m hr hmu hR hm hscale
      (fun q hq => (hmargin q hq).le)]
    apply (abs_sub _ _).trans
    apply add_le_add
    · apply (abs_add_le _ _).trans
      apply add_le_add
      · simpa only [Real.norm_eq_abs] using htg
      · unfold PDE.vecDot
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul (hv i) (by simpa only [Real.norm_eq_abs] using hgg i)
          (abs_nonneg _) hS
    · unfold matrixContraction
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hAb _ i k) (by simpa only [Real.norm_eq_abs] using hhh i k)
        (abs_nonneg _) hAC
  have hFb (n : ℕ) : ∀ᵐ P ∂nu, |F n P| ≤ C := by
    filter_upwards [ae_restrict_mem hQm] with P hP
    have hh := (construction_mem_cylinder_iff T S hS P).mp hP
    exact hb (standardMollifierSequence n) P ⟨hh.1.le, hh.2.1.le⟩
      (fun i => (PDE.abs_apply_le_vecEuclideanNorm P.velocity i).trans hh.2.2.1.le)
  have _h_xinl_0 : ∀ᵐ P : KineticPoint d ∂volume, Tendsto (fun n => backwardOperator (fun _t x v => profileMatrix h (x, v)) (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P) atTop (𝓝 (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P))) := by
    have hF (n : ℕ) := measurable_backwardOperator_of_joint_smooth (profileMatrix h) ((selectedProfile_spec h).2.2.2.2.1)
      (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n))
      (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
        (fun q hq => (hmargin q hq).trans hm) (standardMollifierSequence n))
    have he := construction_fixed_time_tendsto_ae_spacetime
      (fun n z => backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n))
        ((KineticPoint.equivProd d).symm z)) (constructionIndicatorSource h r mu R)
      (fun n => (hF n).comp (KineticPoint.measurable_equivProd_symm d))
      (construction_indicatorSource_measurable h r mu R) ?_
    · simpa only [Equiv.symm_apply_apply] using! he
    · intro t
      have _h_xinl_0 : ∀ᵐ q : XV d ∂volume, Tendsto (fun n => backwardOperator (fun _t x v => (profileMatrix h) (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) ⟨t, q.1, q.2⟩)
        atTop (𝓝 (constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩)) := by
        have hmargin := (fun q hq => (hmargin q hq).le)
        let A := (profileMatrix h)
        have ht := construction_spatialMollify_tendsto_ae _
          (construction_extendedTimeJet_locallyIntegrable h r mu R t)
        have _h_xinl_0 : ∀ᵐ q ∂volume,
            (∀ i : Fin (d + d), Tendsto
              (fun n => spatialMollify (standardMollifierSequence n)
                (fun y => constructionExtendedNativeGradient h r mu R m t y i) q)
              atTop (𝓝 (constructionExtendedNativeGradient h r mu R m t q i))) ∧
            (∀ i k : Fin d, Tendsto
              (fun n => spatialMollify (standardMollifierSequence n)
                (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q)
              atTop (𝓝 (constructionExtendedNativeHessian h r mu R m t q i k))) := by
          have hg (i : Fin (d + d)) := construction_spatialMollify_tendsto_ae
            (fun y => constructionExtendedNativeGradient h r mu R m t y i)
            (construction_locallyIntegrable_native _
              (construction_extendedGradient_locallyIntegrable h r hr mu R m t i))
          have hh (i k : Fin d) := construction_spatialMollify_tendsto_ae
            (fun y => constructionExtendedNativeHessian h r mu R m t y i k)
            (construction_locallyIntegrable_native _
              (construction_extendedHessian_locallyIntegrable h r hr mu R m t i k))
          exact (ae_all_iff.mpr hg).and (ae_all_iff.mpr fun i => ae_all_iff.mpr (hh i))
        filter_upwards [ht, _h_xinl_0] with q hqt hq
        have hx := tendsto_finsetSum Finset.univ (fun i _ =>
          (hq.1 (Fin.castAdd d i)).const_mul (q.2 i))
        have hh := tendsto_finsetSum Finset.univ (fun i _ =>
          tendsto_finsetSum Finset.univ (fun k _ => (hq.2 i k).const_mul (A q i k)))
        have he := (hqt.add hx).sub hh
        simp_rw [construction_smoothed_operator_eq hd ha ha1 h r mu R m hr hmu hR hm
          hscale hmargin]
        simpa only [constructionExtendedSource, PDE.vecDot, matrixContraction] using! he
      filter_upwards [_h_xinl_0,
        construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m hr hmu hR hm
          hscale hmargin t] with q hq heq
      simpa only [constructionIndicatorSource_apply,
        ← heq] using! hq
  have hl : ∀ᵐ P ∂nu, Tendsto (fun n => F n P) atTop (𝓝 (g P)) :=
    ae_restrict_of_ae _h_xinl_0
  have hgb : ∀ᵐ P ∂nu, |g P| ≤ C := by
    filter_upwards [hl, ae_all_iff.mpr hFb] with P hP hbP
    exact le_of_tendsto' hP.abs hbP
  have hF : ∀ n, AEStronglyMeasurable (F n) nu := (fun n => (hF n).aestronglyMeasurable)
  have hg : AEStronglyMeasurable g nu := hg.aestronglyMeasurable
  apply bounded_convergence_eLpNorm nu p hp0 hpTop _
    (fun n => ((hF n).aemeasurable.max aemeasurable_const).aestronglyMeasurable.sub
      (hg.aemeasurable.max aemeasurable_const).aestronglyMeasurable) (2 * C)
  · intro n
    filter_upwards [hFb n, hgb] with x hx hy
    have hbF : |max (F n x) 0| ≤ C := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans hx) hC
    have hbg : |max (g x) 0| ≤ C := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans hy) hC
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using!
      (abs_sub _ _).trans (show |max (F n x) 0| + |max (g x) 0| ≤ 2 * C by
        linarith only [hbF, hbg])
  · filter_upwards [hl] with x hx
    simpa only [Pi.sub_apply, sub_self] using! ((hx.max (tendsto_const_nhds (x := (0 : ℝ)))).sub_const (max (g x) 0))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
