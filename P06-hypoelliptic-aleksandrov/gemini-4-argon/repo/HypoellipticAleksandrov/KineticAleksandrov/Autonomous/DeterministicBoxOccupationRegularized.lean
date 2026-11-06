module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGreenFatou
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsVelocityBound
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsWeightBasic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationEndpoint
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGreenBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierLimit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsScaling
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGrowth
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalGreen
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsDuhamelPhysical
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsRegularizedBarrier
import Mathlib.MeasureTheory.Group.Integral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierErrorBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Actual regularized Bellman occupation, with every cutoff input discharged -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open Parabolic
open SectionTwo Evolution

/- The actual position-regularized homogeneous Bellman barrier satisfies occupation Green.
No modulus, joint regularity, bounded jet or Green identity is taken as a premise. -/
theorem deterministic_regularized_barrier_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam alpha c } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {phi : Z → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hc : 0 < c)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    let Phi := positionConvolution eta (bellmanOriginExtension phi)
    ENNReal.ofReal c *
      (∫⁻ q, ENNReal.ofReal (positionConvolution eta
        (fun w => bellmanGauge w ^ (alpha - 2)) (q.1 - Y, q.2))
          ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, Phi (q.1 - Y, q.2) ∂kernelXV E T z) - Phi (z.1 - Y, z.2)) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let Phi := positionConvolution eta (bellmanOriginExtension phi)
  let f := fun q : Z => Phi (q.1 - Y, q.2)
  let w := fun q : Z => positionConvolution eta
    (fun u => bellmanGauge u ^ (alpha - 2)) (q.1 - Y, q.2)
  have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) := ⟨kernelXV_mass_one hlam A E hE T z⟩
  have hPhi := barrier_position_regularization_joint h ha ha1 eta heta
  have hf : ContDiff ℝ 2 f := hPhi.comp
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  obtain ⟨D, hD, hm⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
  have hconvmod := positionConvolution_modulus eta heta (bellmanOriginExtension phi)
    (h.origin_extension_continuous ha) alpha D hD hm
  have hfm (q u : Z) : |f q - f u| ≤
      D * (|q.1 - u.1| ^ (alpha / 3) + |q.2 - u.2| ^ alpha) := by
    have he : q.1 - Y - (u.1 - Y) = q.1 - u.1 := by ring
    simpa only [f, Prod.fst, Prod.snd, he] using hconvmod (q.1 - Y, q.2) (u.1 - Y, u.2)
  obtain ⟨Bv, hBv, hbv⟩ : ∃ Bv : ℝ, 0 ≤ Bv ∧ ∀ q : ℝ × ℝ,
      |deriv (fun v => positionConvolution eta (bellmanOriginExtension phi) (q.1, v)) q.2| ≤ Bv := by
    let f := positionConvolution eta (bellmanOriginExtension phi)
    have hf := barrier_position_regularization_joint h ha ha1 eta heta
    have hc : Continuous (fun q : ℝ × ℝ => (fderiv ℝ f q) (0, 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (0, 1)).continuous.comp (hf.continuous_fderiv (by norm_num))
    have he (q : ℝ × ℝ) : deriv (fun v => f (q.1, v)) q.2 = (fderiv ℝ f q) (0, 1) :=
      (bellman_hasDerivAt_second (hf.differentiable (by norm_num) q)).deriv
    obtain ⟨S, Cv, hS, hCv, hbfar⟩ : ∃ S Cv : ℝ, 0 < S ∧ 0 ≤ Cv ∧ ∀ q : ℝ × ℝ,
        S + 1 < |q.1| ∨ 1 ≤ |q.2| →
        |deriv (fun v => positionConvolution eta (bellmanOriginExtension phi) (q.1, v)) q.2| ≤ Cv := by
        obtain ⟨S, hS, hbS⟩ := heta.2.1.isBounded.exists_pos_norm_lt
        have hbS' : ∀ x ∈ tsupport eta, |x| < S := by
          simpa only [Real.norm_eq_abs] using hbS
        obtain ⟨_, _, hv, _⟩ := h.origin_jet_bounds
        obtain ⟨Cv, hCv, hbv⟩ := hv
        refine ⟨S, Cv, hS, hCv, fun q hq => ?_⟩
        have hj := (barrier_position_convolution_velocity_jets h ha ha1 eta heta q.1 q.2).1
        rw [hj.deriv]
        have hi := position_kernel_integrable eta (fun Y => bellmanDv phi (Y, q.2))
          heta.1.continuous heta.2.1
          (barrier_velocity_fibers_locallyIntegrable h ha ha1 q.2).1 q.1
        have hηi : Integrable eta volume :=
          heta.1.continuous.integrable_of_hasCompactSupport heta.2.1
        have hbound (Y : ℝ) : |eta (q.1 - Y) * bellmanDv phi (Y, q.2)| ≤
            eta (q.1 - Y) * Cv := by
          by_cases hη : eta (q.1 - Y) = 0
          · simp only [hη, zero_mul, abs_zero, le_refl]
          have hρ : 1 ≤ bellmanGauge (Y, q.2) := by
              rcases hq with hx | hv
              · have he := hbS' (q.1 - Y) (subset_tsupport eta hη)
                have ht : |q.1| ≤ |q.1 - Y| + |Y| := by
                  calc
                    |q.1| = |q.1 - Y + Y| := by congr 1; ring
                    _ ≤ _ := abs_add_le _ _
                have hY : 1 ≤ |Y| := by linarith only [hx, he, ht]
                exact (Real.one_le_rpow hY (by norm_num : 0 ≤ (1 / 3 : ℝ))).trans
                  (BarrierRegularization.barrier_position_gauge_lower (Y, q.2))
              · exact hv.trans (bellmanGauge_coordinate_bounds (Y, q.2)).2

            /- The actual regularized velocity derivative is bounded outside a fixed rectangle. -/
          have hn := BarrierRegularization.barrier_gauge_one_ne_zero hρ
          have hv := (hbv (Y, q.2) hn).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hρ (by linarith)) hCv)
          rw [mul_one] at hv
          rw [abs_mul, abs_of_nonneg (heta.2.2.1 _)]
          exact mul_le_mul_of_nonneg_left hv (heta.2.2.1 _)
        unfold positionConvolution
        calc
          _ ≤ ∫ Y, |eta (q.1 - Y) * bellmanDv phi (Y, q.2)| := abs_integral_le_integral_abs
          _ ≤ ∫ Y, eta (q.1 - Y) * Cv :=
            integral_mono hi.abs ((hηi.comp_sub_left q.1).mul_const Cv) hbound
          _ = Cv := by
            rw [integral_mul_const, integral_sub_left_eq_self, heta.2.2.2, one_mul]

      /- Position regularization has a global bounded actual velocity derivative.
      The bound is proved from joint C² regularity on a compact rectangle and homogeneous decay
        outside. -/
    obtain ⟨B, hb⟩ := ((isCompact_Icc (a := -(S + 1)) (b := S + 1)).prod
      (isCompact_Icc (a := -1) (b := 1))).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max B Cv, hCv.trans (le_max_right _ _), fun q => ?_⟩
    by_cases hq : q ∈ Icc (-(S + 1)) (S + 1) ×ˢ Icc (-1) 1
    · rw [he q]
      have hqb : |(fderiv ℝ f q) (0, 1)| ≤ B := by
        simpa only [Real.norm_eq_abs] using hb q hq
      exact hqb.trans (le_max_left _ _)
    · have hfar : S + 1 < |q.1| ∨ 1 ≤ |q.2| := by
        by_contra hn
        push Not at hn
        exact hq ⟨abs_le.mp hn.1, (abs_le.mp hn.2.le)⟩
      exact (hbfar q hfar).trans (le_max_right _ _)
  have hfbv (q : Z) : |deriv (fun v => f (q.1, v)) q.2| ≤ Bv := hbv (q.1 - Y, q.2)
  have hw : Measurable w := (positionConvolution_measurable eta heta.1.continuous.measurable
    _ (bellmanGauge_continuous.measurable.pow_const _)).comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd)
  have hwn (q : Z) : 0 ≤ w q := integral_nonneg
    (fun X => mul_nonneg (heta.2.2.1 _) (Real.rpow_nonneg (bellmanGauge_nonneg _) _))
  have hfbound (q : Z) : c * w q ≤ physicalSpatialOperator A.a f q :=
    (barrier_position_regularization_of_positive_degree ha ha1 h hbound eta heta).2 A Y q
  have hdiff := (deterministic_barrier_endpoint_of_modulus hH hLE hlam hLam alpha D
    ha.le ha1.le hD Phi hPhi.continuous hconvmod A z T Y).1
  have hfi : Integrable f (kernelXV E T z) := by
    convert hdiff.add (integrable_const (Phi (z.1 - Y, z.2))) using 1
    funext q
    simp only [Pi.add_apply, f]
    rw [show q.1 - Y = -Y + q.1 by ring]
    ring
  have ha := ha.le
  have ha1 := ha1.le
  obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫⁻ q, ENNReal.ofReal (c * (barrierRectCutoff Y R q * w q))
        ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, barrierRectCutoff Y R q * f q ∂kernelXV E T z) -
        barrierRectCutoff Y R z * f z + C * (T : ℝ) / R) := by
    obtain ⟨D1, D2, hD1, hD2, hb1, hb2⟩ := barrierCutoff_derivative_bounds
    let C := (2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) + 2 * Lam * D1 * Bv
    have hL : 0 ≤ Lam := hlam.le.trans hLam
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C, hC, fun R hR => ?_⟩
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    let F := fun q : Z => barrierRectCutoff Y R q * f q
    let G := fun q : Z => c * (barrierRectCutoff Y R q * w q)
    let mu := physicalOccupationMeasure E z T
    have hFc : ContDiff ℝ 2 (fun z => barrierRectCutoff Y R z * f z) := by
      have hc : ContDiff ℝ 2 barrierCutoff := barrierCutoff_contDiff.of_le (by simp)
      exact ((hc.comp ((contDiff_fst.sub contDiff_const).div_const (R ^ 3))).mul
        (hc.comp (contDiff_snd.div_const R))).mul hf
    have hFs : HasCompactSupport (fun z => barrierRectCutoff Y R z * f z) := by
        apply HasCompactSupport.of_support_subset_isCompact
          ((isCompact_Icc (a := Y - 2 * R ^ 3) (b := Y + 2 * R ^ 3)).prod
            (isCompact_Icc (a := -(2 * R)) (b := 2 * R)))
        intro z hz
        by_contra hn
        have hlarge : 2 < |(z.1 - Y) / R ^ 3| ∨ 2 < |z.2 / R| := by
          by_contra hh
          push Not at hh
          apply hn
          have hx := (div_le_iff₀ (pow_pos hR0 3)).mp
            (by simpa only [abs_div, abs_of_pos (pow_pos hR0 3)] using hh.1)
          have hv := (div_le_iff₀ hR0).mp
            (by simpa only [abs_div, abs_of_pos hR0] using hh.2)
          have hxb := abs_le.mp hx
          have hvb := abs_le.mp hv
          exact ⟨⟨by linarith only [hxb.1], by linarith only [hxb.2]⟩, hvb⟩
        apply hz
        rcases hlarge with hx | hv
        · simp only [barrierRectCutoff, (barrierCutoff_zero_jets hx).1, zero_mul]
        · simp only [barrierRectCutoff, (barrierCutoff_zero_jets hv).1, mul_zero, zero_mul]

      /- The literal rectangular cutoff preserves joint C² regularity. -/
    have hFL := physicalSpatialOperator_continuous_compact A F hFc hFs
    have hFi := physicalSpatialOperator_occupation_integrable A F hFc hFs E z T
    have hcut : Continuous (barrierRectCutoff Y R) := by
      exact (barrierCutoff_contDiff.continuous.comp
        ((continuous_fst.sub continuous_const).div_const _)).mul
          (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))
    have hGm : Measurable G := (hcut.measurable.mul hw).const_mul c
    have hGn (q : Z) : 0 ≤ G q :=
      mul_nonneg hc.le (mul_nonneg (barrierRectCutoff_bounds _ _ _).1 (hwn q))
    have hGb (q : Z) : G q ≤ physicalSpatialOperator A.a F q + C / R := by
      have herr := barrierRectError_quantitative A.a f Lam alpha D Bv D1 D2 Y R
        hL ha ha1 hD hBv hD1 hD2 hfm hfbv hb1 hb2 hR q
        (hlam.le.trans (A.bounds _ _).1) (A.bounds _ _).2
      have hid : physicalSpatialOperator A.a (fun w => barrierRectCutoff Y R w * f w) q =
      barrierRectCutoff Y R q * physicalSpatialOperator A.a f q + barrierRectError A.a f Y R q := by
        let a := A.a
        let z := q
        let chi := fun X => barrierCutoff ((X - Y) / R ^ 3)
        let psi := scaledScalarCutoff barrierCutoff R
        let Phi := fun p : Point => f (p.position 0, p.velocity 0)
        let p : Point := ⟨0, fun _ => z.1, fun _ => z.2⟩
        have hc : ContDiff ℝ 2 barrierCutoff := barrierCutoff_contDiff.of_le (by simp)
        have hchi : ContDiff ℝ 2 chi := hc.comp ((contDiff_id.sub contDiff_const).div_const _)
        have hpsi : ContDiff ℝ 2 psi := scaledScalarCutoff_contDiff _ hc _
        have ht : DifferentiableAt ℝ (fun t => Phi ⟨t, p.position, p.velocity⟩) p.time := by
          change DifferentiableAt ℝ (fun _ : ℝ => f z) 0
          exact differentiableAt_const _
        have hx : DifferentiableAt ℝ (fun X => Phi ⟨p.time, fun _ => X, p.velocity⟩)
            (p.position 0) := by
          have hs : ContDiff ℝ 2 (fun X : ℝ => f (X, z.2)) :=
            hf.comp (contDiff_id.prodMk contDiff_const)
          exact hs.differentiable (by norm_num) z.1
        have hv : ContDiff ℝ 2 (fun v => Phi ⟨p.time, p.position, fun _ => v⟩) :=
          hf.comp (contDiff_const.prodMk contDiff_id)
        have hh := spatialCutoffTest_operator a chi psi hchi hpsi Phi p ht hx hv
        have he : spatialCutoffTest chi psi Phi =
            fun q : Point => (fun w => barrierRectCutoff Y R w * f w)
              (q.position 0, q.velocity 0) := rfl
        rw [he, ← physicalSpatialOperator_eq_forward a
          (fun w => barrierRectCutoff Y R w * f w) p] at hh
        change physicalSpatialOperator a (fun w => barrierRectCutoff Y R w * f w) z = _ at hh
        rw [← physicalSpatialOperator_eq_forward a f p, kineticVelocityGradient_scalar] at hh
        dsimp only [chi] at hh
        rw [barrier_position_cutoff_deriv, scaledScalarCutoff_second_deriv _ hc hR0.ne',
          scaledScalarCutoff_deriv _ hc] at hh
        simpa only [psi, Phi, p, barrierRectCutoff, barrierRectError, scaledScalarCutoff, Prod.mk.eta,
          add_assoc] using hh
      have hlift := mul_le_mul_of_nonneg_left (hfbound q) (barrierRectCutoff_bounds Y R q).1
      have heG : G q = barrierRectCutoff Y R q * (c * w q) := by dsimp only [G]; ring
      rw [← heG] at hlift
      have he := (neg_le_abs (barrierRectError A.a f Y R q)).trans herr
      change G q ≤ physicalSpatialOperator A.a F q + C / R
      linarith only [hid, hlift, he]
    obtain ⟨K, hbK⟩ := hFL.1.bounded_above_of_compact_support hFL.2
    have hGi : Integrable G mu := by
      apply (integrable_const (K + C / R)).mono' hGm.aestronglyMeasurable
      filter_upwards with q
      rw [Real.norm_eq_abs, abs_of_nonneg (hGn q)]
      have hLb : physicalSpatialOperator A.a F q ≤ K :=
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbK q)
      exact (hGb q).trans (add_le_add hLb le_rfl)
    have hi := integral_mono hGi (hFi.add (integrable_const (C / R))) hGb
    change (∫ q, G q ∂physicalOccupationMeasure E z T) ≤
      ∫ q, physicalSpatialOperator A.a F q + C / R ∂physicalOccupationMeasure E z T at hi
    rw [integral_add hFi (integrable_const (C / R)), integral_const,
      smul_eq_mul, measureReal_def, physicalOccupationMeasure_mass_eq hlam A E hE,
      ENNReal.toReal_ofReal hT.le] at hi
    have _h_xinl_0 : (∫ w, physicalSpatialOperator A.a F w ∂physicalOccupationMeasure E z T) =
      (∫ w, F w ∂kernelXV E T z) - F z := by
      let f := F
      let F := physicalCompactDatum f hFc.continuous hFs
      have hh := fullspace_green_spatial_compact_c2 hH hlam hLam A E hE T F
        (physicalCompactDatum_contDiff f hFc hFs) (physicalCompactDatum_hasCompactSupport f _ hFs)
        ⟨0, fun _ => z.2, fun _ => z.1⟩ hT
      have hL := physicalSpatialOperator_continuous_compact A f hFc hFs
      have hLi := physicalSpatialOperator_occupation_integrable A f hFc hFs E z T
      have heSource :
          ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
            (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
              (identityDrift 1) (fun q => F (q.position, q.velocity)) q)) =
          ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
            (fun q => -physicalSpatialOperator A.a f (nativeToXV (q.position, q.velocity)))) := by
        congr 1
        funext q
        exact congrArg Neg.neg (physicalSpatialOperator_eq_native A.a f q)
      rw [heSource, duhamelPotential_physical_occupation E z T
        (fun w => -physicalSpatialOperator A.a f w) hL.1.measurable.neg hLi.neg,
        integral_neg] at hh
      have heTerminal := integral_map nativeToXV_measurable.aemeasurable
        (hFc.continuous.measurable.aestronglyMeasurable (μ := kernelXV E T z))
      change (∫ w, f w ∂kernelXV E T z) =
        ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery T z) at heTerminal
      change -(∫ w, physicalSpatialOperator A.a f w ∂physicalOccupationMeasure E z T) =
        f z - ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery T z) at hh
      rw [← heTerminal] at hh
      linarith only [hh]
    rw [_h_xinl_0] at hi
    rw [← ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hGn)]
    apply ENNReal.ofReal_le_ofReal
    exact hi.trans_eq (by dsimp only [F]; ring)
  let F := fun n : ℕ => fun q : Z =>
    ENNReal.ofReal (c * (barrierRectCutoff Y ((n : ℝ) + 1) q * w q))
  let b := fun n : ℕ => (∫ q, barrierRectCutoff Y ((n : ℝ) + 1) q * f q ∂kernelXV E T z) -
    barrierRectCutoff Y ((n : ℝ) + 1) z * f z + C * (T : ℝ) / ((n : ℝ) + 1)
  have hmF (n : ℕ) : Measurable (F n) :=
    (((barrierRectCutoff_continuous _ _).measurable.mul hw).const_mul c).ennreal_ofReal
  have hpF (q : Z) : Tendsto (fun n => F n q) atTop (𝓝 (ENNReal.ofReal (c * w q))) := by
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [barrierRectCutoff_eventually_one Y q] with n hn
    simp only [F, hn, one_mul]
  have hcut0 : Tendsto (fun n : ℕ => barrierRectCutoff Y ((n : ℝ) + 1) z * f z)
      atTop (𝓝 (f z)) := by
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [barrierRectCutoff_eventually_one Y z] with n hn
    simp only [hn, one_mul]
  have herr : Tendsto (fun n : ℕ => C * (T : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_const_nhds (x := C * (T : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbt : Tendsto b atTop (𝓝 ((∫ q, f q ∂kernelXV E T z) - f z)) := by
    have hi : Tendsto (fun n : ℕ => ∫ z, barrierRectCutoff Y ((n : ℝ) + 1) z * f z ∂(kernelXV E T z))
      atTop (𝓝 (∫ z, f z ∂(kernelXV E T z))) := by
      let mu := (kernelXV E T z)
      have hf := hf.continuous.measurable
      apply tendsto_integral_of_dominated_convergence (fun z => |f z|)
      · intro n
        have hc : Continuous (barrierRectCutoff Y ((n : ℝ) + 1)) := by
          exact (barrierCutoff_contDiff.continuous.comp
            ((continuous_fst.sub continuous_const).div_const _)).mul
              (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))
        exact (hc.measurable.mul hf).aestronglyMeasurable
      · exact hfi.abs
      · intro n
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (barrierRectCutoff_bounds _ _ _).1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (barrierRectCutoff_bounds Y ((n : ℝ) + 1) z).2 (abs_nonneg (f z))
      · filter_upwards with z
        apply Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [barrierRectCutoff_eventually_one Y z] with n hn
        simp only [hn, one_mul]
    simpa only [add_zero] using (hi.sub hcut0).add herr
  have hboundF (n : ℕ) : (∫⁻ q, F n q ∂physicalOccupationMeasure E z T) ≤ ENNReal.ofReal (b n) :=
    hb ((n : ℝ) + 1) (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith only [hn])
  have hh := singular_fatou_of_real_bounds (physicalOccupationMeasure E z T) F
    (fun q => ENNReal.ofReal (c * w q)) hmF hpF b _ hbt hboundF
  simpa only [ENNReal.ofReal_mul hc.le,
    lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
