module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionContinuous
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionSlices
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusEstimates
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- Off the origin the extension has the original local germ. -/
theorem barrierExtension_eventuallyEq (phi : (ℝ × ℝ) → ℝ) {q : ℝ × ℝ}
    (hq : q ≠ (0, 0)) : bellmanOriginExtension phi =ᶠ[𝓝 q] phi := by
  filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
  exact bellmanOriginExtension_eqOn phi hz


/-- The position coordinate gives its own cube-root gauge lower bound. -/
theorem barrier_position_gauge_lower (q : ℝ × ℝ) : |q.1| ^ (1 / 3 : ℝ) ≤ bellmanGauge q := by
  have hh := Real.rpow_le_rpow (abs_nonneg q.1) (bellmanGauge_coordinate_bounds q).1
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have he : (bellmanGauge q ^ 3) ^ (1 / 3 : ℝ) = bellmanGauge q := by
    rw [← Real.rpow_natCast_mul (bellmanGauge_nonneg q)]
    norm_num
  rwa [he] at hh

/-- A negative homogeneous gauge bound has a uniform position-fiber power majorant. -/
theorem barrier_position_fiber_bound (beta : ℝ) (hb : beta ≤ 0)
    (f : (ℝ × ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta)
    (X v : ℝ) (hX : X ≠ 0) : |f (X, v)| ≤ C * |X| ^ (beta / 3) := by
  have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
  have hh := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos (abs_pos.mpr hX) _) (barrier_position_gauge_lower (X, v)) hb
  rw [← Real.rpow_mul (abs_nonneg X)] at hh
  have he : (1 / 3 : ℝ) * beta = beta / 3 := by ring
  rw [he] at hh
  exact (hbound _ hq).trans (mul_le_mul_of_nonneg_left hh hC)


/-- Dominated C² jets give actual C² regularity of their parameter integral. -/
theorem singular_parameter_integral_contDiffOn_two
    {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace A] (mu : Measure A)
    {U : Set E} (hU : IsOpen U)
    (f : E → A → F) (f' : E → A → E →L[ℝ] F)
    (f'' : E → A → E →L[ℝ] (E →L[ℝ] F))
    (b0 b1 b2 : A → ℝ) (hb0 : Integrable b0 mu) (hb1 : Integrable b1 mu)
    (hb2 : Integrable b2 mu)
    (hm0 : ∀ x ∈ U, AEStronglyMeasurable (f x) mu)
    (hm1 : ∀ x ∈ U, AEStronglyMeasurable (f' x) mu)
    (hm2 : ∀ x ∈ U, AEStronglyMeasurable (f'' x) mu)
    (hn0 : ∀ᵐ a ∂mu, ∀ x ∈ U, ‖f x a‖ ≤ b0 a)
    (hn1 : ∀ᵐ a ∂mu, ∀ x ∈ U, ‖f' x a‖ ≤ b1 a)
    (hn2 : ∀ᵐ a ∂mu, ∀ x ∈ U, ‖f'' x a‖ ≤ b2 a)
    (hd0 : ∀ᵐ a ∂mu, ∀ x ∈ U, HasFDerivAt (fun y => f y a) (f' x a) x)
    (hd1 : ∀ᵐ a ∂mu, ∀ x ∈ U, HasFDerivAt (fun y => f' y a) (f'' x a) x)
    (hc2 : ∀ᵐ a ∂mu, ContinuousOn (fun x => f'' x a) U) :
    ContDiffOn ℝ 2 (fun x => ∫ a, f x a ∂mu) U ∧
      (∀ x ∈ U, HasFDerivAt (fun y => ∫ a, f y a ∂mu) (∫ a, f' x a ∂mu) x) ∧
      (∀ x ∈ U, HasFDerivAt (fun y => ∫ a, f' y a ∂mu) (∫ a, f'' x a ∂mu) x) := by
  have hi0 x (hx : x ∈ U) : Integrable (f x) mu :=
    hb0.mono' (hm0 x hx) (hn0.mono (fun a ha => ha x hx))
  have hi1 x (hx : x ∈ U) : Integrable (f' x) mu :=
    hb1.mono' (hm1 x hx) (hn1.mono (fun a ha => ha x hx))
  have hd0I x (hx : x ∈ U) :
      HasFDerivAt (fun y => ∫ a, f y a ∂mu) (∫ a, f' x a ∂mu) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (hU.mem_nhds hx)
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hm0 y hy
    · exact hi0 x hx
    · exact hm1 x hx
    · exact hn1
    · exact hb1
    · exact hd0
  have hd1I x (hx : x ∈ U) :
      HasFDerivAt (fun y => ∫ a, f' y a ∂mu) (∫ a, f'' x a ∂mu) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (hU.mem_nhds hx)
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hm1 y hy
    · exact hi1 x hx
    · exact hm2 x hx
    · exact hn2
    · exact hb2
    · exact hd1
  have hcI : ContinuousOn (fun x => ∫ a, f'' x a ∂mu) U := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hm2 y hy
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hn2.mono (fun a ha => ha y hy)
    · exact hb2
    · exact hc2.mono (fun a ha => ha.continuousAt (hU.mem_nhds hx))
  refine ⟨?_, hd0I, hd1I⟩
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ a, f' y a ∂mu, ⟨U, hU.mem_nhds hx, hd0I⟩, ?_⟩
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ a, f'' y a ∂mu, ⟨U, hU.mem_nhds hx, hd1I⟩, ?_⟩
  exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds hx, hcI⟩


/-- The scalar position projection used by the parameter jets. -/
def barrierPositionProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The scalar velocity projection used by the parameter jets. -/
def barrierVelocityProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The actual position convolution integrand, with the integration variable fixed. -/
def barrierConvolutionIntegrand (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : ℝ := κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)

/-- The first parameter jet of the actual convolution integrand. -/
def barrierConvolutionJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (deriv κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) • barrierPositionProjection +
    (κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierVelocityProjection

/-- The second parameter jet, displaying only position kernel and velocity source derivatives. -/
def barrierConvolutionSecondJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection).smulRight barrierPositionProjection +
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection).smulRight
      barrierVelocityProjection






/-- A scalar combination of the two coordinate projections has its elementary norm bound. -/
theorem barrier_projection_norm_le (a b : ℝ) :
    ‖a • barrierPositionProjection + b • barrierVelocityProjection‖ ≤ |a| + |b| := by
  exact (norm_add_le _ _).trans_eq (by
    simp [norm_smul, barrierPositionProjection, barrierVelocityProjection, ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd])

/-- The first convolution jet only needs the value and first velocity fiber majorants. -/
theorem barrierConvolutionJet_norm_le (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) :
    ‖barrierConvolutionJet κ phi q Y‖ ≤
      |deriv κ (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        |κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| := by
  simpa only [barrierConvolutionJet, abs_mul] using
    barrier_projection_norm_le
      (deriv κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
      (κ (q.1 - Y) * bellmanDv phi (Y, q.2))

/-- The second convolution jet needs only the locally integrable second velocity majorant. -/
theorem barrierConvolutionSecondJet_norm_le (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) :
    ‖barrierConvolutionSecondJet κ phi q Y‖ ≤
      |deriv (deriv κ) (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        2 * |deriv κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| +
          |κ (q.1 - Y)| * |bellmanDvv phi (Y, q.2)| := by
  unfold barrierConvolutionSecondJet
  have h1 := barrier_projection_norm_le
    (deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
    (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
  have h2 := barrier_projection_norm_le
    (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
    (κ (q.1 - Y) * bellmanDvv phi (Y, q.2))
  have hh := norm_add_le
    ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection |>.smulRight barrierPositionProjection)
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection
        |>.smulRight barrierVelocityProjection)
  have hX : ‖barrierPositionProjection‖ = 1 := ContinuousLinearMap.norm_fst ℝ ℝ ℝ
  have hv : ‖barrierVelocityProjection‖ = 1 := ContinuousLinearMap.norm_snd ℝ ℝ ℝ
  simp [ContinuousLinearMap.norm_smulRight_apply, hX, hv] at hh
  simp at h1 h2
  linarith only [hh, h1, h2]


/-- Both scalar kernel derivatives used in the second parameter jet are continuous. -/
theorem barrier_kernel_derivatives_continuous (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) :
    Continuous (deriv κ) ∧ Continuous (deriv (deriv κ)) := by
  have hd : ContDiff ℝ 1 (deriv κ) := hκ.deriv'
  exact ⟨hκ.continuous_deriv (by norm_num), hd.continuous_deriv_one⟩



/-- Scalar measurable coefficients give a measurable coordinate linear form. -/
theorem barrier_projection_measurable {T : Type*} [MeasurableSpace T]
    {a b : T → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => a x • barrierPositionProjection + b x • barrierVelocityProjection) :=
  (ha.smul measurable_const).add (hb.smul measurable_const)

/-- Scalar continuous coefficients give a continuous coordinate linear form. -/
theorem barrier_projection_continuous {T : Type*} [TopologicalSpace T]
    {a b : T → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => a x • barrierPositionProjection + b x • barrierVelocityProjection) :=
  (ha.smul continuous_const).add (hb.smul continuous_const)




/-- Position convolution of the continuous extension, in physical coordinate order. -/
def positionBarrierConvolution (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  ∫ Y, barrierConvolutionIntegrand κ phi q Y

/-- Compact scalar kernels and both derivatives have simultaneous finite global bounds. -/
theorem barrier_kernel_uniform_bounds (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ)
    (hs : HasCompactSupport κ) :
    ∃ K0 K1 K2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧
      (∀ x, |κ x| ≤ K0) ∧ (∀ x, |deriv κ x| ≤ K1) ∧
        ∀ x, |deriv (deriv κ) x| ≤ K2 := by
  obtain ⟨hc1, hc2⟩ := barrier_kernel_derivatives_continuous κ hκ
  obtain ⟨K0, hb0⟩ := hκ.continuous.bounded_above_of_compact_support hs
  obtain ⟨K1, hb1⟩ := hc1.bounded_above_of_compact_support hs.deriv
  obtain ⟨K2, hb2⟩ := hc2.bounded_above_of_compact_support hs.deriv.deriv
  refine ⟨max K0 0, max K1 0, max K2 0, le_max_right _ _, le_max_right _ _,
    le_max_right _ _, ?_, ?_, ?_⟩
  · intro x
    simpa using (hb0 x).trans (le_max_left K0 0)
  · intro x
    simpa using (hb1 x).trans (le_max_left K1 0)
  · intro x
    simpa using (hb2 x).trans (le_max_left K2 0)

/-- Both scalar coordinates of a parameter in the unit ball stay in their unit intervals. -/
theorem barrier_parameter_ball_bounds {q q0 : ℝ × ℝ} (hq : q ∈ Metric.ball q0 1) :
    |q.1 - q0.1| < 1 ∧ |q.2 - q0.2| < 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hq
  exact ⟨by simpa using (norm_fst_le (q -
    q0)).trans_lt hq,
    by simpa using (norm_snd_le (q -
      q0)).trans_lt hq⟩

/-- A compact integration window contains every nearby translated kernel support. -/
theorem barrier_convolution_support_window (κ : ℝ → ℝ) (hs : HasCompactSupport κ)
    (q0 : ℝ × ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ q ∈ Metric.ball q0 1, ∀ Y : ℝ, Y ∉ Icc (-R) R →
      κ (q.1 - Y) = 0 ∧ deriv κ (q.1 - Y) = 0 ∧ deriv (deriv κ) (q.1 - Y) = 0 := by
  obtain ⟨S, hS, hSb⟩ := hs.isBounded.exists_pos_norm_lt
  let R := |q0.1| + S + 2
  refine ⟨R, by dsimp only [R]; positivity, fun q hq Y hY => ?_⟩
  have hn : q.1 - Y ∉ tsupport κ := by
    intro ht
    have hsmall := hSb (q.1 - Y) ht
    rw [Real.norm_eq_abs] at hsmall
    have hqabs : |q.1| ≤ |q0.1| + |q.1 - q0.1| := by
      calc |q.1| = |q0.1 + (q.1 - q0.1)| := by congr 1; ring
           _ ≤ _ := by simpa using norm_add_le q0.1 (q.1 - q0.1)
    have hYabs : |Y| ≤ |q.1| + |Y - q.1| := by
      calc |Y| = |q.1 + (Y - q.1)| := by congr 1; ring
           _ ≤ _ := by simpa using norm_add_le q.1 (Y - q.1)
    have hYlarge := lt_of_not_ge (fun hh => hY (abs_le.mp hh))
    rw [abs_sub_comm Y q.1] at hYabs
    dsimp only [R] at hYlarge
    linarith only [hqabs, ((barrier_parameter_ball_bounds hq).1), hYabs, hsmall, hYlarge]
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport (fun hh => hn (tsupport_deriv_subset hh))⟩




end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

section



namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- The position coordinate gives its own cube-root gauge lower bound. -/
theorem barrier_position_gauge_lower (q : ℝ × ℝ) : |q.1| ^ (1 / 3 : ℝ) ≤ bellmanGauge q := by
  have hh := Real.rpow_le_rpow (abs_nonneg q.1) (bellmanGauge_coordinate_bounds q).1
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have he : (bellmanGauge q ^ 3) ^ (1 / 3 : ℝ) = bellmanGauge q := by
    rw [← Real.rpow_natCast_mul (bellmanGauge_nonneg q)]
    norm_num
  rwa [he] at hh


/-- The three jet fibers are integrable on every compact position interval, uniformly in v. -/
theorem barrier_jet_fiber_integrable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (v a b : ℝ) :
    IntegrableOn (fun X => bellmanDx phi (X, v)) (Icc a b) volume ∧
    IntegrableOn (fun X => bellmanDv phi (X, v)) (Icc a b) volume ∧
    IntegrableOn (fun X => bellmanDvv phi (X, v)) (Icc a b) volume  := by
  have barrier_position_fiber_bound (beta : ℝ) (hb : beta ≤ 0) (f : (ℝ × ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta) (X : ℝ) (hX : X ≠ 0) :
      |f (X, v)| ≤ C * |X| ^ (beta / 3) := by
    have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
    have hh := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos (abs_pos.mpr hX) _) (barrier_position_gauge_lower (X, v)) hb
    rw [← Real.rpow_mul (abs_nonneg X)] at hh
    have he : (1 / 3 : ℝ) * beta = beta / 3 := by ring
    rw [he] at hh
    exact (hbound _ hq).trans (mul_le_mul_of_nonneg_left hh hC)
  have hi (beta : ℝ) (hb : -3 < beta) (hb0 : beta ≤ 0)
      (f : (ℝ × ℝ) → ℝ) (hc : ContinuousOn f bellmanPuncturedSet)
      (C : ℝ) (hC : 0 ≤ C)
      (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta) :
      IntegrableOn (fun X => f (X, v)) (Icc a b) volume := by
    have hm : Measurable (fun X => f (X, v)) :=
      (measurable_of_continuousOn_compl_singleton (0, 0) hc).comp
        (measurable_id.prodMk measurable_const)
    have hmaj := ((bellman_abs_rpow_locallyIntegrable (beta / 3) (by linarith)).smul C)
      |>.integrableOn_isCompact (isCompact_Icc (a := a) (b := b))
    apply hmaj.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with X hX
    simpa using
      barrier_position_fiber_bound beta hb0 f C hC hbound X hX
  obtain ⟨_, hX, hv, hvv⟩ := h.origin_jet_bounds
  obtain ⟨CX, hCX, hbX⟩ := hX
  obtain ⟨Cv, hCv, hbv⟩ := hv
  obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
  refine ⟨?_, ?_, ?_⟩
  · exact hi (alpha - 3) (by linarith) (by linarith) _ h.dx_continuousOn CX hCX hbX
  · exact hi (alpha - 1) (by linarith) (by linarith) _
      (h.directional_contDiffOn (0, 1)).continuousOn Cv hCv hbv
  · exact hi (alpha - 2) (by linarith) (by linarith) _ h.dvv_continuousOn Cvv hCvv hbvv


/-- A continuous function with a locally integrable derivative off zero has no point defect. -/
theorem singular_line_weak_derivative (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : LocallyIntegrable g volume) (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (g x) x)
    (test : ℝ → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ x, f x * deriv test x) = -(∫ x, g x * test x) := by
  have h1 := hg.integrable_smul_right_of_hasCompactSupport ht.continuous hs
  have h2 := (hf.locallyIntegrable (μ := volume)).integrable_smul_right_of_hasCompactSupport
    (ht.continuous_deriv (by norm_num)) hs.deriv
  simp at h1 h2
  let H := fun x => f x * test x
  let D := fun x => g x * test x + f x * deriv test x
  have hD : Integrable D volume := h1.add h2
  have hH := hf.mul ht.continuous
  have hHk : HasCompactSupport H := hs.mul_left
  have hdH (x : ℝ) (hx : x ≠ 0) : HasDerivAt H (D x) x :=
    (hd x hx).mul ((ht.differentiable (by norm_num) x).hasDerivAt)
  have he := integral_add_compl (s := Iic 0) measurableSet_Iic hD
  rw [compl_Iic, (integral_Iic_of_hasDerivAt_of_tendsto (hH.continuousAt.continuousWithinAt (x := 0)) (fun x hx => hdH x hx.ne) hD.integrableOn (hHk.is_zero_at_infty.mono_left atBot_le_cocompact)), (integral_Ioi_of_hasDerivAt_of_tendsto (hH.continuousAt.continuousWithinAt (x := 0)) (fun x hx => hdH x hx.ne') hD.integrableOn (hHk.is_zero_at_infty.mono_left atTop_le_cocompact))] at he
  have hz : (∫ x, D x) = 0 := by linarith only [he]
  rw [integral_add h1 h2] at hz
  linarith only [hz]

/-- Each actual position derivative fiber is locally integrable on the full position line. -/
theorem barrier_dx_fiber_locallyIntegrable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1) (v : ℝ) :
    LocallyIntegrable (fun X => bellmanDx phi (X, v)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR, hRb⟩ := hK.isBounded.exists_pos_norm_lt
  apply (barrier_jet_fiber_integrable h ha ha1 v (-R) R).1.mono_set
  intro x hx
  have hh := hRb x hx
  rw [Real.norm_eq_abs] at hh
  exact abs_le.mp hh.le

/-- The actual position convolution moves its derivative onto the source jet even at v=0. -/
theorem barrier_position_fiber_weak_dx {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (v : ℝ) (test : ℝ → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ X, bellmanOriginExtension phi (X, v) * deriv test X) =
      -(∫ X, bellmanDx phi (X, v) * test X) := by
  apply singular_line_weak_derivative _ _
    ((h.origin_extension_continuous ha).comp (continuous_id.prodMk continuous_const))
    (barrier_dx_fiber_locallyIntegrable h ha ha1 v) ?_ test ht hs
  intro X hX
  have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
  have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
    (by norm_num)
  exact (bellman_hasDerivAt_first hd).congr_of_eventuallyEq
    ((barrierExtension_eventuallyEq phi hq).comp_tendsto
      ((continuous_id.prodMk continuous_const).tendsto X))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory BarrierRegularization Filter HypoellipticAleksandrov
open scoped Convolution Topology

/-- Position-only convolution, leaving the velocity coordinate fixed. -/
def positionConvolution (eta : ℝ → ℝ) (Phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  ∫ X, eta (q.1 - X) * Phi (X, q.2)

/-- A compact smooth approximate-identity kernel at any fixed positive scale. -/
def IsNonnegativeUnitSmoothMollifier (eta : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
    (∀ X, 0 ≤ eta X) ∧ (∫ X, eta X) = 1

/-- The convolution is the ordinary scalar convolution of each position fiber. -/
theorem positionConvolution_eq (eta : ℝ → ℝ) (Phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    positionConvolution eta Phi q =
      ((fun X => Phi (X, q.2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] eta) q.1 := by
  unfold positionConvolution convolution
  congr 1
  funext X
  exact mul_comm _ _


/-- Any locally integrable fiber can be tested against a translated compact smooth kernel. -/
theorem position_kernel_integrable (eta f : ℝ → ℝ) (heta : Continuous eta)
    (hc : HasCompactSupport eta) (hf : LocallyIntegrable f volume) (X : ℝ) :
    Integrable (fun Y => eta (X - Y) * f Y) volume := by
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', mul_comm] using (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf heta X)

/-- All source velocity fibers are locally integrable, including at velocity zero. -/
theorem barrier_velocity_fibers_locallyIntegrable {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha) (ha1 : alpha < 1) (v : ℝ) :
    LocallyIntegrable (fun X => bellmanDv Phi (X, v)) volume ∧
      LocallyIntegrable (fun X => bellmanDvv Phi (X, v)) volume := by
  have hi (f : ℝ → ℝ) (hf : ∀ a b, IntegrableOn f (Icc a b) volume) :
      LocallyIntegrable f volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_lt
    apply (hf (-R) R).mono_set
    intro x hx
    exact abs_le.mp (by simpa using (hR x hx).le)
  exact ⟨hi _ (fun a b => (barrier_jet_fiber_integrable h ha ha1 v a b).2.1),
    hi _ (fun a b => (barrier_jet_fiber_integrable h ha ha1 v a b).2.2)⟩

/-- The convolved source weight is a genuine integrable position fiber. -/
theorem barrier_weight_fiber_locallyIntegrable (alpha : ℝ) (ha : 0 < alpha)
    (ha1 : alpha < 1) (v : ℝ) :
    LocallyIntegrable (fun X => bellmanGauge (X, v) ^ (alpha - 2)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hm : Measurable (fun X => bellmanGauge (X, v) ^ (alpha - 2)) :=
    ((bellmanGauge_continuous.comp (continuous_id.prodMk continuous_const)).measurable).pow_const _
  apply ((bellman_abs_rpow_locallyIntegrable ((alpha - 2) / 3) (by linarith)).integrableOn_isCompact hK).mono' hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _)]
  simpa [abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _)] using (barrier_position_fiber_bound (alpha - 2) (by linarith) (fun q => bellmanGauge q ^ (alpha - 2)) 1 zero_le_one (fun q _ => by rw [abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _), one_mul]) X v hX)

/-- The coefficient is held at the evaluation point while integrating the source inequality.
This is an inequality for the convolved actual source jets, without any derivative of `a`. -/
theorem barrier_convolved_jet_inequality {lam Lam alpha c : ℝ}
    {Phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha Phi)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b Phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta)
    (A : SmoothAutonomous lam Lam) (Y : ℝ) (q : ℝ × ℝ) :
    c * positionConvolution eta (fun w => bellmanGauge w ^ (alpha - 2))
      (q.1 - Y, q.2) ≤
      q.2 * positionConvolution eta (bellmanDx Phi) (q.1 - Y, q.2) +
        A.a q.1 q.2 * positionConvolution eta (bellmanDvv Phi) (q.1 - Y, q.2) := by
  have hiX := position_kernel_integrable eta _ heta.1.continuous heta.2.1
    (barrier_dx_fiber_locallyIntegrable h ha ha1 q.2) (q.1 - Y)
  have hivv := position_kernel_integrable eta _ heta.1.continuous heta.2.1
    (barrier_velocity_fibers_locallyIntegrable h ha ha1 q.2).2 (q.1 - Y)
  have hh := integral_mono_ae ((position_kernel_integrable eta _ heta.1.continuous heta.2.1 (barrier_weight_fiber_locallyIntegrable alpha ha ha1 q.2) (q.1 - Y)).const_mul c)
    ((hiX.const_mul q.2).add (hivv.const_mul (A.a q.1 q.2))) ?_
  · simpa [positionConvolution, integral_add (hiX.const_mul q.2)
      (hivv.const_mul (A.a q.1 q.2)), integral_const_mul] using hh
  · filter_upwards [volume.ae_ne 0] with X hX
    have hq : (X, q.2) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
    have hi := mul_le_mul_of_nonneg_left (hbound (X, q.2) hq (A.a q.1 q.2) (A.bounds q.1 q.2)) (heta.2.2.1 (q.1 - Y - X))
    dsimp only [bellmanOperator] at hi
    simpa [mul_add, mul_left_comm, mul_assoc] using hi




/-- Both actual velocity derivatives commute with position convolution, including at v=0. -/
theorem barrier_position_convolution_velocity_jets {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) (X v : ℝ) :
    HasDerivAt (fun w => positionConvolution eta (bellmanOriginExtension Phi) (X, w))
      (positionConvolution eta (bellmanDv Phi) (X, v)) v ∧
    HasDerivAt (fun w => positionConvolution eta (bellmanDv Phi) (X, w))
      (positionConvolution eta (bellmanDvv Phi) (X, v)) v  := by
  have position_convolution_velocity_hasDerivAt (f : (ℝ × ℝ) → ℝ) (g : (ℝ × ℝ) → ℝ) (hf : LocallyIntegrable (fun Y => f (Y, v)) volume) (hg : Measurable g) (p : ℝ) (C : ℝ) (hp : -1 < p) (hb : ∀ Y : ℝ, Y ≠ 0 → ∀ w : ℝ, |g (Y, w)| ≤ C * |Y| ^ p) (hd : ∀ Y : ℝ, Y ≠ 0 → ∀ w : ℝ,
      HasDerivAt (fun u => f (Y, u)) (g (Y, w)) w) (hfm : ∀ w : ℝ, Measurable (fun Y => f (Y, w))) :
      HasDerivAt (fun w => positionConvolution eta f (X, w))
      (positionConvolution eta g (X, v)) v := by
    unfold positionConvolution
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w Y => eta (X - Y) * f (Y, w))
      (F' := fun w Y => eta (X - Y) * g (Y, w))
      (s := univ) (bound := fun Y => C * (eta (X - Y) * |Y| ^ p)) (μ := volume)
      (by simp) ?_ (position_kernel_integrable eta _ heta.1.continuous heta.2.1 hf X)
      ?_ ?_ ((position_kernel_integrable eta (fun Y => |Y| ^ p) heta.1.continuous heta.2.1 (bellman_abs_rpow_locallyIntegrable p hp) X).const_mul C) ?_).2
    · exact Eventually.of_forall (fun w =>
        ((heta.1.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
          (hfm w)).aestronglyMeasurable)
    · exact ((heta.1.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
        (hg.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    · filter_upwards [volume.ae_ne 0] with Y hY w _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heta.2.2.1 (X - Y))]
      exact (mul_le_mul_of_nonneg_left (hb Y hY w) (heta.2.2.1 (X - Y))).trans_eq
        (by ring)
    · filter_upwards [volume.ae_ne 0] with Y hY w _
      exact (hd Y hY w).const_mul (eta (X - Y))
  obtain ⟨_, _, ⟨Cv, hCv, hbv⟩, ⟨Cvv, hCvv, hbvv⟩⟩ := h.origin_jet_bounds
  have hmv := measurable_of_continuousOn_compl_singleton (0, 0)
    (h.directional_contDiffOn (0, 1)).continuousOn
  constructor
  · apply position_convolution_velocity_hasDerivAt _ _
      ((h.origin_extension_continuous ha).comp
        (continuous_id.prodMk continuous_const)).locallyIntegrable
      hmv ((alpha - 1) / 3) Cv (by linarith)
      (fun Y hY w => barrier_position_fiber_bound (alpha - 1) (by linarith)
        _ Cv hCv hbv Y w hY)
    · intro Y hY w
      have hq : (Y, w) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
      have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
        (by norm_num)
      exact (bellman_hasDerivAt_second hd).congr_of_eventuallyEq
        ((barrierExtension_eventuallyEq Phi hq).comp_tendsto
          ((continuous_const.prodMk continuous_id).tendsto w))
    · intro w
      exact (h.origin_extension_continuous ha).measurable.comp
        (measurable_id.prodMk measurable_const)
  · apply position_convolution_velocity_hasDerivAt _ _
      (barrier_velocity_fibers_locallyIntegrable h ha ha1 v).1
      (measurable_of_continuousOn_compl_singleton (0, 0) h.dvv_continuousOn) ((alpha - 2) / 3) Cvv (by linarith)
      (fun Y hY w => barrier_position_fiber_bound (alpha - 2) (by linarith)
        _ Cvv hCvv hbvv Y w hY)
    · intro Y hY w
      have hq : (Y, w) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
      have hd := ((h.directional_contDiffOn (0, 1)).contDiffAt
        (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
      exact bellman_hasDerivAt_second hd
    · intro w
      exact hmv.comp (measurable_id.prodMk measurable_const)




/-- The precise separate regularity asserted for the position-regularized barrier. -/
def IsCInfinityPositionC2Velocity (f : (ℝ × ℝ) → ℝ) : Prop :=
  (∀ v : ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun X => f (X, v))) ∧
    ∀ X : ℝ, ContDiff ℝ 2 (fun v => f (X, v))

/-- Regularity and the scalar forward-operator inequality for any actual source barrier.
The conclusion displays `v ∂X + a(X,v) ∂vv` without introducing another PDE interface. -/
theorem barrier_position_regularization_of_positive_degree
    {lam Lam alpha c : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (h : IsBellmanHomogeneous alpha Phi)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b Phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    IsCInfinityPositionC2Velocity (positionConvolution eta (bellmanOriginExtension Phi)) ∧
      ∀ (A : SmoothAutonomous lam Lam) (Y : ℝ) (q : ℝ × ℝ),
        c * positionConvolution eta (fun w => bellmanGauge w ^ (alpha - 2))
          (q.1 - Y, q.2) ≤
        q.2 * deriv (fun X =>
          positionConvolution eta (bellmanOriginExtension Phi) (X - Y, q.2)) q.1 +
        A.a q.1 q.2 * deriv (deriv (fun v =>
          positionConvolution eta (bellmanOriginExtension Phi) (q.1 - Y, v))) q.2    := by
  have barrier_position_convolution_position_jet (X : ℝ) (v : ℝ) :
      HasDerivAt (fun w => positionConvolution eta (bellmanOriginExtension Phi) (w, v))
      (positionConvolution eta (bellmanDx Phi) (X, v)) X := by
    have hf : LocallyIntegrable (fun Y => bellmanOriginExtension Phi (Y, v)) volume :=
      ((h.origin_extension_continuous ha).comp
        (continuous_id.prodMk continuous_const)).locallyIntegrable
    have hd := HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hf heta.2.1 (heta.1.of_le (by norm_cast)) X
    have ht : ContDiff ℝ 1 (fun Y => eta (X - Y)) :=
      (heta.1.of_le (by norm_cast)).comp (contDiff_const.sub contDiff_id)
    have hw := barrier_position_fiber_weak_dx h ha ha1 v _ ht (heta.2.1.comp_homeomorph (Homeomorph.subLeft X))
    simp only [deriv_comp_const_sub, mul_neg, integral_neg] at hw
    have he : positionConvolution (deriv eta) (bellmanOriginExtension Phi) (X, v) =
        positionConvolution eta (bellmanDx Phi) (X, v) := by
      dsimp only [positionConvolution]
      simpa only [neg_inj, mul_comm] using hw
    have hefun : ((fun Y => bellmanOriginExtension Phi (Y, v))
        ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] eta) =
        (fun w => positionConvolution eta (bellmanOriginExtension Phi) (w, v)) :=
      funext fun w => (positionConvolution_eq eta _ (w, v)).symm
    rw [hefun, ← positionConvolution_eq (deriv eta) _ (X, v), he] at hd
    exact hd
  have barrier_position_convolution_velocity_c2 (X : ℝ) :
      ContDiff ℝ 2 (fun v => positionConvolution eta (bellmanOriginExtension Phi) (X, v)) := open Filter in by
    have position_convolution_velocity_continuous (g : (ℝ × ℝ) → ℝ) (hg : Measurable g) (p : ℝ) (C : ℝ) (hp : -1 < p) (hb : ∀ Y : ℝ, Y ≠ 0 → ∀ w : ℝ, |g (Y, w)| ≤ C * |Y| ^ p) (hc : ∀ Y : ℝ, Y ≠ 0 → Continuous (fun w => g (Y, w))) :
        Continuous (fun w => positionConvolution eta g (X, w)) := by
      have hbound := (position_kernel_integrable eta (fun Y => |Y| ^ p)
        heta.1.continuous heta.2.1 (bellman_abs_rpow_locallyIntegrable p hp) X).const_mul C
      apply continuous_iff_continuousAt.mpr
      intro v
      unfold positionConvolution
      apply continuousAt_of_dominated (bound := fun Y => C * (eta (X - Y) * |Y| ^ p))
      · exact Eventually.of_forall (fun w =>
          ((heta.1.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
            (hg.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
      · exact Eventually.of_forall (fun w => by
          filter_upwards [volume.ae_ne 0] with Y hY
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heta.2.2.1 (X - Y))]
          exact (mul_le_mul_of_nonneg_left (hb Y hY w) (heta.2.2.1 (X - Y))).trans_eq
            (by ring))
      · exact hbound
      · filter_upwards [volume.ae_ne 0] with Y hY
        exact (continuous_const.mul (hc Y hY)).continuousAt
    have hj := barrier_position_convolution_velocity_jets h ha ha1 eta heta X
    have he : deriv (fun v => positionConvolution eta (bellmanOriginExtension Phi) (X, v)) =
        (fun v => positionConvolution eta (bellmanDv Phi) (X, v)) := funext fun v => (hj v).1.deriv
    have he2 : deriv (fun v => positionConvolution eta (bellmanDv Phi) (X, v)) =
        (fun v => positionConvolution eta (bellmanDvv Phi) (X, v)) := funext fun v => (hj v).2.deriv
    obtain ⟨_, _, _, ⟨C, hC, hb⟩⟩ := h.origin_jet_bounds
    have hc : Continuous (fun v => positionConvolution eta (bellmanDvv Phi) (X, v)) := by
      apply position_convolution_velocity_continuous _
        (measurable_of_continuousOn_compl_singleton (0, 0) h.dvv_continuousOn)
        ((alpha - 2) / 3) C (by linarith)
        (fun Y hY w => barrier_position_fiber_bound (alpha - 2) (by linarith) _ C hC hb Y w hY)
      intro Y hY
      exact h.dvv_continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun w he => hY (congrArg Prod.fst he))
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun v => (hj v).1.differentiableAt, (by norm_num), ?_⟩
    rw [he, contDiff_one_iff_deriv, he2]
    exact ⟨fun v => (hj v).2.differentiableAt, hc⟩
  have barrier_position_convolution_smooth (v : ℝ) :
      ContDiff ℝ (⊤ : ℕ∞)
      (fun X => positionConvolution eta (bellmanOriginExtension Phi) (X, v)) := by
    have hf : LocallyIntegrable (fun X => bellmanOriginExtension Phi (X, v)) volume :=
      ((h.origin_extension_continuous ha).comp
      (continuous_id.prodMk continuous_const)).locallyIntegrable
    simpa only [positionConvolution_eq] using
      heta.2.1.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf heta.1
  refine ⟨⟨barrier_position_convolution_smooth,
    barrier_position_convolution_velocity_c2⟩, ?_⟩
  intro A Y q
  have hxshift := (barrier_position_convolution_position_jet (q.1 - Y) q.2).comp q.1 ((hasDerivAt_id q.1).sub_const Y)
  have he : deriv (fun v =>
      positionConvolution eta (bellmanOriginExtension Phi) (q.1 - Y, v)) =
      (fun v => positionConvolution eta (bellmanDv Phi) (q.1 - Y, v)) := by
    funext v
    exact (barrier_position_convolution_velocity_jets h ha ha1 eta heta (q.1 - Y) v).1.deriv
  rw [he, ((barrier_position_convolution_velocity_jets h ha ha1 eta heta (q.1 - Y) q.2).2.deriv)]
  have hxe : deriv (fun X =>
      positionConvolution eta (bellmanOriginExtension Phi) (X - Y, q.2)) q.1 =
      positionConvolution eta (bellmanDx Phi) (q.1 - Y, q.2) := by
    simpa [Function.comp_def] using hxshift.deriv
  rw [hxe]
  exact barrier_convolved_jet_inequality h ha ha1 hbound eta heta A Y q


/-- The position convolution agrees with the literal parameter integral. -/
theorem positionConvolution_barrier_eq (eta : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ) :
    positionConvolution eta (bellmanOriginExtension phi) =
      positionBarrierConvolution eta phi := rfl

/-- Position smoothing has joint C² regularity required by the compact Green API. -/
theorem barrier_position_regularization_joint {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    ContDiff ℝ 2 (positionConvolution eta (bellmanOriginExtension phi))  := by
  have positionBarrierConvolution_contDiff (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ) :
      ContDiff ℝ 2 (positionBarrierConvolution κ phi) := by
    have barrier_slice_hasFDerivAt (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
        HasFDerivAt (fun p => bellmanOriginExtension phi (Y, p.2))
        (bellmanDv phi (Y, q.2) • barrierVelocityProjection) q := by
      have hq : (Y, q.2) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
      have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
        (by norm_num)
      have hslice := (bellman_hasDerivAt_second hd).congr_of_eventuallyEq
        ((barrierExtension_eventuallyEq phi hq).comp_tendsto
          ((continuous_const.prodMk continuous_id).tendsto q.2))
      exact hslice.comp_hasFDerivAt q hasFDerivAt_snd
    have positionBarrierConvolution_jet_spec (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (hs : HasCompactSupport κ) :
        ∀ q0 : ℝ × ℝ,
        ContDiffAt ℝ 2 (positionBarrierConvolution κ phi) q0 ∧
        HasFDerivAt (positionBarrierConvolution κ phi) (∫ Y, barrierConvolutionJet κ phi q0 Y) q0 ∧
        HasFDerivAt (fun q => ∫ Y, barrierConvolutionJet κ phi q Y)
          (∫ Y, barrierConvolutionSecondJet κ phi q0 Y) q0 := by
      intro q0
      have barrierConvolutionSecondJet_continuous (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (Y : ℝ) (hY : Y ≠ 0) :
          Continuous (fun q => barrierConvolutionSecondJet κ phi q Y) := by
        have barrier_velocity_jets_parameter_continuous :
            Continuous (fun q : ℝ × ℝ => bellmanDv phi (Y, q.2)) ∧
            Continuous (fun q : ℝ × ℝ => bellmanDvv phi (Y, q.2)) := by
          have hmap : MapsTo (fun q : ℝ × ℝ => (Y, q.2)) univ bellmanPuncturedSet :=
            fun _ _ he => hY (congrArg Prod.fst he)
          have hc : ContinuousOn (fun q : ℝ × ℝ => (Y, q.2)) univ :=
            (continuous_const.prodMk continuous_snd).continuousOn
          exact ⟨continuousOn_univ.mp ((h.directional_contDiffOn (0, 1)).continuousOn.comp hc hmap),
            continuousOn_univ.mp (h.dvv_continuousOn.comp hc hmap)⟩
        obtain ⟨hk1, hk2⟩ := barrier_kernel_derivatives_continuous κ hκ
        obtain ⟨hv, hvv⟩ := barrier_velocity_jets_parameter_continuous
        have hp : Continuous (fun q : ℝ × ℝ => bellmanOriginExtension phi (Y, q.2)) :=
          (h.origin_extension_continuous ha).comp (continuous_const.prodMk continuous_snd)
        have hk0 : Continuous (fun q : ℝ × ℝ => κ (q.1 - Y)) := hκ.continuous.comp (continuous_fst.sub
          continuous_const)
        have hk1' : Continuous (fun q : ℝ × ℝ => deriv κ (q.1 - Y)) := hk1.comp (continuous_fst.sub
          continuous_const)
        have hk2' : Continuous (fun q : ℝ × ℝ => deriv (deriv κ) (q.1 - Y)) := hk2.comp
          (continuous_fst.sub continuous_const)
        let LX := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
          barrierPositionProjection
        let Lv := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
          barrierVelocityProjection
        have h1 := barrier_projection_continuous (hk2'.mul hp) (hk1'.mul hv)
        have h2 := barrier_projection_continuous (hk1'.mul hv) (hk0.mul hvv)
        exact (LX.continuous.comp h1).add (Lv.continuous.comp h2)
      have barrierConvolutionJets_measurable (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (q : ℝ × ℝ) :
          Measurable (barrierConvolutionJet κ phi q) ∧
          Measurable (barrierConvolutionSecondJet κ phi q) := by
        have barrier_velocity_jets_measurable : Measurable (bellmanDv phi) ∧ Measurable (bellmanDvv phi) :=
          ⟨measurable_of_continuousOn_compl_singleton (0, 0)
                (h.directional_contDiffOn (0, 1)).continuousOn,
              measurable_of_continuousOn_compl_singleton (0, 0) h.dvv_continuousOn⟩
        obtain ⟨hk1, hk2⟩ := barrier_kernel_derivatives_continuous κ hκ
        obtain ⟨hmv, hmvv⟩ := barrier_velocity_jets_measurable
        have hm0 : Measurable (fun Y : ℝ => bellmanOriginExtension phi (Y, q.2)) :=
          (h.origin_extension_continuous ha).measurable.comp
          (measurable_id.prodMk measurable_const)
        have hm1 : Measurable (fun Y : ℝ => bellmanDv phi (Y, q.2)) := hmv.comp (measurable_id.prodMk
          measurable_const)
        have hm2 : Measurable (fun Y : ℝ => bellmanDvv phi (Y, q.2)) := hmvv.comp (measurable_id.prodMk
          measurable_const)
        have hk0 : Measurable (fun Y : ℝ => κ (q.1 - Y)) := hκ.continuous.measurable.comp
          (measurable_const.sub measurable_id)
        have hk1' : Measurable (fun Y : ℝ => deriv κ (q.1 - Y)) := hk1.measurable.comp
          (measurable_const.sub measurable_id)
        have hk2' : Measurable (fun Y : ℝ => deriv (deriv κ) (q.1 - Y)) := hk2.measurable.comp
          (measurable_const.sub measurable_id)
        constructor
        · exact barrier_projection_measurable (hk1'.mul hm0) (hk0.mul hm1)
        · let LX := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
            barrierPositionProjection
          let Lv := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ)).flip
            barrierVelocityProjection
          have h1 := barrier_projection_measurable (hk2'.mul hm0) (hk1'.mul hm1)
          have h2 := barrier_projection_measurable (hk1'.mul hm1) (hk0.mul hm2)
          exact (LX.continuous.measurable.comp h1).add (Lv.continuous.measurable.comp h2)
      have barrierConvolutionJet_hasFDerivAt (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
          HasFDerivAt (fun p => barrierConvolutionJet κ phi p Y)
          (barrierConvolutionSecondJet κ phi q Y) q := by
        have barrier_dv_slice_hasFDerivAt :
            HasFDerivAt (fun p : ℝ × ℝ => bellmanDv phi (Y, p.2))
            (bellmanDvv phi (Y, q.2) • barrierVelocityProjection) q := by
          have hq : (Y, q.2) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
          have hd := ((h.directional_contDiffOn (0, 1)).contDiffAt
            (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
          exact (bellman_hasDerivAt_second hd).comp_hasFDerivAt q hasFDerivAt_snd
        have hk := ((hκ.differentiable (by norm_num) (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
          ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
        have hk' := ((hκ.differentiable_deriv_two (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
          ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
        have hp := barrier_slice_hasFDerivAt q Y hY
        have hp' := barrier_dv_slice_hasFDerivAt
        have hh := ((hk'.mul hp).smul_const barrierPositionProjection).add
          ((hk.mul hp').smul_const barrierVelocityProjection)
        convert hh using 1
        · rfl
        · apply ContinuousLinearMap.ext
          intro w
          apply ContinuousLinearMap.ext
          intro u
          simp [barrierConvolutionSecondJet, barrierPositionProjection, barrierVelocityProjection]
          ring
      have barrierConvolutionIntegrand_hasFDerivAt (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ) (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
          HasFDerivAt (fun p => barrierConvolutionIntegrand κ phi p Y)
          (barrierConvolutionJet κ phi q Y) q := by
        have hk := ((hκ.differentiable (by norm_num) (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
          ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
        have hh := hk.mul (barrier_slice_hasFDerivAt q Y hY)
        convert hh using 1
        · rfl
        · apply ContinuousLinearMap.ext
          intro w
          simp [barrierConvolutionJet, barrierPositionProjection, barrierVelocityProjection]
          ring
      obtain ⟨R, hR, hwindow⟩ := barrier_convolution_support_window κ hs q0
      let K := Icc (-R) R
      let U := Metric.ball q0 1
      let mu := volume.restrict K
      have hmu : IsFiniteMeasure mu := by
        constructor
        rw [Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top
      let := hmu
      obtain ⟨K0, K1, K2, hK0, hK1, hK2, hbκ0, hbκ1, hbκ2⟩ :=
        barrier_kernel_uniform_bounds κ hκ hs
      obtain ⟨_, _, hv, hvv⟩ := h.origin_jet_bounds
      obtain ⟨Cv, hCv, hbv⟩ := hv
      obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
      have hψ := h.origin_extension_continuous ha
      obtain ⟨B0, hB0b⟩ := ((isCompact_Icc (a := -R) (b := R)).prod
        (isCompact_Icc (a := q0.2 - 1) (b := q0.2 + 1))).exists_bound_of_continuousOn
          hψ.continuousOn
      let B := max B0 0
      have hB : 0 ≤ B := le_max_right _ _
      have hbphi (q : ℝ × ℝ) (hq : q ∈ U) (Y : ℝ) (hY : Y ∈ K) :
          |bellmanOriginExtension phi (Y, q.2)| ≤ B := by
        have hqv := (barrier_parameter_ball_bounds hq).2
        have hv : q.2 ∈ Icc (q0.2 - 1) (q0.2 + 1) := by
          have hh := abs_lt.mp hqv
          constructor <;> linarith only [hh.1, hh.2]
        have hh := hB0b (Y, q.2) ⟨hY, hv⟩
        rw [Real.norm_eq_abs] at hh
        exact hh.trans (le_max_left _ _)
      let p1 := (alpha - 1) / 3
      let p2 := (alpha - 2) / 3
      let b0 := fun _ : ℝ => K0 * B
      let b1 := fun Y : ℝ => K1 * B + K0 * Cv * |Y| ^ p1
      let b2 := fun Y : ℝ => K2 * B + 2 * K1 * Cv * |Y| ^ p1 + K0 * Cvv * |Y| ^ p2
      have hi1 : Integrable (fun Y : ℝ => |Y| ^ p1) mu :=
        (bellman_abs_rpow_locallyIntegrable p1 (by dsimp only [p1]; linarith))
          |>.integrableOn_isCompact isCompact_Icc
      have hi2 : Integrable (fun Y : ℝ => |Y| ^ p2) mu :=
        (bellman_abs_rpow_locallyIntegrable p2 (by dsimp only [p2]; linarith))
          |>.integrableOn_isCompact isCompact_Icc
      have hb0 : Integrable b0 mu := integrable_const _
      have hb1 : Integrable b1 mu := (integrable_const _).add (hi1.const_mul (K0 * Cv))
      have hb2 : Integrable b2 mu := ((integrable_const _).add
        (hi1.const_mul (2 * K1 * Cv))).add (hi2.const_mul (K0 * Cvv))
      let : TopologicalSpace.PseudoMetrizableSpace
          ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) := by
        let m : PseudoMetricSpace ((ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) := inferInstance
        exact ⟨⟨m.toUniformSpace, rfl, inferInstance⟩⟩
      have hmeas0 (q : ℝ × ℝ) : Measurable (barrierConvolutionIntegrand κ phi q) :=
        (hκ.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
          (hψ.measurable.comp (measurable_id.prodMk measurable_const))
      have hmeas1 q := (barrierConvolutionJets_measurable κ hκ q).1
      have hmeas2 q := (barrierConvolutionJets_measurable κ hκ q).2
      have hae : ∀ᵐ Y ∂mu, Y ∈ K ∧ Y ≠ 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae (volume.ae_ne 0)] with Y hY hn
        exact ⟨hY, hn⟩
      have hs2 : ContDiffOn ℝ 2 (fun q => ∫ Y, barrierConvolutionIntegrand κ phi q Y ∂mu) U ∧
          (∀ q ∈ U, HasFDerivAt (fun p => ∫ Y, barrierConvolutionIntegrand κ phi p Y ∂mu)
            (∫ Y, barrierConvolutionJet κ phi q Y ∂mu) q) ∧
          (∀ q ∈ U, HasFDerivAt (fun p => ∫ Y, barrierConvolutionJet κ phi p Y ∂mu)
            (∫ Y, barrierConvolutionSecondJet κ phi q Y ∂mu) q) := by
        apply singular_parameter_integral_contDiffOn_two mu Metric.isOpen_ball
          (barrierConvolutionIntegrand κ phi) (barrierConvolutionJet κ phi)
          (barrierConvolutionSecondJet κ phi) b0 b1 b2 hb0 hb1 hb2
          (fun q _ => (hmeas0 q).aestronglyMeasurable)
          (fun q _ => (hmeas1 q).aestronglyMeasurable)
          (fun q _ => (hmeas2 q).aestronglyMeasurable)
        · filter_upwards [hae] with Y hY
          intro q hq
          rw [barrierConvolutionIntegrand, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hbκ0 _) (hbphi q hq Y hY.1) (abs_nonneg _) hK0
        · filter_upwards [hae] with Y hY
          intro q hq
          have hvb := barrier_position_fiber_bound (alpha - 1) (by linarith) _ Cv hCv hbv
            Y q.2 hY.2
          apply (barrierConvolutionJet_norm_le κ phi q Y).trans
          dsimp only [b1, p1]
          calc
            _ ≤ K1 * B + K0 * (Cv * |Y| ^ ((alpha - 1) / 3)) := by
              gcongr
              all_goals first
              | exact hbκ1 _
              | exact hbphi q hq Y hY.1
              | exact hbκ0 _
            _ = _ := by ring
        · filter_upwards [hae] with Y hY
          intro q hq
          have hvb := barrier_position_fiber_bound (alpha - 1) (by linarith) _ Cv hCv hbv
            Y q.2 hY.2
          have hvvb := barrier_position_fiber_bound (alpha - 2) (by linarith) _ Cvv hCvv hbvv
            Y q.2 hY.2
          apply (barrierConvolutionSecondJet_norm_le κ phi q Y).trans
          dsimp only [b2, p1, p2]
          calc
            _ ≤ K2 * B + 2 * K1 * (Cv * |Y| ^ ((alpha - 1) / 3)) +
                K0 * (Cvv * |Y| ^ ((alpha - 2) / 3)) := by
              gcongr
              all_goals first
              | exact hbκ2 _
              | exact hbphi q hq Y hY.1
              | exact hbκ1 _
              | exact hvb
              | exact hbκ0 _
            _ = _ := by ring
        · filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with Y hY
          intro q _
          exact barrierConvolutionIntegrand_hasFDerivAt κ hκ q Y hY
        · filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with Y hY
          intro q _
          exact barrierConvolutionJet_hasFDerivAt κ hκ q Y hY
        · filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with Y hY
          exact (barrierConvolutionSecondJet_continuous κ hκ Y hY).continuousOn
      have he : positionBarrierConvolution κ phi =ᶠ[𝓝 q0]
          fun q => ∫ Y, barrierConvolutionIntegrand κ phi q Y ∂mu := by
        filter_upwards [Metric.ball_mem_nhds q0 (by norm_num : (0 : ℝ) < 1)] with q hq
        apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
        intro Y hY
        rw [barrierConvolutionIntegrand, (hwindow q hq Y hY).1, zero_mul]
      have hq0 : q0 ∈ U := Metric.mem_ball_self (by norm_num)
      have he1 : (fun q => ∫ Y, barrierConvolutionJet κ phi q Y) =ᶠ[𝓝 q0]
          fun q => ∫ Y, barrierConvolutionJet κ phi q Y ∂mu := by
        filter_upwards [Metric.ball_mem_nhds q0 (by norm_num : (0 : ℝ) < 1)] with q hq
        apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
        intro Y hY
        obtain ⟨h0, h1, _⟩ := hwindow q hq Y hY
        simp [barrierConvolutionJet, h0, h1]
      have he2 : (∫ Y, barrierConvolutionSecondJet κ phi q0 Y) =
          ∫ Y, barrierConvolutionSecondJet κ phi q0 Y ∂mu := by
        apply (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) ?_).symm
        intro Y hY
        obtain ⟨h0, h1, h2⟩ := hwindow q0 hq0 Y hY
        simp [barrierConvolutionSecondJet, h0, h1, h2, ContinuousLinearMap.zero_smulRight]
        apply ContinuousLinearMap.ext
        intro w
        apply ContinuousLinearMap.ext
        intro u
        simp [add_apply, zero_apply]
      have hcd := (hs2.1 q0 hq0).contDiffAt (Metric.ball_mem_nhds q0 (by norm_num))
      refine ⟨hcd.congr_of_eventuallyEq he, ?_, ?_⟩
      · rw [he1.eq_of_nhds]
        exact (hs2.2.1 q0 hq0).congr_of_eventuallyEq he
      · rw [he2]
        exact (hs2.2.2 q0 hq0).congr_of_eventuallyEq he1
    rw [contDiff_iff_contDiffAt]
    exact fun q => (positionBarrierConvolution_jet_spec κ hκ hs q).1
  rw [positionConvolution_barrier_eq]
  exact positionBarrierConvolution_contDiff eta
    (heta.1.of_le (by simp)) heta.2.1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

end

