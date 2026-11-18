module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenHorizon

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Real HypoellipticAleksandrov Parabolic SectionTwo TheoremA Evolution Set MeasureTheory Filter
open scoped Topology

/-- The source's cone probe has a uniform unit bound. -/
theorem reconstructionConeTransition_bound (x : ℝ) :
    0 ≤ expNegInvGlue x ∧ expNegInvGlue x ≤ 1 := by
  refine ⟨expNegInvGlue.nonneg x, ?_⟩
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact zero_le_one
  · rw [expNegInvGlue, ite_eq_right hx]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (not_le.mp hx).le))

/-- The exact derivative of the cone transition. -/
theorem reconstructionConeTransition_deriv (x : ℝ) :
    deriv expNegInvGlue x = x⁻¹ ^ 2 * expNegInvGlue x := by
  simpa using ((expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x).deriv)

/-- The derivative is bounded and strictly positive exactly on the positive axis. -/
theorem reconstructionConeTransition_deriv_bounds (x : ℝ) :
    0 ≤ deriv expNegInvGlue x ∧ deriv expNegInvGlue x ≤ 2 ∧
      (0 < x → 0 < deriv expNegInvGlue x) := by
  rw [reconstructionConeTransition_deriv]
  refine ⟨mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg x), ?_, ?_⟩
  · by_cases hx : x ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero]
      norm_num
    · have hx' : 0 < x := not_le.mp hx
      have hh := Real.pow_div_factorial_le_exp x⁻¹ (inv_pos.mpr hx').le 2
      norm_num only [Nat.factorial, Nat.cast_ofNat] at hh
      have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x⁻¹)).le
      rw [expNegInvGlue, ite_eq_right hx]
      have he : Real.exp x⁻¹ * Real.exp (-x⁻¹) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith
  · intro hx
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr hx)) (expNegInvGlue.pos_of_pos hx)


/-- The affine transport coordinate used to detect finite-speed violations. -/
def reconstructionConeCoordinate (alpha beta gamma : ℝ) (p : Point) : ℝ :=
  alpha * p.time + beta * p.position 0 + gamma

/-- Composition with the cone transition is a genuine globally smooth physical test. -/
theorem reconstructionConeProbe_smooth (alpha beta gamma : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) ((expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) ∘
      reconstructionPhysicalHomeomorph) := by
  apply expNegInvGlue.contDiff.comp
  exact ((contDiff_const.mul (Evolution.timeCoord 1).contDiff).add
    (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).comp
      (transportedCoord 1).contDiff))).add contDiff_const



/-- A nonpositive transport direction gives closed-cone support for both actual measures. -/
theorem reconstruction_transport_cone_ae
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (alpha beta gamma : ℝ)
    (he : reconstructionConeCoordinate alpha beta gamma e.1 = 0)
    (hdir : ∀ v ∈ H.carrier, alpha + v * beta ≤ 0) :
    (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      reconstructionConeCoordinate alpha beta gamma p ≤ 0) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e, reconstructionConeCoordinate alpha beta gamma p ≤ 0  := by
  have reconstruction_strict_transport_cone_ae (alpha : ℝ) (gamma : ℝ) (delta : ℝ) (hdelta : 0 < delta) (he : reconstructionConeCoordinate alpha beta gamma e.1 = 0) (hdir : ∀ v ∈ H.carrier, alpha + v * beta ≤ -delta) :
      (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      reconstructionConeCoordinate alpha beta gamma p ≤ 0) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e, reconstructionConeCoordinate alpha beta gamma p ≤ 0 := by
    have reconstructionConeProbe_operator (a : ℝ → ℝ → ℝ) (p : Point) :
        forwardScalarOperator a (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p =
        (alpha + p.velocity 0 * beta) *
          deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) := open Parabolic in by
      have hd (x : ℝ) :=
        ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).differentiable (by simp) x)
      have ht : kineticTimeDerivative
          (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p =
          deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) * alpha := by
        have hh := (hd _).hasDerivAt.comp p.time
          ((((hasDerivAt_id p.time).const_mul alpha).add_const (beta * p.position 0)).add_const gamma)
        simpa using! hh.deriv
      have hx : kineticPositionGradient
          (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p 0 =
          deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) * beta := by
        rw [kineticPositionGradient_scalar]
        have hh := (hd _).hasDerivAt.comp (p.position 0)
          ((((hasDerivAt_id (p.position 0)).const_mul beta).const_add (alpha * p.time)).add_const gamma)
        simpa using! hh.deriv
      have hv : kineticVelocityHessian
          (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p 0 0 = 0 := by
        rw [kineticVelocityHessian_scalar]
        change deriv (deriv (fun _ => expNegInvGlue
          (alpha * p.time + beta * p.position 0 + gamma))) (p.velocity 0) = 0
        have hh : deriv (fun _ : ℝ => expNegInvGlue
            (alpha * p.time + beta * p.position 0 + gamma)) = fun _ => 0 :=
          funext (fun x => deriv_const x _)
        rw [hh]
        exact deriv_const _ _
      unfold forwardScalarOperator
      rw [ht, hx, hv]
      ring
    let rho := reconstructionConeCoordinate alpha beta gamma
    let phi := expNegInvGlue ∘ rho
    let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
    let Γ := stripGreenOfKernel H E.2 T e
    let V := max |H.lo| |H.hi|
    let C := |alpha| + V * |beta|
    have hV : 0 ≤ V := (abs_nonneg H.lo).trans (le_max_left _ _)
    have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (mul_nonneg hV (abs_nonneg _))
    have hv (v : ℝ) (hv : v ∈ H.carrier) : |v| ≤ V := by
      apply abs_le.mpr
      exact ⟨((neg_le_neg (le_max_left |H.lo| |H.hi|)).trans (neg_abs_le H.lo)).trans hv.1.le,
        hv.2.le.trans ((le_abs_self H.hi).trans (le_max_right _ _))⟩
    have hop (p : Point) : forwardScalarOperator A.a phi p =
        (alpha + p.velocity 0 * beta) * deriv expNegInvGlue (rho p) :=
      reconstructionConeProbe_operator A.a p
    have hbd (p : Point) (hp : p.velocity 0 ∈ H.carrier) :
        |forwardScalarOperator A.a phi p| ≤ C * 2 := by
      rw [hop, abs_mul, abs_of_nonneg (reconstructionConeTransition_deriv_bounds _).1]
      apply mul_le_mul _ (reconstructionConeTransition_deriv_bounds _).2.1
        (reconstructionConeTransition_deriv_bounds _).1 hC
      exact (abs_add_le _ _).trans (add_le_add le_rfl (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hv _ hp) (abs_nonneg _)))
    have hi := strip_identity_bounded_smooth_of_realization hH hlam hLam A H E hE T e phi
      (reconstructionConeProbe_smooth alpha beta gamma) (by
        refine ⟨max 1 (C * 2), fun p hp => ?_⟩
        constructor
        · change |expNegInvGlue (rho p)| ≤ _
          rw [abs_of_nonneg (expNegInvGlue.nonneg _)]
          exact (reconstructionConeTransition_bound _).2.trans (le_max_left _ _)
        · exact (hbd p hp).trans (le_max_right _ _))
    have hpn : ∀ p, 0 ≤ phi p := fun p => expNegInvGlue.nonneg _
    have hint : Integrable phi Ω := by
      apply Integrable.mono' (integrable_const 1)
        ((reconstruction_smooth_physical_continuous phi
          (reconstructionConeProbe_smooth _ _ _)).measurable.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpn p)]
        exact (reconstructionConeTransition_bound _).2)
    have hkn : forwardScalarOperator A.a phi ≤ᵐ[Γ] 0 := by
      filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
      rw [hop]
      exact mul_nonpos_of_nonpos_of_nonneg ((hdir _ hp.2).trans (neg_nonpos.mpr hdelta.le))
        (reconstructionConeTransition_deriv_bounds _).1
    have hpos := integral_nonneg_of_ae (μ := Ω) (Filter.Eventually.of_forall hpn)
    have hneg := integral_nonpos_of_ae hkn
    have hzero : phi e.1 = 0 := by
      change expNegInvGlue (reconstructionConeCoordinate alpha beta gamma e.1) = 0
      rw [he]
      exact expNegInvGlue.zero
    change phi e.1 = (∫ p, phi p ∂Ω) - (∫ p, forwardScalarOperator A.a phi p ∂Γ) at hi
    rw [hzero] at hi
    have hφint : (∫ p, phi p ∂Ω) = 0 := by linarith
    have hkint : (∫ p, forwardScalarOperator A.a phi p ∂Γ) = 0 := by linarith
    constructor
    · have hz := (integral_eq_zero_iff_of_nonneg hpn hint).mp hφint
      filter_upwards [hz] with p hp
      exact expNegInvGlue.zero_iff_nonpos.mp hp
    · have hdc : Continuous (deriv expNegInvGlue) :=
        (expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).continuous_deriv (by simp)
      have hrho : Continuous rho :=
        ((continuous_const.mul continuous_time).add
          (continuous_const.mul ((continuous_apply 0).comp continuous_position))).add continuous_const
      have hmeas : AEStronglyMeasurable (forwardScalarOperator A.a phi) Γ := by
        have hc : Continuous (fun p => (alpha + p.velocity 0 * beta) *
            deriv expNegInvGlue (rho p)) := (((continuous_const.add
          (((continuous_apply 0).comp continuous_velocity).mul continuous_const)).mul
            (hdc.comp hrho)))
        exact hc.measurable.aestronglyMeasurable.congr
          (Filter.Eventually.of_forall (fun p => (hop p).symm))
      have hkintg : Integrable (forwardScalarOperator A.a phi) Γ := by
        apply Integrable.mono' (integrable_const (C * 2)) hmeas
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
        rw [Real.norm_eq_abs]
        exact hbd p hp.2
      have hz := (integral_eq_zero_iff_of_nonneg_ae (by
        filter_upwards [hkn] with p hp; exact neg_nonneg.mpr hp) hkintg.neg).mp
          (by
            change (∫ p, -forwardScalarOperator A.a phi p ∂Γ) = 0
            rw [integral_neg, hkint, neg_zero])
      filter_upwards [hz, stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp hs
      by_contra hposrho
      have hdr := (reconstructionConeTransition_deriv_bounds (rho p)).2.2 (not_le.mp hposrho)
      have hcoef := (hdir _ hs.2).trans_lt (neg_neg_of_pos hdelta)
      have hn := mul_neg_of_neg_of_pos hcoef hdr
      rw [← hop] at hn
      change -forwardScalarOperator A.a phi p = 0 at hp
      linarith
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hn (n : ℕ) := reconstruction_strict_transport_cone_ae
    (alpha - r n) (gamma + r n * e.1.time) (r n) (hr n)
    (by dsimp only [reconstructionConeCoordinate] at he ⊢; nlinarith)
    (fun v hv => by have hh := hdir v hv; linarith)
  have hlimit (μ : Measure Point)
      (ha : ∀ n, ∀ᵐ p ∂μ,
        reconstructionConeCoordinate (alpha - r n) beta (gamma + r n * e.1.time) p ≤ 0) :
      ∀ᵐ p ∂μ, reconstructionConeCoordinate alpha beta gamma p ≤ 0 := by
    filter_upwards [(ae_all_iff.mpr ha)] with p hp
    have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n => reconstructionConeCoordinate alpha beta gamma p -
        r n * p.time + r n * e.1.time) atTop
        (𝓝 (reconstructionConeCoordinate alpha beta gamma p)) := by
      simpa using
        (tendsto_const_nhds.sub (hr0.mul_const p.time)).add (hr0.mul_const e.1.time)
    have hρ : Tendsto (fun n => reconstructionConeCoordinate (alpha - r n) beta
        (gamma + r n * e.1.time) p) atTop
        (𝓝 (reconstructionConeCoordinate alpha beta gamma p)) := by
      apply ht.congr
      intro n
      dsimp only [reconstructionConeCoordinate]
      ring
    exact le_of_tendsto hρ (Filter.Eventually.of_forall hp)
  exact ⟨hlimit _ (fun n => (hn n).1), hlimit _ (fun n => (hn n).2)⟩



/-- The finite-horizon Green measure gives zero mass to violations of the physical cone. -/
theorem strip_cone_finite_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H E.2 T e
      {p | |p.position 0 - e.1.position 0| > max |H.lo| |H.hi| * (p.time - e.1.time)} = 0  := by
  have strip_cone_ae_of_realization :
      (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      |p.position 0 - e.1.position 0| ≤ max |H.lo| |H.hi| * (p.time - e.1.time)) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
      |p.position 0 - e.1.position 0| ≤ max |H.lo| |H.hi| * (p.time - e.1.time) := by
    let V := max |H.lo| |H.hi|
    have hr := reconstruction_transport_cone_ae hH hlam hLam A H E hE T e
      (-V) 1 (V * e.1.time - e.1.position 0)
      (by dsimp only [reconstructionConeCoordinate]; ring)
      (fun v hv => by
        have hh : v ≤ V := hv.2.le.trans ((le_abs_self H.hi).trans (le_max_right _ _))
        linarith)
    have hl := reconstruction_transport_cone_ae hH hlam hLam A H E hE T e
      (-V) (-1) (V * e.1.time + e.1.position 0)
      (by dsimp only [reconstructionConeCoordinate]; ring)
      (fun v hv => by
        have hh := ((neg_le_neg (le_max_left |H.lo| |H.hi|)).trans
          (neg_abs_le H.lo)).trans hv.1.le
        linarith)
    have hbound (p : Point)
        (hr : reconstructionConeCoordinate (-V) 1 (V * e.1.time - e.1.position 0) p ≤ 0)
        (hl : reconstructionConeCoordinate (-V) (-1) (V * e.1.time + e.1.position 0) p ≤ 0) :
        |p.position 0 - e.1.position 0| ≤ V * (p.time - e.1.time) := by
      dsimp only [reconstructionConeCoordinate] at hr hl
      apply abs_le.mpr
      constructor <;> nlinarith
    constructor
    · filter_upwards [hr.1, hl.1] with p hp hq
      exact hbound p hp hq
    · filter_upwards [hr.2, hl.2] with p hp hq
      exact hbound p hp hq
  have hh := (strip_cone_ae_of_realization).2
  rw [ae_iff] at hh
  simpa using hh


/-- Finite-horizon zero-set statements pass to the actual infinite-horizon Green measure. -/
theorem reconstruction_green_infinite_zero_of_finite
    (H : Interval) (E : StripEvolution H) (e : StripPole H ⊤)
    (B : Set Point) (hB : MeasurableSet B)
    (hz : ∀ T : ℝ, ∀ hT : e.1.time < T,
      stripGreenOfKernel H E.2 T ⟨e.1, WithTop.coe_lt_coe.mpr hT, e.2.2⟩ B = 0) :
    stripGreenOfKernel H E.2 ⊤ e B = 0 := by
  let t (n : ℕ) := e.1.time + (n : ℝ) + 1
  have ht (n : ℕ) : e.1.time < t n := by
    dsimp only [t]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzero (n : ℕ) : stripGreenOfKernel H E.2 ⊤ e (B ∩ {p | p.time < t n}) = 0 := by
    have hh := hz (t n) (ht n)
    rw [stripGreenOfKernel_horizonRestriction, Measure.restrict_apply hB] at hh
    exact hh
  have hcover : B = ⋃ n : ℕ, B ∩ {p | p.time < t n} := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
      apply mem_iUnion.mpr
      refine ⟨n, hp, ?_⟩
      change p.time < t n
      dsimp only [t]
      linarith
    · intro hp
      rcases mem_iUnion.mp hp with ⟨n, hn⟩
      exact hn.1
  rw [hcover]
  apply le_antisymm _ bot_le
  exact (measure_iUnion_le _).trans (by simp [hzero])


/-- The canonical Green measure obeys the same literal physical cone for every horizon. -/
theorem strip_cone
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ) (e : StripPole H T) :
    stripGreen hH hLE hlam hLam A H T e
      {p | |p.position 0 - e.1.position 0| > max |H.lo| |H.hi| * (p.time - e.1.time)} = 0  := by
  have strip_cone_of_realization (E : StripEvolution H) (hE : IsStripEvolution A H E) :
      stripGreenOfKernel H E.2 T e
      {p | |p.position 0 - e.1.position 0| > max |H.lo| |H.hi| * (p.time - e.1.time)} = 0 := by
    cases T with
    | coe T => exact strip_cone_finite_of_realization hH hlam hLam A H E hE T e
    | top =>
      apply reconstruction_green_infinite_zero_of_finite H E e
      · exact isOpen_lt
          ((continuous_const.mul (continuous_time.sub continuous_const)))
          ((((continuous_apply 0).comp continuous_position).sub continuous_const).abs)
            |>.measurableSet
      · intro T hT
        exact strip_cone_finite_of_realization hH hlam hLam A H E hE T _
  exact strip_cone_of_realization _
    (stripEvolution_spec hH hLE hlam hLam A H)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

