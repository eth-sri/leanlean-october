module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo TheoremA Evolution Set MeasureTheory
open scoped ENNReal

/-- An exponential plane depending only on time and physical velocity. -/
def reconstructionExponentialPlane (alpha beta gamma : ℝ) (p : Point) : ℝ :=
  Real.exp (alpha * p.time + beta * p.velocity 0 + gamma)

/-- The exponential plane is smooth in the prescribed packed physical coordinates. -/
theorem reconstructionExponentialPlane_smooth (alpha beta gamma : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (reconstructionExponentialPlane alpha beta gamma ∘ reconstructionPhysicalHomeomorph) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (Evolution.timeCoord 1) :=
    (Evolution.timeCoord 1).contDiff
  exact ((contDiff_const.mul ht).add
    (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).comp
      (diffusedCoord 1).contDiff)) |>.add contDiff_const).exp

private theorem exponentialPlane_second_deriv (c beta : ℝ) (v : ℝ) :
    deriv (deriv (fun w => Real.exp (c + beta * w))) v =
      beta ^ 2 * Real.exp (c + beta * v) := by
  have hd (w : ℝ) : HasDerivAt (fun w => Real.exp (c + beta * w))
      (Real.exp (c + beta * w) * beta) w :=
    by simpa using
      (((hasDerivAt_id w).const_mul beta).const_add c).exp
  rw [(funext (fun w => (hd w).deriv)), (hd v |>.mul_const beta).deriv]
  ring

/-- No coefficient derivative occurs in the exponential plane operator. -/
theorem reconstructionExponentialPlane_operator (a : ℝ → ℝ → ℝ)
    (alpha beta gamma : ℝ) (p : Point) :
    forwardScalarOperator a (reconstructionExponentialPlane alpha beta gamma) p =
      (alpha + a (p.position 0) (p.velocity 0) * beta ^ 2) *
        reconstructionExponentialPlane alpha beta gamma p := by
  have ht : kineticTimeDerivative (reconstructionExponentialPlane alpha beta gamma) p =
      alpha * reconstructionExponentialPlane alpha beta gamma p := by
    change deriv (fun t => Real.exp (alpha * t + beta * p.velocity 0 + gamma)) p.time = _
    simpa [reconstructionExponentialPlane, mul_comm] using
      ((((hasDerivAt_id p.time).const_mul alpha).add_const
        (beta * p.velocity 0)).add_const gamma).exp.deriv
  have hx : kineticPositionGradient (reconstructionExponentialPlane alpha beta gamma) p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    change deriv (fun _ => Real.exp (alpha * p.time + beta * p.velocity 0 + gamma))
      (p.position 0) = 0
    exact deriv_const _ _
  have hv : kineticVelocityHessian (reconstructionExponentialPlane alpha beta gamma) p 0 0 =
      beta ^ 2 * reconstructionExponentialPlane alpha beta gamma p := by
    rw [kineticVelocityHessian_scalar]
    have heq : (fun v => reconstructionExponentialPlane alpha beta gamma
        ⟨p.time, p.position, fun _ => v⟩) =
        fun v => Real.exp ((alpha * p.time + gamma) + beta * v) := by
      funext v
      dsimp only [reconstructionExponentialPlane]
      congr 1
      ring
    rw [heq, exponentialPlane_second_deriv]
    congr 2
    ring
  unfold forwardScalarOperator
  rw [ht, hx, hv]
  ring


/-- The actual exit measure satisfies the explicit two-face Gaussian early-exit bound. -/
theorem strip_exit_early_face_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : sMinus ≤ e.1.time) (theta : ℝ) (htheta : 0 < theta) :
    stripExitOfRealization hH hlam hLam A H E hE T e
      {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta} ≤
        ENNReal.ofReal (2 * Real.exp
          (-(min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) ^ 2 /
            (4 * Lam * theta)))  := by
  have reconstruction_early_face_exponential_bound (k : ℝ) (beta : ℝ) (face : ℝ) (d : ℝ) (_hk : 0 ≤ k) (hbeta : beta ^ 2 = k ^ 2) (hface : ∀ v ∈ Icc H.lo H.hi, beta * (v - face) ≤ 0) (hd : beta * (e.1.velocity 0 - face) ≤ -k * d) :
      stripExitOfRealization hH hlam hLam A H E hE T e
      {p | p.velocity 0 = face ∧ p.time ≤ sMinus + theta} ≤
        ENNReal.ofReal (Real.exp (Lam * k ^ 2 * theta - k * d)) := by
    have stripExitOfRealization_le_supersolution (phi : Point → ℝ) (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph)) (hb : ∃ M : ℝ, ∀ p, e.1.time ≤ p.time → p.time ≤ T →
        p.velocity 0 ∈ H.carrier → |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) (hop : ∀ p, e.1.time ≤ p.time → p ∈ stripPast H T →
        forwardScalarOperator A.a phi p ≤ 0) (hn : ∀ p, e.1.time ≤ p.time → p.time ≤ T →
        p.velocity 0 ∈ Icc H.lo H.hi → 0 ≤ phi p) (B : Set Point) (hB : MeasurableSet B) (hbd : ∀ p ∈ B, e.1.time ≤ p.time → p.time ≤ T →
        p.velocity 0 ∈ Icc H.lo H.hi → 1 ≤ phi p) :
        stripExitOfRealization hH hlam hLam A H E hE T e B ≤ ENNReal.ofReal (phi e.1) := by
      let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
      let Γ := stripGreenOfKernel H E.2 T e
      have hi := strip_identity_bounded_smooth_future_of_realization hH hlam hLam A H E hE T e
        phi hphi hb
      have hnonpos : (∫ p, forwardScalarOperator A.a phi p ∂Γ) ≤ 0 := by
        apply integral_nonpos_of_ae
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
          reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
        exact hop p ht.le hp
      have hΩ := stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e
      have hc := reconstruction_smooth_physical_continuous phi hphi
      obtain ⟨M, hM⟩ := hb
      have hint : Integrable phi Ω := by
        apply Integrable.mono' (integrable_const (max M 0)) hc.measurable.aestronglyMeasurable
        filter_upwards [hΩ] with p hp
        rw [Real.norm_eq_abs]
        exact (reconstruction_closed_velocity_slice_bound H phi hc M p hp.2.2
          (fun v hv => (hM ⟨p.time, p.position, fun _ => v⟩ hp.1 hp.2.1 hv).1)).trans
            (le_max_left _ _)
      have hnn : 0 ≤ᵐ[Ω] phi := by
        filter_upwards [hΩ] with p hp
        exact hn p hp.1 hp.2.1 hp.2.2
      calc Ω B = ∫⁻ p, B.indicator 1 p ∂Ω := (lintegral_indicator_one hB).symm
        _ ≤ ∫⁻ p, ENNReal.ofReal (phi p) ∂Ω := by
          apply lintegral_mono_ae
          filter_upwards [hΩ] with p hp
          by_cases hpb : p ∈ B
          · rw [indicator_of_mem hpb, Pi.one_apply]
            exact ENNReal.one_le_ofReal.mpr (hbd p hpb hp.1 hp.2.1 hp.2.2)
          · simp only [indicator_of_notMem hpb, zero_le]
        _ = ENNReal.ofReal (∫ p, phi p ∂Ω) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
        _ ≤ ENNReal.ofReal (phi e.1) := ENNReal.ofReal_le_ofReal (by
          change phi e.1 = (∫ p, phi p ∂Ω) - (∫ p, forwardScalarOperator A.a phi p ∂Γ) at hi
          linarith)
    let c := Lam * k ^ 2
    let b := sMinus + theta
    let phi := reconstructionExponentialPlane (-c) beta (c * b - beta * face)
    have hLam0 := hlam.trans_le hLam
    have hc := mul_nonneg hLam0.le (sq_nonneg k)
    have hp (p : Point) : phi p = Real.exp (c * (b - p.time) + beta * (p.velocity 0 - face)) := by
      dsimp only [phi, reconstructionExponentialPlane]
      congr 1
      ring
    have hpos (p : Point) : 0 < phi p := by rw [hp]; exact Real.exp_pos _
    have hop (p : Point) : forwardScalarOperator A.a phi p =
        (A.a (p.position 0) (p.velocity 0) - Lam) * k ^ 2 * phi p := by
      rw [reconstructionExponentialPlane_operator, hbeta]
      dsimp only [c]
      ring
    have hpn (p : Point) (ht : e.1.time ≤ p.time) (hv : p.velocity 0 ∈ Icc H.lo H.hi) :
        phi p ≤ Real.exp (c * theta) := by
      rw [hp]
      apply Real.exp_le_exp.mpr
      have hf := hface (p.velocity 0) hv
      have hh : b - p.time ≤ theta := by dsimp only [b]; linarith
      have hh' := mul_le_mul_of_nonneg_left hh hc
      linarith
    have hbound : ∃ M : ℝ, ∀ p, e.1.time ≤ p.time → p.time ≤ T →
        p.velocity 0 ∈ H.carrier → |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M := by
      refine ⟨(1 + c) * Real.exp (c * theta), fun p ht _ hv => ?_⟩
      have hv' : p.velocity 0 ∈ Icc H.lo H.hi := ⟨hv.1.le, hv.2.le⟩
      have hpb := hpn p ht hv'
      have ha := A.bounds (p.position 0) (p.velocity 0)
      have hpb0 := (hpos p).le
      constructor
      · rw [abs_of_nonneg hpb0]
        nlinarith [Real.exp_pos (c * theta)]
      · rw [hop, abs_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr ha.2),
          abs_of_nonneg (sq_nonneg k), abs_of_nonneg hpb0]
        have h1 : -(A.a (p.position 0) (p.velocity 0) - Lam) * k ^ 2 ≤ c := by
          dsimp only [c]
          nlinarith [sq_nonneg k]
        have hh := mul_le_mul h1 hpb hpb0 hc
        nlinarith [Real.exp_pos (c * theta)]
    have hB : MeasurableSet {p : Point | p.velocity 0 = face ∧ p.time ≤ b} :=
      (isClosed_eq ((continuous_apply 0).comp continuous_velocity)
        continuous_const).measurableSet.inter
        (isClosed_le continuous_time continuous_const).measurableSet
    have hmass := stripExitOfRealization_le_supersolution phi
      (reconstructionExponentialPlane_smooth _ _ _) hbound
      (fun p _ _ => by
        rw [hop]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (A.bounds _ _).2) (sq_nonneg k))
          (hpos p).le)
      (fun p _ _ _ => (hpos p).le) _ hB
      (fun p hp' _ _ _ => by
        rw [hp, hp'.1, sub_self, mul_zero, add_zero]
        exact Real.one_le_exp_iff.mpr (mul_nonneg hc (sub_nonneg.mpr hp'.2)))
    apply hmass.trans
    apply ENNReal.ofReal_le_ofReal
    rw [hp]
    apply Real.exp_le_exp.mpr
    have ht : b - e.1.time ≤ theta := by dsimp only [b]; linarith
    have hh := mul_le_mul_of_nonneg_left ht hc
    dsimp only [c] at hh ⊢
    linarith
  let d := min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)
  have hLam0 := hlam.trans_le hLam
  let k := d / (2 * Lam * theta)
  have hk : 0 < k := div_pos (lt_min (sub_pos.mpr e.2.2.1) (sub_pos.mpr e.2.2.2)) (by positivity)
  have hl := reconstruction_early_face_exponential_bound k (-k) H.lo d hk.le (by ring)
    (fun v hv => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le)
      (sub_nonneg.mpr hv.1))
    (by
      have hh := mul_le_mul_of_nonneg_left (min_le_left
        (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) hk.le
      change -k * (e.1.velocity 0 - H.lo) ≤ -k * d
      nlinarith)
  have hr := reconstruction_early_face_exponential_bound k k H.hi d hk.le rfl
    (fun v hv => mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hv.2))
    (by
      have hh := mul_le_mul_of_nonneg_left (min_le_right
        (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) hk.le
      change k * (e.1.velocity 0 - H.hi) ≤ -k * d
      nlinarith)
  have hfront (v : ℝ) (hv : v ∈ frontier H.carrier) : v = H.lo ∨ v = H.hi := by
    change v ∈ frontier (Ioo H.lo H.hi) at hv
    rw [frontier_Ioo H.ordered] at hv
    simpa using hv
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  have hsub : {p : Point | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta} ⊆
      {p | p.velocity 0 = H.lo ∧ p.time ≤ sMinus + theta} ∪
        {p | p.velocity 0 = H.hi ∧ p.time ≤ sMinus + theta} := by
    intro p hp
    rcases hfront _ hp.1 with hv | hv
    · exact Or.inl ⟨hv, hp.2⟩
    · exact Or.inr ⟨hv, hp.2⟩
  have hexp : Lam * k ^ 2 * theta - k * d = -d ^ 2 / (4 * Lam * theta) := by
    dsimp only [k]
    field_simp
    ring
  calc Ω {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta}
      ≤ Ω {p | p.velocity 0 = H.lo ∧ p.time ≤ sMinus + theta} +
        Ω {p | p.velocity 0 = H.hi ∧ p.time ≤ sMinus + theta} :=
          (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (Lam * k ^ 2 * theta - k * d)) +
        ENNReal.ofReal (Real.exp (Lam * k ^ 2 * theta - k * d)) := add_le_add hl hr
    _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, hexp, ← two_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

