module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov Set MeasureTheory Filter HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology

/-- Quadratic velocity moment with its sharp diffusion correction. -/
def velocitySecondBarrier (Lam v0 tau : ℝ) (p : Point) : ℝ :=
  (p.velocity 0-v0)^2+2*Lam*(tau-p.time)

/-- Quadratic transported position moment with its integrated diffusion correction. -/
def positionSecondBarrier (Lam X0 tau : ℝ) (p : Point) : ℝ :=
  (p.position 0-X0+(tau-p.time)*p.velocity 0)^2+
    (2/3 : ℝ)*Lam*(tau-p.time)^3



/-- Exact quadratic velocity computation for the physical kinetic operator. -/
theorem velocitySecondBarrier_operator (a : ℝ → ℝ → ℝ) (Lam v0 tau : ℝ)
    (p : Point) :
    forwardScalarOperator a (velocitySecondBarrier Lam v0 tau) p =
      -2*(Lam-a (p.position 0) (p.velocity 0)) := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  have ht : deriv (fun s => velocitySecondBarrier Lam v0 tau
      ⟨s, p.position, p.velocity⟩) p.time = -2*Lam := by
    apply HasDerivAt.deriv
    convert (hasDerivAt_const p.time ((p.velocity 0-v0)^2)).add
      (((hasDerivAt_const p.time tau).sub (hasDerivAt_id p.time)).const_mul
        (2*Lam)) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hx : deriv (fun x => velocitySecondBarrier Lam v0 tau
      ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) = 0 := by
    change deriv (fun _ => (p.velocity 0-v0)^2+2*Lam*(tau-p.time)) _ = 0
    exact deriv_const _ _
  have hv : deriv (fun v => velocitySecondBarrier Lam v0 tau
      ⟨p.time, p.position, fun _ => v⟩) = fun v => 2*(v-v0) := by
    funext v
    apply HasDerivAt.deriv
    convert (((hasDerivAt_id v).sub_const v0).fun_pow 2).add_const
      (2*Lam*(tau-p.time)) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  rw [kineticTimeDerivative, ht, hx, hv]
  have hvv : deriv (fun v => 2*(v-v0)) (p.velocity 0) = 2 := by
    simpa using
      (((hasDerivAt_id (p.velocity 0)).sub_const v0).const_mul 2).deriv
  rw [hvv]
  ring

/-- Exact quadratic position computation; transport cancels the time derivative. -/
theorem positionSecondBarrier_operator (a : ℝ → ℝ → ℝ) (Lam X0 tau : ℝ)
    (p : Point) :
    forwardScalarOperator a (positionSecondBarrier Lam X0 tau) p =
      -2*(Lam-a (p.position 0) (p.velocity 0))*(tau-p.time)^2 := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  have ht : deriv (fun s => positionSecondBarrier Lam X0 tau
      ⟨s, p.position, p.velocity⟩) p.time =
      -2*(p.position 0-X0+(tau-p.time)*p.velocity 0)*p.velocity 0-
        2*Lam*(tau-p.time)^2 := by
    have hs := (hasDerivAt_const p.time tau).sub (hasDerivAt_id p.time)
    apply HasDerivAt.deriv
    convert ((hs.mul_const (p.velocity 0)).const_add (p.position 0-X0)).fun_pow 2 |>.add
      ((hs.fun_pow 3).const_mul ((2/3 : ℝ)*Lam)) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hx : deriv (fun x => positionSecondBarrier Lam X0 tau
      ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) =
      2*(p.position 0-X0+(tau-p.time)*p.velocity 0) := by
    apply HasDerivAt.deriv
    convert (((hasDerivAt_id (p.position 0)).sub_const X0).add_const
      ((tau-p.time)*p.velocity 0)).fun_pow 2 |>.add_const
        ((2/3 : ℝ)*Lam*(tau-p.time)^3) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hv : deriv (fun v => positionSecondBarrier Lam X0 tau
      ⟨p.time, p.position, fun _ => v⟩) =
      fun v => 2*(p.position 0-X0+(tau-p.time)*v)*(tau-p.time) := by
    funext v
    apply HasDerivAt.deriv
    convert (((hasDerivAt_id v).const_mul (tau-p.time)).const_add
      (p.position 0-X0)).fun_pow 2 |>.add_const
        ((2/3 : ℝ)*Lam*(tau-p.time)^3) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  have hvv : deriv (fun v => 2*(p.position 0-X0+(tau-p.time)*v)*(tau-p.time))
      (p.velocity 0) = 2*(tau-p.time)^2 := by
    apply HasDerivAt.deriv
    convert ((((hasDerivAt_id (p.velocity 0)).const_mul (tau-p.time)).const_add
      (p.position 0-X0)).const_mul 2).mul_const (tau-p.time) using 1 <;>
      ((try funext s); (try dsimp [velocitySecondBarrier, positionSecondBarrier]); all_goals ring)
  rw [kineticTimeDerivative, ht, hx, hv, hvv]
  ring

/-- The velocity polynomial is a supersolution under the pointwise upper bound. -/
theorem velocitySecondBarrier_operator_nonpos (a : ℝ → ℝ → ℝ)
    (Lam v0 tau : ℝ) (p : Point) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (velocitySecondBarrier Lam v0 tau) p ≤ 0 := by
  rw [velocitySecondBarrier_operator]
  nlinarith only [ha]

/-- The position polynomial is a supersolution under the same upper bound. -/
theorem positionSecondBarrier_operator_nonpos (a : ℝ → ℝ → ℝ)
    (Lam X0 tau : ℝ) (p : Point) (ha : a (p.position 0) (p.velocity 0) ≤ Lam) :
    forwardScalarOperator a (positionSecondBarrier Lam X0 tau) p ≤ 0 := by
  rw [positionSecondBarrier_operator]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

/-- Starting-point quadratic velocity value has the exact source constant. -/
theorem velocitySecondBarrier_start (Lam X0 v0 T : ℝ) :
    velocitySecondBarrier Lam v0 T ⟨0, fun _ => X0, fun _ => v0⟩ = 2*Lam*T := by
  simp [velocitySecondBarrier, zero_pow (by norm_num : 2 ≠ 0)]

/-- Starting-point quadratic position value has the integrated diffusion time power. -/
theorem positionSecondBarrier_start (Lam X0 v0 T : ℝ) :
    positionSecondBarrier Lam X0 T ⟨0, fun _ => X0, fun _ => v0⟩ =
      v0^2*T^2+(2/3 : ℝ)*Lam*T^3 := by
  simp [positionSecondBarrier]
  ring

/-- Velocity second-moment barrier is nonnegative on its terminal past. -/
theorem velocitySecondBarrier_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam)
    (v0 tau : ℝ) (p : Point) (ht : p.time ≤ tau) :
    0 ≤ velocitySecondBarrier Lam v0 tau p := by
  dsimp [velocitySecondBarrier]
  positivity

/-- Position second-moment barrier is nonnegative on the same past. -/
theorem positionSecondBarrier_nonneg {Lam : ℝ} (hLam : 0 ≤ Lam)
    (X0 tau : ℝ) (p : Point) (ht : p.time ≤ tau) :
    0 ≤ positionSecondBarrier Lam X0 tau p := by
  dsimp [positionSecondBarrier]
  positivity




/-- Raw smoothness supplies global continuity on the native point carrier. -/
theorem terminal_raw_continuous (W : Point → ℝ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (rawLift W)) : Continuous W := by
  exact hW.continuous.comp (KineticPoint.homeomorphProd 1).continuous_toFun

/-- Raw smoothness supplies all comparison slices. -/
theorem terminal_raw_regular (W : Point → ℝ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (rawLift W)) (p : Point) : IsSliceRegularAt W p := by
  apply IsSliceRegularAt.of_contDiffAt
  exact (hW.of_le (by norm_num)).contDiffAt




/-- Each fixed point eventually lies in the unit region of both coordinate cutoffs. -/
theorem conservationDatum_eventually_one (x : EvolutionAmbientState 1) :
    ∀ᶠ N : ℕ in atTop, conservationDatum N x = 1 := by
  have h1 : ∀ᶠ N : ℕ in atTop, ‖x.1‖ ≤ (N : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x.1‖).mono fun N h => by linarith
  have h2 : ∀ᶠ N : ℕ in atTop, ‖x.2‖ ≤ (N : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖x.2‖).mono fun N h => by linarith
  filter_upwards [h1, h2] with N hN1 hN2
  change zCutoffN 1 N x.1 * zCutoffN 1 N x.2 = 1
  rw [zCutoffN_eq_one hN1, zCutoffN_eq_one hN2, one_mul]


/-- Fatou transfers compact polynomial comparison to the unbounded terminal moment. -/
theorem terminal_polynomial_lintegral_le {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (g : EvolutionAmbientState 1 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg0 : ∀ x, 0 ≤ g x)
    (W : Point → ℝ) (hc : Continuous W) (hr : ∀ p, IsSliceRegularAt W p)
    (tau : ℝ) (hn : ∀ p, p.time ≤ tau → 0 ≤ W p)
    (hop : ∀ p, p.time ≤ tau →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) W p ≤ 0)
    (ht : ∀ p, p.time = tau → g (p.position, p.velocity) = W p)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) (hq : q.1.2.1 = tau) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂E.2.master q) ≤
      ENNReal.ofReal (W ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩)   := by
  let momentCutoff (N : ℕ) :
      BoundedBorel (EvolutionAmbientState 1) := by
    have hs := hg.mul (conservationDatum_smoothCompact N 0).1
    have hc : HasCompactSupport (fun x => g x * conservationDatum N x) :=
      (conservationDatum_smoothCompact N 0).2.1.mul_left
    refine ⟨fun x => g x * conservationDatum N x, hs.continuous.measurable, ?_⟩
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hs.continuous
    exact ⟨max C 0, le_max_right _ _, fun x =>
      (show |g x * conservationDatum N x| ≤ C from
        by simpa using hC x).trans (le_max_left _ _)⟩
  have momentCutoff_integral_le (N : ℕ) :
      ∫ x, momentCutoff N x ∂E.2.master q ≤
      W ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ := by
    have momentCutoff_smoothCompact :
        IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) tau
        (momentCutoff N) := by
      refine ⟨hg.mul (conservationDatum_smoothCompact N tau).1,
        (conservationDatum_smoothCompact N tau).2.1.mul_left, ?_⟩
      exact tsupport_mul_subset_right.trans (conservationDatum_smoothCompact N tau).2.2
    obtain ⟨u, hu, hrep, -⟩ := hE.1 tau (momentCutoff N)
      (momentCutoff_smoothCompact)
    let state : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
      ⟨q.1.2.2, q.2.2⟩
    have horder := hq ▸ q.2.1
    have he := integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
      q.1.1 tau horder state (momentCutoff N) (momentCutoff N).measurable
    have huq : u ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ =
        ∫ x, momentCutoff N x ∂E.2.master q := by
      have hquery : evolutionQueryOfState autonomousWholeDomain (fun _ => 0)
          q.1.1 tau horder state = q := by
        apply Subtype.ext
        change (q.1.1, tau, q.1.2.2) = q.1
        rw [← hq]
      rw [hquery] at he
      exact (hrep q.1.1 horder state).trans ((hE.2.1 q.1.1 tau horder state (terminalStateDatum (momentCutoff N))).trans he.symm)
    rw [← huq]
    apply terminal_polynomial_comparison hlam A tau _ u W hu hc hr hn hop
      (fun p hp => ?_) _ horder
    change g (p.position, p.velocity) * conservationDatum N (p.position, p.velocity) ≤ W p
    rw [ht p hp]
    exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N _).2 (hn p hp.le)).trans
      (by rw [mul_one])
  let f := fun N x => ENNReal.ofReal (momentCutoff N x)
  have hlim (x) : liminf (fun N => f N x) atTop = ENNReal.ofReal (g x) := by
    have he : (fun N => f N x) =ᶠ[atTop] fun _ => ENNReal.ofReal (g x) := by
      filter_upwards [conservationDatum_eventually_one x] with N hN
      change ENNReal.ofReal (g x * conservationDatum N x) = _
      rw [hN, mul_one]
    rw [Filter.liminf_congr he, liminf_const]
  rw [← lintegral_congr hlim]
  apply (lintegral_liminf_le (fun N => (momentCutoff N).measurable.ennreal_ofReal)).trans
  refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
  apply (Filter.Eventually.of_forall (fun N => ?_)).frequently
  let : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  have hfi : Integrable (momentCutoff N) (E.2.master q) :=
    boundedBorel_integrable (momentCutoff N) _
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall
    (fun x => by
      change 0 ≤ g x * conservationDatum N x
      exact mul_nonneg (hg0 x) (conservationDatum_bounds N x).1))]
  exact ENNReal.ofReal_le_ofReal (momentCutoff_integral_le N)


/-- The actual velocity terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_velocity_2_moment {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*Lam*(T : ℝ))   := by
  have velocitySecondBarrier_raw_smooth (v0 : ℝ) :
      ContDiff ℝ (⊤ : ℕ∞) (rawLift (velocitySecondBarrier Lam v0 T ∘ terminalPhysicalPoint)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
      (q.2.1 0-v0)^2+2*Lam*(T-q.1))
    fun_prop
  have velocitySecondBarrier_terminal (v0 : ℝ) (p : Point) :
      velocitySecondBarrier Lam v0 p.time p = (p.velocity 0-v0)^2 := by
    simp [velocitySecondBarrier]
  let W := velocitySecondBarrier Lam z.2 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.1 0-z.2)^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw := velocitySecondBarrier_raw_smooth z.2
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => sq_nonneg _) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => velocitySecondBarrier_nonneg ((hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2) z.2 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact velocitySecondBarrier_operator_nonpos A.a Lam z.2 T (terminalPhysicalPoint p)
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (velocitySecondBarrier_terminal z.2 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint, nativeToXV, velocitySecondBarrier_start] using h

/-- The actual position terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_position_2_moment {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (z.2^2*(T : ℝ)^2+(2/3 : ℝ)*Lam*(T : ℝ)^3)   := by
  have positionSecondBarrier_raw_smooth (X0 : ℝ) :
      ContDiff ℝ (⊤ : ℕ∞) (rawLift (positionSecondBarrier Lam X0 T ∘ terminalPhysicalPoint)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
      (q.2.2 0-X0+(T-q.1)*q.2.1 0)^2+(2/3:ℝ)*Lam*(T-q.1)^3)
    fun_prop
  have positionSecondBarrier_terminal (X0 : ℝ) (p : Point) :
      positionSecondBarrier Lam X0 p.time p = (p.position 0-X0)^2 := by
    simp [positionSecondBarrier, zero_pow
      (by norm_num : 3 ≠ 0)]
  let W := positionSecondBarrier Lam z.1 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.2 0-z.1)^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw := positionSecondBarrier_raw_smooth z.1
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => sq_nonneg _) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => positionSecondBarrier_nonneg ((hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2) z.1 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact positionSecondBarrier_operator_nonpos A.a Lam z.1 T (terminalPhysicalPoint p)
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (positionSecondBarrier_terminal z.1 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint, nativeToXV, positionSecondBarrier_start] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

