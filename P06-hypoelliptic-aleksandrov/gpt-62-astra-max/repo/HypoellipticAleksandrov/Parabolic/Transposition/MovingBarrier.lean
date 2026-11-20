module
public import HypoellipticAleksandrov.Parabolic.Transposition.KineticFields
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonMoving
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidBarrier
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveMollification
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib

/-! # A supersolution envelope on a Lipschitz moving ball

Translate the universal elliptic profile to the moving centre. On a finite slab approximate
the centre by smooth curves with the same Lipschitz bound. The speed enters only as a
bounded drift; adding a vanishing constant restores nonnegativity throughout the true ball.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity KineticAleksandrov KineticAleksandrov.Evolution Lieberman Set Metric
open scoped ContDiff Matrix MatrixOrder Matrix.Norms.Elementwise Topology
variable {n : ℕ}

private def shiftProfile (q : PDE.Vec n → ℝ) (c : ℝ → PDE.Vec n) (δ : ℝ) (p : KineticPoint n) := q (p.position - c p.time) + δ

private theorem shift_op {q : PDE.Vec n → ℝ} (hq : ContDiff ℝ ∞ q) {c : ℝ → PDE.Vec n} (hc : ContDiff ℝ ∞ c)
    (δ : ℝ) (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (p : KineticPoint n) :
    transportedForwardOperator B b (shiftProfile q c δ) p =
      scalarParabolicZeroOrderOperator (fun _ _ => fullKineticCoefficientAt B p) (fun _ _ => -deriv c p.time)
        (fun _ _ => 0) (fun z => q z.2) (p.time, p.position-c p.time) := by
  let y := p.position - c p.time
  have ht := (((hq.differentiable (by simp) y).hasFDerivAt.comp_hasDerivAt p.time
    ((hasDerivAt_const p.time p.position).sub ((hc.differentiable (by simp) _).hasDerivAt))).add_const δ).deriv
  change deriv (fun t => q (p.position - c t) + δ) p.time = fderiv ℝ q y (0 - deriv c p.time) at ht
  have t : kineticTimeDerivative (shiftProfile q c δ) p = PDE.vecDot (-deriv c p.time) (PDE.classicalGradient q y) := by
    simp only [kineticTimeDerivative,shiftProfile]; change deriv (fun t => q (p.position - c t) + δ) p.time = _
    rw [ht,zero_sub,PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues]; exact Finset.sum_congr rfl (fun _ _ => mul_comm ..)
  have g (v) : kineticPositionGradient (shiftProfile q c δ) ⟨p.time,v,p.velocity⟩ = PDE.classicalGradient q (v-c p.time) := by
    ext i; simp [kineticPositionGradient,PDE.classicalGradient,shiftProfile,fderiv_comp_sub]
  have H : diffusedHessian (shiftProfile q c δ) p = scalarSpatialHessian (fun z => q z.2) (p.time,y) := by
    unfold diffusedHessian scalarSpatialHessian; simp only [g, fderiv_comp_sub]; rfl
  have Z : kineticVelocityGradient (shiftProfile q c δ) p = 0 := by ext i; simp [kineticVelocityGradient,PDE.classicalGradient,shiftProfile]
  simp [transportedForwardOperator_apply,scalarParabolicZeroOrderOperator_apply,t,H,Z,y,scalarTimeDerivative,scalarSpatialGradient,PDE.vecDot,add_comm]

private theorem radial_profile (hd : 0 < n) {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam) (M L : ℝ) (hM : 0 ≤ M) :
    ∃ q : PDE.Vec n → ℝ, ContDiff ℝ ∞ q ∧ (∀ y, PDE.vecNormSq y ≤ r^2 → 0 ≤ q y) ∧
      (∀ y, PDE.vecNormSq y = r^2 → q y = 0) ∧
      ∀ (c : ℝ → PDE.Vec n), ContDiff ℝ ∞ c → ∀ δ (B : FullKineticCoefficient n) b (p : KineticPoint n),
        lam • (1 : PDE.Mat n) ≤ fullKineticCoefficientAt B p → PDE.vecEuclideanNorm (deriv c p.time) ≤ L →
        transportedForwardOperator B b (shiftProfile q c δ) p ≤ -M := by
  let Q : PDE.Mat n := (r^2)⁻¹ • (1 : PDE.Mat n)
  have pdQ : Q.PosDef := Matrix.PosDef.one.smul (by positivity : 0 < (r^2)⁻¹)
  obtain ⟨q,hq,hn,hz,hL⟩ := universal_ellipsoid_barrier hd pdQ lam M L hlam hM
  have quad y : PDE.vecDot y (Q *ᵥ y) = PDE.vecNormSq y / r^2 := by
    simp [Q, Matrix.smul_mulVec,PDE.vecDot,PDE.vecNormSq,Finset.mul_sum,div_eq_inv_mul,mul_left_comm]
  refine ⟨q,hq,fun y hy => hn y (by rwa [quad,div_le_one (by positivity)]),fun y hy => hz y (by rw [quad,hy,div_self (by positivity)]),?_⟩
  intro c hc δ B b p hl hp; rw [shift_op hq hc]; exact hL _ _ _ hl (by simpa [PDE.vecEuclideanNorm_neg] using hp)

/-- Boundary data needed by the transposed finite-slab problem. -/
def LateralBarrier (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (a T M : ℝ)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (g : KineticPoint n → ℝ) : Prop :=
  Continuous g ∧ (∀ p ∈ movingActiveSlab Ω γ a T, 0 ≤ g p) ∧
    (∀ p : KineticPoint n, p.position ∈ frontier (movingDomain Ω γ p.time) → g p = 0) ∧
    ∀ ε > (0 : ℝ), ∃ G : KineticPoint n → ℝ, Sm (G ∘ world n) ∧
      ∀ p ∈ movingActiveSlab Ω γ a T, 0 ≤ G p ∧ transportedForwardOperator B b G p ≤ -M ∧ G p ≤ g p + ε

theorem ball_lateral_barrier (hd : 0 < n) (c : PDE.Vec n) {r lam Lam a T M : ℝ}
    (hr : 0 < r) (hT : a < T) (hlam : 0 < lam) (hM : 0 ≤ M) {γ : ℝ → PDE.Vec n}
    (hγ : IsContinuousPiecewiseC1 γ) {B : FullKineticCoefficient n} (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec n → PDE.Vec n) : ∃ g, LateralBarrier (PDE.euclideanBall c r) γ a T M B b g := by
  obtain ⟨L,hL,hγL⟩ := exists_evolution_curve_lipschitzOn hγ a T hT
  obtain ⟨q,hq,hn,hz,hqop⟩ := radial_profile hd hr hlam M (Real.sqrt n * L) hM
  let gap (g : ℝ → PDE.Vec n) (p : KineticPoint n) := p.position - (g p.time + c)
  let g (p : KineticPoint n) := q (gap γ p)
  refine ⟨g, hq.continuous.comp (continuous_position.sub ((hγ.1.comp continuous_time).add continuous_const)),
    fun p hp => hn _ (mem_movingDomain_euclideanBall_iff.mp hp.2.2).le, fun p hp => hz _ (vecNormSq_eq_of_mem_frontier_movingDomain hp), ?_⟩
  intro ε hε
  let K := closedBall (0 : PDE.Vec n) (r+1)
  obtain ⟨δ,hδ,hu⟩ := Metric.uniformContinuousOn_iff.mp (show UniformContinuousOn q K from (isCompact_closedBall _ _).uniformContinuousOn_of_continuous hq.continuous.continuousOn) (ε/2) (half_pos hε)
  let η := min 1 (δ/2)
  have hη : 0 < η := lt_min one_pos (half_pos hδ)
  obtain ⟨s,hs,hsL,hclose⟩ := exists_smooth_lipschitz_approx (continuous_slabExtension hγ.1 a T) hL (slabExtension_lipschitz hT.le hL hγL) hη
  have lip : LipschitzWith ⟨L,hL⟩ s := LipschitzWith.of_dist_le_mul fun x y =>
    (PDE.norm_le_vecEuclideanNorm (s x-s y)).trans (hsL x y)
  let center t := s t + c
  refine ⟨shiftProfile q center (ε/2), ?_, ?_⟩
  · change ContDiff ℝ ∞ ((fun z : ℝ × (PDE.Vec n × PDE.Vec n) => q (z.2.1-center z.1) + ε/2) ∘ split n)
    exact ((hq.comp (contDiff_snd.fst.sub ((hs.comp contDiff_fst).add contDiff_const))).add contDiff_const).comp (split n).contDiff
  intro p hp
  have htime : p.time ∈ Icc a T := ⟨hp.1,hp.2.1.le⟩
  have he := hclose p.time
  rw [slabExtension_eq γ htime] at he
  have close : dist (gap s p) (gap γ p) ≤ η := by
    rw [dist_eq_norm]; change ‖(p.position - (s p.time+c)) - (p.position - (γ p.time+c))‖ ≤ _
    rw [show (p.position - (s p.time+c)) - (p.position - (γ p.time+c)) = -(s p.time-γ p.time) by abel, norm_neg]
    exact (PDE.norm_le_vecEuclideanNorm _).trans he
  have ng : ‖gap γ p‖ < r := (PDE.norm_le_vecEuclideanNorm _).trans_lt (mem_movingDomain_euclideanBall_iff_norm_lt hr |>.mp hp.2.2)
  have ds := dist_triangle (gap s p) (gap γ p) 0
  simp only [dist_zero_right] at ds
  have near := hu _ (show gap s p ∈ K from by simp only [K,mem_closedBall,dist_zero_right]; linarith [min_le_left 1 (δ/2)])
    _ (show gap γ p ∈ K from by simp only [K,mem_closedBall,dist_zero_right]; linarith)
    (show dist (gap s p) (gap γ p) < δ from close.trans_lt ((min_le_right ..).trans_lt (half_lt_self hδ)))
  rw [Real.dist_eq, abs_lt] at near
  change 0 ≤ q (gap s p) + ε/2 ∧ _ ∧ q (gap s p) + ε/2 ≤ q (gap γ p) + ε
  have h0 := hn _ (mem_movingDomain_euclideanBall_iff.mp hp.2.2).le
  refine ⟨by dsimp [gap] at *; linarith, hqop center (hs.add contDiff_const) _ _ _ p (hell _ _ _).1 ?_,by linarith⟩
  rw [show deriv center p.time = deriv s p.time from deriv_add_const _]
  exact (PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _).trans (mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz lip) (Real.sqrt_nonneg _))

end HypoellipticAleksandrov.Parabolic.Transposition
