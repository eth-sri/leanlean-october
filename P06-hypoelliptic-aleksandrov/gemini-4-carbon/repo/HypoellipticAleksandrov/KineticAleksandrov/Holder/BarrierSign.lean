module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.QuadraticCalculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffJets
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import PDEFoundation.Ambient.HilbertVec
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovariancePhysical
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierVelocity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Analysis.Calculus.FDeriv.Const

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Parabolic Scaling Filter Set Matrix MeasureTheory
open scoped Topology BigOperators MatrixOrder

/-- A source-compatible cutoff, zero through `-1/128` and one from zero onward. -/
def barrierCutoff (theta : ℝ) : ℝ := Real.smoothTransition (128 * theta + 1)

/-- The internally chosen barrier cutoff is infinitely differentiable. -/
theorem contDiff_barrierCutoff : ContDiff ℝ (⊤ : ℕ∞) barrierCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.add contDiff_const)

/-- The barrier cutoff has values in the closed unit interval. -/
theorem barrierCutoff_bounds (theta : ℝ) : 0 ≤ barrierCutoff theta ∧ barrierCutoff theta ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The barrier cutoff vanishes throughout the left cutoff region. -/
theorem barrierCutoff_zero {theta : ℝ} (htheta : theta ≤ -(1 / 128 : ℝ)) :
    barrierCutoff theta = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [htheta])

/-- The barrier cutoff is exactly one on all nonnegative times. -/
theorem barrierCutoff_one {theta : ℝ} (htheta : 0 ≤ theta) : barrierCutoff theta = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [htheta])

/-- The source damping coefficient, fixed before the block and amplitude. -/
def Xi (d : ℕ) (lam Lam H h : ℝ) : ℝ :=
  2 * Lam * (128 * (d : ℝ) / lam) / h + 2 * H ^ 2 / (3 * lam)

/-- The raw quadratic form is smooth at every point of the positive-definite strip. -/
theorem contDiffAt_qform_raw {d : ℕ} {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hs : -(h / 128) ≤ s) (y V : PDE.Vec d) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun Q : ℝ × (PDE.Vec d × PDE.Vec d) => qform lam h Q.1 Q.2.1 Q.2.2)
      (s, (y, V)) := by
  have heq : (fun Q : ℝ × (PDE.Vec d × PDE.Vec d) =>
      qform lam h Q.1 Q.2.1 Q.2.2) =
      (fun Q => (covarianceVV lam h Q.1 * PDE.vecDot Q.2.1 Q.2.1 -
        2 * covarianceXV lam h Q.1 * PDE.vecDot Q.2.1 Q.2.2 +
        covarianceXX lam h Q.1 * PDE.vecDot Q.2.2 Q.2.2) / covarianceDet lam h Q.1) := by
    funext Q
    exact qform_eq_scalar lam hh _ _ _
  rw [heq]
  apply ContDiffAt.div
  · unfold covarianceVV covarianceXV covarianceXX PDE.vecDot
    fun_prop
  · unfold covarianceDet covarianceVV covarianceXV covarianceXX
    fun_prop
  · exact (covarianceDet_pos hlam hh hs).ne'



/-- Source moving-frame coordinates, without any change of velocity normalization. -/
def movingCoordinates {d : ℕ} (tminus : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (P.time - tminus, (P.position - x (P.time - tminus),
    P.velocity - v (P.time - tminus)))

/-- The literal scalar function in moving coordinates. -/
def movingLift {d : ℕ} (f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ)
    (tminus : ℝ) (x v : ℝ → PDE.Vec d) (P : KineticPoint d) : ℝ :=
  f (movingCoordinates tminus x v P)



/-- The moving-frame transport identity, before the velocity Hessian is subtracted. -/
theorem movingLift_transport {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} {x v : ℝ → PDE.Vec d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (tminus : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (movingLift f tminus x v) P +
      PDE.vecDot P.velocity (kineticPositionGradient (movingLift f tminus x v) P) =
    fderiv ℝ f (movingCoordinates tminus x v P)
      (1, (P.velocity - v (P.time - tminus), 0)) -
    fderiv ℝ f (movingCoordinates tminus x v P)
      (0, (0, deriv v (P.time - tminus)))   := by
  have hasDerivAt_movingCoordinates_transport (hx : HasDerivAt x (v (P.time - tminus)) (P.time - tminus)) (hv : DifferentiableAt ℝ v (P.time - tminus)) :
      HasDerivAt (fun r : ℝ => movingCoordinates tminus x v
      ⟨P.time + r, P.position + r • P.velocity, P.velocity⟩)
      (1, (P.velocity - v (P.time - tminus), -deriv v (P.time - tminus))) 0 := by
    have ht : HasDerivAt (fun r : ℝ => P.time + r - tminus) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add P.time).sub_const tminus
    have hx' : HasDerivAt x (v (P.time - tminus)) (P.time + 0 - tminus) := by
      simpa only [add_zero] using hx
    have hxc := hx'.scomp 0 ht
    have hv' : HasDerivAt v (deriv v (P.time - tminus)) (P.time + 0 - tminus) := by
      simpa only [add_zero] using hv.hasDerivAt
    have hvc := hv'.scomp 0 ht
    have hpos : HasDerivAt (fun r : ℝ => P.position + r • P.velocity) P.velocity 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const P.velocity).const_add P.position
    simpa only [movingCoordinates, Pi.sub_apply, Function.comp_def, mul_one, one_smul,
      zero_add, add_zero, zero_sub] using
      ht.prodMk ((hpos.sub hxc).prodMk ((hasDerivAt_const 0 P.velocity).sub hvc))
  have contDiff_movingCoordinates :
      ContDiff ℝ (⊤ : ℕ∞) (fun Q : ℝ × (PDE.Vec d × PDE.Vec d) =>
      movingCoordinates tminus x v ⟨Q.1, Q.2.1, Q.2.2⟩) := by
    unfold movingCoordinates
    exact (contDiff_fst.sub contDiff_const).prodMk
      ((contDiff_fst.comp contDiff_snd).sub
        (hx.comp (contDiff_fst.sub contDiff_const)) |>.prodMk
        ((contDiff_snd.comp contDiff_snd).sub
          (hv.comp (contDiff_fst.sub contDiff_const))))
  have hcomp := hf.comp (contDiff_movingCoordinates)
  have hd : DifferentiableAt ℝ (rawLift (movingLift f tminus x v)) (rawPoint P) :=
    hcomp.differentiable (by norm_num) _
  have hcurve := hasDerivAt_movingCoordinates_transport
    (hkin _) (hv.differentiable (by norm_num) _)
  have hder := (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have htransport := hasDerivAt_kinetic_transport hd
  have heq := htransport.unique hder
  simp only [add_zero, zero_smul] at heq
  rw [heq]
  rw [← map_sub]
  congr 1
  ext <;> simp



/-- The literal Gaussian formula, used analytically only on the definite covariance strip. -/
def gaussianFormula {d : ℕ} (chi : ℝ → ℝ)
    (lam Lam H h L ell tminus sblock : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) : ℝ :=
  let s := P.time - tminus
  let sigma := s - sblock
  ell * chi (sigma / h) *
    (Real.exp (-Xi d lam Lam H h * sigma -
      qform lam h sigma (P.position - x s) (P.velocity - v s)) - Real.exp (-L ^ 2))

/-- The source barrier, extended by zero from the positive-definite cutoff strip. -/
def gaussianBarrier {d : ℕ} (lam Lam H h L ell tminus sblock : ℝ)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d) : ℝ :=
  if -(1 / 128 : ℝ) < (P.time - tminus - sblock) / h then
    gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v P
  else 0

/-- Outside the covariance strip the source cutoff kills the entire formula. -/
theorem gaussianBarrier_eq_formula {d : ℕ} (lam Lam H h L ell tminus sblock : ℝ)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d) :
    gaussianBarrier lam Lam H h L ell tminus sblock x v P =
      gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v P := by
  unfold gaussianBarrier
  split_ifs with hs
  · rfl
  · unfold gaussianFormula
    dsimp only
    rw [barrierCutoff_zero (le_of_not_gt hs), mul_zero, zero_mul]

/-- Smoothness of the literal formula at each point of the closed definite strip. -/
theorem contDiffAt_raw_gaussianFormula {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (Q : ℝ × (PDE.Vec d × PDE.Vec d))
    (hQ : -(1 / 128 : ℝ) ≤ (Q.1 - tminus - sblock) / h) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (rawLift (gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v)) Q := by
  have hs : -(h / 128) ≤ Q.1 - tminus - sblock := by
    have hz := (le_div_iff₀ hh).mp hQ
    linarith only [hz]
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (T.1 - tminus - sblock, (T.2.1 - x (T.1 - tminus),
          T.2.2 - v (T.1 - tminus)))) := by
    exact ((contDiff_fst.sub contDiff_const).sub contDiff_const).prodMk
      ((contDiff_fst.comp contDiff_snd).sub
        (hx.comp (contDiff_fst.sub contDiff_const)) |>.prodMk
        ((contDiff_snd.comp contDiff_snd).sub
          (hv.comp (contDiff_fst.sub contDiff_const))))
  have hq := (contDiffAt_qform_raw hlam hh hs
    (Q.2.1 - x (Q.1 - tminus)) (Q.2.2 - v (Q.1 - tminus))).comp Q hmap.contDiffAt
  have htime : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : ℝ × (PDE.Vec d × PDE.Vec d) => T.1 - tminus - sblock) := by fun_prop
  have hchi := contDiff_barrierCutoff.comp (htime.div_const h)
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
    ell * barrierCutoff ((T.1 - tminus - sblock) / h) *
      (Real.exp (-Xi d lam Lam H h * (T.1 - tminus - sblock) -
        qform lam h (T.1 - tminus - sblock)
          (T.2.1 - x (T.1 - tminus)) (T.2.2 - v (T.1 - tminus))) - Real.exp (-L ^ 2))) Q
  exact (contDiffAt_const.mul hchi.contDiffAt).mul
    (((contDiffAt_const.mul htime.contDiffAt).sub hq).exp.sub contDiffAt_const)

/-- Global smoothness follows by gluing to zero, without a global inverse smoothness claim. -/
theorem contDiff_raw_gaussianBarrier {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞)
      (rawLift (gaussianBarrier lam Lam H h L ell tminus sblock x v)) := by
  rw [contDiff_iff_contDiffAt]
  intro Q
  by_cases hs : -(1 / 128 : ℝ) ≤ (Q.1 - tminus - sblock) / h
  · have hf := contDiffAt_raw_gaussianFormula hlam hh Lam H L ell tminus sblock hx hv Q hs
    apply hf.congr_of_eventuallyEq
    exact Eventually.of_forall (fun T => gaussianBarrier_eq_formula _ _ _ _ _ _ _ _ _ _ _)
  · have ht : Continuous (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (T.1 - tminus - sblock) / h) := by fun_prop
    have he : ∀ᶠ T in 𝓝 Q, (T.1 - tminus - sblock) / h < -(1 / 128 : ℝ) :=
      ht.continuousAt.eventually (gt_mem_nhds (lt_of_not_ge hs))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with T hT
    change gaussianBarrier lam Lam H h L ell tminus sblock x v
      ⟨T.1, T.2.1, T.2.2⟩ = 0
    unfold gaussianBarrier
    exact ite_eq_right (not_lt.mpr hT.le)



/-- Velocity translation leaves the velocity Hessian unchanged in moving coordinates. -/
theorem movingLift_velocityHessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (tminus : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) :
    kineticVelocityHessian (movingLift f tminus x v) P =
      kineticVelocityHessian
        (fun Q : KineticPoint d => f (P.time - tminus, (Q.position, Q.velocity)))
        ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩ := by
  let s := P.time - tminus
  let y := P.position - x s
  let g := fun V : PDE.Vec d => f (s, (y, V))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hslice : (fun V : PDE.Vec d => movingLift f tminus x v ⟨P.time, P.position, V⟩) =
      (fun V => g (-v s + (1 : ℝ) • V)) := by
    funext V
    simp only [movingLift, movingCoordinates, s, y, g, one_smul]
    congr 2
    abel_nf
  rw [kineticVelocityHessian_eq_sliceHessian, hslice,
    kineticVelocityHessian_eq_sliceHessian]
  have h := sliceHessian_affine (y₀ := -v s) (c := (1 : ℝ)) (Y := P.velocity)
    (hg.contDiffAt.of_le (by norm_cast))
  simpa only [one_smul, one_pow, neg_add_eq_sub] using h

/-- The source time slice is the raw time-direction derivative. -/
theorem deriv_raw_time_slice {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (s : ℝ) (y V : PDE.Vec d) :
    deriv (fun r => f (r, (y, V))) s = fderiv ℝ f (s, (y, V)) (1, (0, 0)) := by
  have hc := (hasDerivAt_id s).prodMk (hasDerivAt_const s (y, V))
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hc).deriv

/-- The source position-line derivative is the raw transport-direction derivative. -/
theorem deriv_raw_position_line {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (s : ℝ) (y V : PDE.Vec d) :
    deriv (fun r : ℝ => f (s, (y + r • V, V))) 0 =
      fderiv ℝ f (s, (y, V)) (0, (V, 0)) := by
  have hx : HasDerivAt (fun r : ℝ => y + r • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add y
  have hc := (hasDerivAt_const 0 s).prodMk (hx.prodMk (hasDerivAt_const 0 V))
  simpa only [Function.comp_def, zero_smul, add_zero] using
    ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt 0 hc).deriv




/-- The same source zero extension in stationary raw coordinates. -/
def gaussianProfile {d : ℕ} (lam Lam H h L ell sblock : ℝ)
    (Q : ℝ × (PDE.Vec d × PDE.Vec d)) : ℝ :=
  gaussianBarrier lam Lam H h L ell 0 sblock (fun _ => 0) (fun _ => 0)
    ⟨Q.1, Q.2.1, Q.2.2⟩

/-- The internally constructed stationary profile is smooth everywhere. -/
theorem contDiff_gaussianProfile {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell sblock : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianProfile (d := d) lam Lam H h L ell sblock) :=
  contDiff_raw_gaussianBarrier hlam hh Lam H L ell 0 sblock contDiff_const contDiff_const

/-- Moving the stationary profile produces exactly the whole-carrier source barrier. -/
theorem gaussianBarrier_eq_movingLift {d : ℕ} (lam Lam H h L ell tminus sblock : ℝ)
    (x v : ℝ → PDE.Vec d) :
    gaussianBarrier lam Lam H h L ell tminus sblock x v =
      movingLift (gaussianProfile lam Lam H h L ell sblock) tminus x v := by
  funext P
  simp only [gaussianBarrier, movingLift, movingCoordinates, gaussianProfile,
    sub_zero, gaussianFormula]

/-- On positive block times the stationary profile is the uncut Gaussian formula. -/
theorem gaussianProfile_of_pos {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    gaussianProfile lam Lam H h L ell sblock (s, (y, V)) =
      ell * (Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) - Real.exp (-L ^ 2)) := by
  unfold gaussianProfile
  rw [gaussianBarrier_eq_formula]
  dsimp only [gaussianFormula]
  simp only [sub_zero]
  rw [barrierCutoff_one (div_nonneg hs.le hh.le), mul_one]

/-- The time slice agrees locally with the uncut formula at a positive block time. -/
theorem gaussianProfile_time_eventuallyEq {d : ℕ} (lam Lam H L ell sblock : ℝ)
    {h s : ℝ} (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) =ᶠ[𝓝 s]
      (fun t => ell * (Real.exp (-Xi d lam Lam H h * (t - sblock) -
        qform lam h (t - sblock) y V) - Real.exp (-L ^ 2))) := by
  have he : ∀ᶠ t in 𝓝 s, 0 < t - sblock :=
    (continuousAt_id.sub continuousAt_const).eventually (lt_mem_nhds hs)
  filter_upwards [he] with t ht
  exact gaussianProfile_of_pos lam Lam H L ell sblock hh ht y V



/-- A smooth Euclidean Lipschitz velocity has the same Euclidean acceleration bound. -/
theorem vecEuclideanNorm_deriv_le {d : ℕ} {v : ℝ → PDE.Vec d} {H : ℝ}
    (hH : 0 ≤ H) (hv : Differentiable ℝ v)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) (s : ℝ) :
    PDE.vecEuclideanNorm (deriv v s) ≤ H := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he : HasDerivAt (fun t => e (v t)) (e (deriv v s)) s :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hv s).hasDerivAt
  have hb : ∀ᶠ t in 𝓝 s, ‖e (v t) - e (v s)‖ ≤ H * ‖t - s‖ := by
    exact Eventually.of_forall fun t => by
      rw [← map_sub, Real.norm_eq_abs]
      change ‖(v t - v s).toHilbertVec‖ ≤ H * |t - s|
      rw [← PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
      exact hLip t s
  have hnorm := norm_deriv_le_of_lip' hH hb
  rw [he.deriv] at hnorm
  rw [PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  exact hnorm



/-- Exact rescaling of the inverse velocity block. -/
theorem gramian_inv_velocity_scaling {lam h s : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ s) :
    (gramian lam h s)⁻¹ 1 1 = (ghat lam (s / h))⁻¹ 1 1 / h := by
  have hstrip : -(1 / 128 : ℝ) ≤ s / h := by
    apply (le_div_iff₀ hh).mpr
    linarith
  have hd := (posDef_ghat hlam hstrip).det_pos.ne'
  have hscale : covarianceDet lam h s = h ^ 4 * (ghat lam (s / h)).det := by
    rw [det_ghat]
    unfold covarianceDet covarianceXX covarianceVV covarianceXV
    field_simp
    ring
  have ha : covarianceXX lam h s =
      h ^ 3 * (lam / 64 * (1 + (s / h) ^ 2) + lam * (s / h) ^ 3 / 3) := by
    unfold covarianceXX
    field_simp
  rw [gramian_inv_blocks lam hh, ghat_inv_velocity]
  simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hscale, ha]
  field_simp

/-- Native velocity block trace bound, with the original dimension and physical scale. -/
theorem gramian_velocity_trace_le (d : ℕ) {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hs0 : 0 ≤ s) (hs1 : s ≤ h) :
    Matrix.trace (((gramian lam h s)⁻¹ 1 1) • (1 : PDE.Mat d)) ≤
      (128 * (d : ℝ) / lam) / h := by
  have ht0 : 0 ≤ s / h := div_nonneg hs0 hh.le
  have ht1 : s / h ≤ 1 := (div_le_one hh).mpr hs1
  have hs : -(h / 128) ≤ s := by linarith
  rw [gramian_inv_velocity_scaling hlam hh hs, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  have hi := div_le_div_of_nonneg_right (ghat_inv_velocity_le hlam ht0 ht1) hh.le
  have hm := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  convert hm using 1
  ring



/-- Native rank-one contraction is the corresponding Euclidean quadratic form. -/
theorem matrixContraction_rankOne {d : ℕ} (A : PDE.Mat d) (p : PDE.Vec d) :
    matrixContraction A (fun i j => p i * p j) = PDE.vecDot p (A.mulVec p) := by
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Contraction against the identity is exactly the native matrix trace. -/
theorem matrixContraction_identity {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A (1 : PDE.Mat d) = A.trace := by
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

/-- The exact Gaussian Hessian contraction in native Euclidean coordinates. -/
theorem matrixContraction_gaussian {d : ℕ} (A : PDE.Mat d) (p : PDE.Vec d) (a R : ℝ) :
    matrixContraction A (fun i j => a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j)) =
      a * (4 * PDE.vecDot p (A.mulVec p) - 2 * R * A.trace) := by
  let K : PDE.Mat d := fun i j => p i * p j
  have hm : (fun i j => a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j)) =
      a • ((4 : ℝ) • K + (-2 * R) • (1 : PDE.Mat d)) := by
    ext i j
    change a * (4 * p i * p j - 2 * R * (1 : PDE.Mat d) i j) =
      a * ((4 : ℝ) * (p i * p j) + (-2 * R) * (1 : PDE.Mat d) i j)
    ring
  rw [hm, matrixContraction_smul_right, matrixContraction_add_right,
    matrixContraction_smul_right, matrixContraction_smul_right,
    matrixContraction_rankOne, matrixContraction_identity]
  ring

/-- Lower Loewner ellipticity yields the literal native quadratic lower bound. -/
theorem loewner_quadratic_lower {d : ℕ} {A : PDE.Mat d} {lam : ℝ}
    (hl : lam • (1 : PDE.Mat d) ≤ A) (p : PDE.Vec d) :
    lam * PDE.vecNormSq p ≤ PDE.vecDot p (A.mulVec p) := by
  have hp := (Matrix.le_iff.mp hl).dotProduct_mulVec_nonneg p
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  change 0 ≤ PDE.vecDot p (A.mulVec p) - lam * PDE.vecNormSq p at hp
  linarith only [hp]

/-- Upper Loewner ellipticity bounds the coefficient trace by `d Lam`. -/
theorem loewner_trace_upper {d : ℕ} {A : PDE.Mat d} {Lam : ℝ}
    (hu : A ≤ Lam • (1 : PDE.Mat d)) : A.trace ≤ (d : ℝ) * Lam := by
  have hp := (Matrix.le_iff.mp hu).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at hp
  simp only [Fintype.card_fin, smul_eq_mul] at hp
  linarith only [hp]

/-- The inverse velocity covariance scalar is nonnegative on the definite strip. -/
theorem gramian_inv_velocity_nonneg {lam h s : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ s) : 0 ≤ (gramian lam h s)⁻¹ 1 1 :=
  (posDef_gramian hlam hh hs).inv.posSemidef.diag_nonneg





/-- Transport cancellation gives the exact scalar Gaussian contribution to the operator. -/
theorem gaussianProfile_transport {d : ℕ} {lam h s : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell sblock : ℝ)
    (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    deriv (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) s +
      deriv (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
        (s, (y + r • V, V))) 0 =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h + lam * PDE.vecNormSq (pform lam h (s - sblock) y V))   := by
  have gaussianProfile_position_deriv {d : ℕ} (y : PDE.Vec d) (V : PDE.Vec d) :
      deriv (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
      (s, (y + r • V, V))) 0 =
      -ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        deriv (fun r : ℝ => qform lam h (s - sblock) (y + r • V) V) 0 := by
    have heq : (fun r : ℝ => gaussianProfile lam Lam H h L ell sblock
        (s, (y + r • V, V))) =
        (fun r : ℝ => ell * (Real.exp (-Xi d lam Lam H h * (s - sblock) -
          qform lam h (s - sblock) (y + r • V) V) - Real.exp (-L ^ 2))) := by
      funext r
      exact gaussianProfile_of_pos lam Lam H L ell sblock hh hs _ _
    rw [heq]
    have hq := hasDerivAt_qform_transport lam hh (s - sblock) y V
    have he := (((hasDerivAt_const 0 (-Xi d lam Lam H h * (s - sblock))).sub hq).exp.sub_const
      (Real.exp (-L ^ 2))).const_mul ell
    simp only [Pi.sub_apply] at he
    rw [he.deriv, hq.deriv]
    simp only [zero_smul, add_zero, zero_sub]
    ring
  have gaussianProfile_time_deriv {d : ℕ} (y : PDE.Vec d) (V : PDE.Vec d) :
      deriv (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) s =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h - deriv (fun t => qform lam h t y V) (s - sblock)) := by
    have hstrip : -(h / 128) ≤ s - sblock := by linarith only [hs, hh]
    have hqt := hasDerivAt_qform_time hlam hh hstrip y V
    have ht := (hasDerivAt_id s).sub_const sblock
    have hq := hqt.comp s ht
    have he := (((ht.const_mul (-Xi d lam Lam H h)).sub hq).exp.sub_const
      (Real.exp (-L ^ 2))).const_mul ell
    have heq := gaussianProfile_time_eventuallyEq lam Lam H L ell sblock hh hs y V
    have he' := he.congr_of_eventuallyEq heq
    rw [he'.deriv, hqt.deriv]
    simp only [Pi.sub_apply, Function.comp_def, id_eq, mul_one]
    ring
  rw [gaussianProfile_time_deriv,
    gaussianProfile_position_deriv]
  have hstrip : -(h / 128) < s - sblock := by linarith only [hs, hh]
  have hq := quadratic_transport_identity lam h (s - sblock) hlam hh hstrip y V
  calc
    _ = ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
        (-Xi d lam Lam H h - (deriv (fun t => qform lam h t y V) (s - sblock) +
          deriv (fun r : ℝ => qform lam h (s - sblock) (y + r • V) V) 0)) := by ring
    _ = _ := by rw [hq]; ring



/-- For fixed covariance time the native velocity quadratic is smooth everywhere. -/
theorem contDiff_qform_velocity {d : ℕ} (lam h sigma : ℝ) (y : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun V => qform lam h sigma y V) := by
  unfold qform PDE.vecDot
  fun_prop

/-- The profile velocity slice factors into an exponential quadratic and a constant. -/
theorem gaussianProfile_velocitySlice {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y : PDE.Vec d) :
    (fun V => gaussianProfile lam Lam H h L ell sblock (s, (y, V))) =
      (fun V => (ell * Real.exp (-Xi d lam Lam H h * (s - sblock))) *
        Real.exp (-qform lam h (s - sblock) y V) + (-ell * Real.exp (-L ^ 2))) := by
  funext V
  rw [gaussianProfile_of_pos lam Lam H L ell sblock hh hs]
  rw [sub_eq_add_neg (-Xi d lam Lam H h * (s - sblock)), Real.exp_add]
  ring

/-- The profile velocity gradient is exactly minus twice amplitude times Gaussian times `p`. -/
theorem gaussianProfile_velocityGradient {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    PDE.classicalGradient
      (fun W => gaussianProfile lam Lam H h L ell sblock (s, (y, W))) V =
      (-2 * ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V)) • pform lam h (s - sblock) y V := by
  have hq := (contDiff_qform_velocity lam h (s - sblock) y).differentiable (by norm_num) V
  have hExp : DifferentiableAt ℝ (fun W => Real.exp (-qform lam h (s - sblock) y W)) V :=
    hq.neg.exp
  have hMul : DifferentiableAt ℝ (fun W =>
      (ell * Real.exp (-Xi d lam Lam H h * (s - sblock))) *
        Real.exp (-qform lam h (s - sblock) y W)) V :=
    (differentiableAt_const _).mul hExp
  rw [gaussianProfile_velocitySlice lam Lam H L ell sblock hh hs,
    classicalGradient_add hMul (differentiableAt_const _),
    classicalGradient_const_mul _ hExp,
    classicalGradient_exp_neg hq]
  have hzero : PDE.classicalGradient (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) V = 0 := by
    ext i
    simp [PDE.classicalGradient]
  rw [hzero, add_zero]
  have hgrad := kineticVelocityGradient_qform lam hh (s - sblock) y V
  change PDE.classicalGradient (fun W => qform lam h (s - sblock) y W) V = _ at hgrad
  rw [hgrad, sub_eq_add_neg (-Xi d lam Lam H h * (s - sblock)), Real.exp_add]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The profile velocity Hessian has the exact Gaussian rank-one minus covariance form. -/
theorem gaussianProfile_velocityHessian {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) (i j : Fin d) :
    sliceHessian (fun W => gaussianProfile lam Lam H h L ell sblock (s, (y, W))) V i j =
      ell * Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) *
      (4 * pform lam h (s - sblock) y V i * pform lam h (s - sblock) y V j -
        2 * (gramian lam h (s - sblock))⁻¹ 1 1 * (1 : PDE.Mat d) i j) := by
  have hq : ContDiff ℝ 2 (fun W => qform lam h (s - sblock) y W) :=
    (contDiff_qform_velocity lam h (s - sblock) y).of_le (by norm_cast)
  rw [gaussianProfile_velocitySlice lam Lam H L ell sblock hh hs,
    sliceHessian_add (contDiffAt_const.mul hq.contDiffAt.neg.exp) contDiffAt_const,
    sliceHessian_const_mul _ hq.contDiffAt.neg.exp]
  have hz : sliceHessian (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) V = 0 := by
    have hc : (fun W : PDE.Vec d =>
        PDE.classicalGradient (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) W) =
        (fun _ => (0 : PDE.Vec d)) := by
      funext W
      ext k
      change (fderiv ℝ (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) W)
        (PDE.basisVec k) = 0
      rw [fderiv_const_apply]
      rfl
    ext k l
    change (fderiv ℝ (fun W : PDE.Vec d =>
        PDE.classicalGradient (fun _ : PDE.Vec d => -ell * Real.exp (-L ^ 2)) W) V)
        (PDE.basisVec k) l = 0
    rw [hc, fderiv_const_apply]
    rfl
  rw [hz, add_zero, Matrix.smul_apply, sliceHessian_exp_neg hq]
  have hgrad := kineticVelocityGradient_qform lam hh (s - sblock) y V
  change PDE.classicalGradient (fun W => qform lam h (s - sblock) y W) V = _ at hgrad
  have hhess := kineticVelocityHessian_qform lam (h := h) (s - sblock) y V
  rw [kineticVelocityHessian_eq_sliceHessian] at hhess
  rw [hgrad, hhess]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rw [sub_eq_add_neg (-Xi d lam Lam H h * (s - sblock)), Real.exp_add]
  ring



/-- The source Gaussian operator identity without division by the amplitude. -/
theorem gaussianBarrier_backwardOperator {d : ℕ} (A : FullKineticCoefficient d)
    {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (P : KineticPoint d) (hs : 0 < P.time - tminus - sblock) :
    backwardOperator A (gaussianBarrier lam Lam H h L ell tminus sblock x v) P =
      ell * Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
      (-Xi d lam Lam H h +
        lam * PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) +
        2 * PDE.vecDot (deriv v (P.time - tminus))
          (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) +
        2 * (gramian lam h (P.time - tminus - sblock))⁻¹ 1 1 *
          (fullKineticCoefficientAt A P).trace -
        4 * PDE.vecDot (pform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)))
          ((fullKineticCoefficientAt A P).mulVec
            (pform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)))))  := by
  have movingLift_backwardOperator {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      backwardOperator A (movingLift f tminus x v) P =
      deriv (fun s => f (s, (P.position - x (P.time - tminus),
        P.velocity - v (P.time - tminus)))) (P.time - tminus) +
      deriv (fun r : ℝ => f (P.time - tminus,
        (P.position - x (P.time - tminus) + r • (P.velocity - v (P.time - tminus)),
          P.velocity - v (P.time - tminus)))) 0 -
      PDE.vecDot (deriv v (P.time - tminus))
        (kineticVelocityGradient (fun Q : KineticPoint d =>
          f (P.time - tminus, (Q.position, Q.velocity)))
          ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩) -
      matrixContraction (fullKineticCoefficientAt A P)
        (kineticVelocityHessian (fun Q : KineticPoint d =>
          f (P.time - tminus, (Q.position, Q.velocity)))
          ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩) := by
    let s := P.time - tminus
    let y := P.position - x s
    let V := P.velocity - v s
    have hslice : DifferentiableAt ℝ (rawLift (fun Q : KineticPoint d =>
        f (s, (Q.position, Q.velocity)))) (rawPoint (⟨0, y, V⟩ : KineticPoint d)) := by
      exact (hf.comp (contDiff_const.prodMk contDiff_snd)).differentiable (by norm_num) _
    rw [backwardOperator, movingLift_transport hf hx hv hkin,
      movingLift_velocityHessian hf, deriv_raw_time_slice hf, deriv_raw_position_line hf]
    rw [vecDot_kineticVelocityGradient hslice]
    change _ = _
    have hvel : fderiv ℝ (rawLift (fun Q : KineticPoint d => f (s, (Q.position, Q.velocity))))
        (rawPoint (⟨0, y, V⟩ : KineticPoint d)) (0, (0, deriv v s)) =
        fderiv ℝ f (s, (y, V)) (0, (0, deriv v s)) := by
      have hc := (hasFDerivAt_const s (rawPoint (⟨0, y, V⟩ : KineticPoint d))).prodMk
        (hasFDerivAt_snd (𝕜 := ℝ) (p := rawPoint (⟨0, y, V⟩ : KineticPoint d)))
      change fderiv ℝ (f ∘ fun Q : ℝ × (PDE.Vec d × PDE.Vec d) => (s, Q.2))
        (rawPoint (⟨0, y, V⟩ : KineticPoint d)) (0, (0, deriv v s)) = _
      rw [((hf.differentiable (by norm_num) _).hasFDerivAt.comp _ hc).fderiv]
      simp [rawPoint]
    rw [hvel]
    rw [← map_add]
    simp only [movingCoordinates, s, y, V, Prod.mk_add_mk, zero_add, add_zero]
  let s := P.time - tminus
  let sigma := s - sblock
  let y := P.position - x s
  let V := P.velocity - v s
  let pvec := pform lam h sigma y V
  let G := Real.exp (-Xi d lam Lam H h * sigma - qform lam h sigma y V)
  let B := fullKineticCoefficientAt A P
  have hf := contDiff_gaussianProfile (d := d) hlam hh Lam H L ell sblock
  have hg : kineticVelocityGradient (fun Q : KineticPoint d =>
      gaussianProfile lam Lam H h L ell sblock (s, (Q.position, Q.velocity)))
      ⟨0, y, V⟩ = (-2 * ell * G) • pvec :=
    gaussianProfile_velocityGradient lam Lam H L ell sblock hh hs y V
  have hHess : kineticVelocityHessian (fun Q : KineticPoint d =>
      gaussianProfile lam Lam H h L ell sblock (s, (Q.position, Q.velocity)))
      ⟨0, y, V⟩ =
      (fun i j => ell * G * (4 * pvec i * pvec j -
        2 * (gramian lam h sigma)⁻¹ 1 1 * (1 : PDE.Mat d) i j)) := by
    rw [kineticVelocityHessian_eq_sliceHessian]
    ext i j
    exact gaussianProfile_velocityHessian lam Lam H L ell sblock hh hs y V i j
  rw [gaussianBarrier_eq_movingLift,
    movingLift_backwardOperator hf,
    gaussianProfile_transport hlam hh Lam H L ell sblock hs y V]
  change ell * G * (-Xi d lam Lam H h + lam * PDE.vecNormSq pvec) -
    PDE.vecDot (deriv v s) _ - matrixContraction B _ = _
  rw [hg, hHess, matrixContraction_gaussian]
  rw [PDE.vecDot_comm (deriv v s), vecDot_smul_left, PDE.vecDot_comm pvec]
  change _ = ell * G * (-Xi d lam Lam H h + lam * PDE.vecNormSq pvec +
    2 * PDE.vecDot (deriv v s) pvec + 2 * (gramian lam h sigma)⁻¹ 1 1 * B.trace -
    4 * PDE.vecDot pvec (B.mulVec pvec))
  ring



/-- Ellipticity and the covariance trace give the source Gaussian differential sign. -/
theorem gaussianBarrier_sign {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell tminus sblock : ℝ) (hLam : lam ≤ Lam) (hH : 0 ≤ H) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) :
    ∀ᵐ P ∂(volume.restrict {P : KineticPoint d |
      0 < P.time - tminus - sblock ∧ P.time - tminus - sblock ≤ h}),
      backwardOperator A (gaussianBarrier lam Lam H h L ell tminus sblock x v) P ≤
        -(3 * lam / 2) * ell *
          Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
            qform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
          PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) ∧
        -(3 * lam / 2) * ell *
          Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
            qform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
          PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) ≤ 0  := by
  have acceleration_young {d : ℕ} {H : ℝ} (a : PDE.Vec d) (p : PDE.Vec d) (ha : PDE.vecEuclideanNorm a ≤ H) :
      2 * PDE.vecDot a p ≤ (3 * lam / 2) * PDE.vecNormSq p + 2 * H ^ 2 / (3 * lam) := by
    have hdot := (le_abs_self (PDE.vecDot a p)).trans
      ((PDE.abs_vecDot_le_vecEuclideanNorm_mul a p).trans
        (mul_le_mul_of_nonneg_right ha (PDE.vecEuclideanNorm_nonneg p)))
    have hr := PDE.vecEuclideanNorm_sq p
    have hden : 0 < 3 * lam := by positivity
    have hy : 2 * H * PDE.vecEuclideanNorm p ≤
        (3 * lam / 2) * PDE.vecNormSq p + 2 * H ^ 2 / (3 * lam) := by
      apply (mul_le_mul_iff_right₀ hden).mp
      have hcancel : (3 * lam) * (2 * H ^ 2 / (3 * lam)) = 2 * H ^ 2 := by
        field_simp
      rw [mul_add, hcancel, ← hr]
      nlinarith only [sq_nonneg (3 * lam * PDE.vecEuclideanNorm p - 2 * H)]
    exact (mul_le_mul_of_nonneg_left hdot (by norm_num)).trans (by
      simpa only [mul_assoc] using hy)
  let S := {P : KineticPoint d | 0 < P.time - tminus - sblock ∧
    P.time - tminus - sblock ≤ h}
  have ht : Continuous (fun P : KineticPoint d => P.time - tminus - sblock) :=
    (continuous_time.sub continuous_const).sub continuous_const
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const ht).measurableSet.inter
      (isClosed_le ht continuous_const).measurableSet
  have hlo := hA.2.2.1.filter_mono (ae_restrict_le (μ := volume) (s := S))
  have hup := hA.2.2.2.filter_mono (ae_restrict_le (μ := volume) (s := S))
  filter_upwards [hlo, hup, ae_restrict_mem hS] with P hl hu hP
  let sigma := P.time - tminus - sblock
  let y := P.position - x (P.time - tminus)
  let V := P.velocity - v (P.time - tminus)
  let pvec := pform lam h sigma y V
  let R := (gramian lam h sigma)⁻¹ 1 1
  let B := fullKineticCoefficientAt A P
  let G := Real.exp (-Xi d lam Lam H h * sigma - qform lam h sigma y V)
  have hs : 0 < sigma ∧ sigma ≤ h := hP
  have hstrip : -(h / 128) ≤ sigma := by linarith only [hh, hs.1]
  have hR : 0 ≤ R := gramian_inv_velocity_nonneg hlam hh hstrip
  have hLam0 : 0 ≤ Lam := (hlam.trans_le hLam).le
  have hquad := loewner_quadratic_lower hl pvec
  have htrA := loewner_trace_upper hu
  have htrR := gramian_velocity_trace_le d hlam hh hs.1.le hs.2
  rw [Matrix.trace_smul, Matrix.trace_one] at htrR
  simp only [Fintype.card_fin, smul_eq_mul] at htrR
  have htrace : 2 * R * B.trace ≤ 2 * Lam * (128 * (d : ℝ) / lam) / h := by
    calc
      _ ≤ 2 * R * ((d : ℝ) * Lam) :=
        mul_le_mul_of_nonneg_left htrA (mul_nonneg (by norm_num) hR)
      _ = (2 * Lam) * (R * (d : ℝ)) := by ring
      _ ≤ (2 * Lam) * ((128 * (d : ℝ) / lam) / h) :=
        mul_le_mul_of_nonneg_left htrR (mul_nonneg (by norm_num) hLam0)
      _ = _ := by ring
  have hyoung := acceleration_young (deriv v (P.time - tminus)) pvec
    (vecEuclideanNorm_deriv_le hH (hv.differentiable (by norm_num)) hLip _)
  have hfactor : -Xi d lam Lam H h + lam * PDE.vecNormSq pvec +
      2 * PDE.vecDot (deriv v (P.time - tminus)) pvec + 2 * R * B.trace -
      4 * PDE.vecDot pvec (B.mulVec pvec) ≤ -(3 * lam / 2) * PDE.vecNormSq pvec := by
    unfold Xi
    linarith only [hquad, htrace, hyoung]
  have hG : 0 ≤ ell * G := mul_nonneg hell (Real.exp_pos _).le
  have hsign := mul_le_mul_of_nonneg_left hfactor hG
  rw [gaussianBarrier_backwardOperator A hlam hh Lam H L ell tminus sblock hx hv hkin P hs.1]
  constructor
  · convert hsign using 1; ring
  · change -(3 * lam / 2) * ell * G * PDE.vecNormSq pvec ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hell)
        (Real.exp_pos _).le) (PDE.vecNormSq_nonneg pvec)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

