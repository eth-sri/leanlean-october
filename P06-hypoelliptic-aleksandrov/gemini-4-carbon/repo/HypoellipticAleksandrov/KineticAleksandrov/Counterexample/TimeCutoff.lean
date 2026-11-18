module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Flattening

@[expose] public noncomputable section

namespace HypoellipticAleksandrov
open scoped BigOperators



/-- The continuous linear functional `w ↦ 2 (z · w)`. -/
noncomputable def vecNormSqFDeriv {d : ℕ} (z : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i, (2 * z i) • ContinuousLinearMap.proj i

@[simp]
theorem vecNormSqFDeriv_apply {d : ℕ} (z w : PDE.Vec d) :
    vecNormSqFDeriv z w = 2 * PDE.vecDot z w := by
  classical
  unfold vecNormSqFDeriv PDE.vecDot
  simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The squared explicit Euclidean norm has derivative `w ↦ 2 (z · w)`. -/
theorem hasFDerivAt_vecNormSq {d : ℕ} (z : PDE.Vec d) :
    HasFDerivAt PDE.vecNormSq (vecNormSqFDeriv z) z := by
  classical
  have hd : DifferentiableAt ℝ PDE.vecNormSq z := by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop
  convert hd.hasFDerivAt using 1
  ext w
  rw [vecNormSqFDeriv_apply]
  unfold PDE.vecNormSq PDE.vecDot
  rw [fderiv_fun_sum fun i _ => by fun_prop]
  simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp
  rw [(hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv]
  simp
  ring




end HypoellipticAleksandrov

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open HypoellipticAleksandrov.Parabolic Set
open scoped BigOperators MatrixOrder ContDiff

/-- Decaying quadratic barrier from Appendix C. -/
def barrier {d : ℕ} (mu R : ℝ) (P : KineticPoint d) : ℝ :=
  Real.exp (-mu * P.time) * (2 - PDE.vecNormSq P.velocity / R ^ 2)

/-- Exact time derivative. -/
theorem barrier_timeDerivative {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (barrier mu R) P =
      -mu * Real.exp (-mu * P.time) * (2 - PDE.vecNormSq P.velocity / R ^ 2) := by
  have h := (((hasDerivAt_id P.time).const_mul (-mu)).exp).mul_const
    (2 - PDE.vecNormSq P.velocity / R ^ 2)
  change deriv (fun t => Real.exp (-mu * t) *
    (2 - PDE.vecNormSq P.velocity / R ^ 2)) P.time = _
  simpa [mul_assoc, mul_comm, mul_left_comm] using h.deriv

/-- Independence of position. -/
theorem barrier_positionGradient {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticPositionGradient (barrier mu R) P = 0 := by
  ext i
  change fderiv ℝ (fun _x =>
    Real.exp (-mu * P.time) * (2 - PDE.vecNormSq P.velocity / R ^ 2))
      P.position (PDE.basisVec i) = 0
  rw [fderiv_const_apply]
  rfl

/-- Exact coordinate velocity gradient. -/
theorem barrier_velocityGradient {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticVelocityGradient (barrier mu R) P =
      fun i => -(2 * Real.exp (-mu * P.time) / R ^ 2) * P.velocity i := by
  have h := ((hasFDerivAt_const (c := 2) P.velocity).sub
    ((hasFDerivAt_vecNormSq P.velocity).mul_const ((R ^ 2)⁻¹))).const_mul
      (Real.exp (-mu * P.time))
  ext i
  change fderiv ℝ (fun v => Real.exp (-mu * P.time) *
    (2 - PDE.vecNormSq v / R ^ 2)) P.velocity (PDE.basisVec i) = _
  dsimp only [Pi.sub_apply] at h
  simp only [div_eq_mul_inv] at *
  rw [h.fderiv]
  simp
  simp [PDE.vecDot, PDE.basisVec_apply, mul_ite, Finset.sum_ite_eq', Finset.mem_univ]
  ring

/-- Exact velocity Hessian, including its diagonal factor two. -/
theorem barrier_velocityHessian {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticVelocityHessian (barrier mu R) P =
      (-(2 * Real.exp (-mu * P.time) / R ^ 2)) • (1 : PDE.Mat d) := by
  have hg : (fun v => PDE.classicalGradient
      (fun w => barrier mu R ⟨P.time, P.position, w⟩) v) =
      fun v => (-(2 * Real.exp (-mu * P.time) / R ^ 2)) • v := by
    funext v
    exact barrier_velocityGradient mu R ⟨P.time, P.position, v⟩
  ext i j
  unfold kineticVelocityHessian
  rw [hg]
  have h := (hasFDerivAt_id (𝕜 := ℝ) P.velocity).const_smul
    (-(2 * Real.exp (-mu * P.time) / R ^ 2))
  change HasFDerivAt (fun v =>
    (-(2 * Real.exp (-mu * P.time) / R ^ 2)) • v) _ P.velocity at h
  rw [h.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply, PDE.basisVec_apply]
  simp only [eq_comm]

/-- Contraction of the barrier Hessian with an arbitrary coefficient. -/
theorem barrier_hessianContraction {d : ℕ} (A : PDE.Mat d) (mu R : ℝ)
    (P : KineticPoint d) :
    matrixContraction A (kineticVelocityHessian (barrier mu R) P) =
      -(2 * Real.exp (-mu * P.time) / R ^ 2) * A.trace := by
  rw [barrier_velocityHessian, matrixContraction_smul_right]
  congr 1
  simp [matrixContraction, Matrix.one_apply, mul_ite, Finset.sum_ite_eq, Finset.mem_univ, Matrix.trace, Matrix.diag_apply]

/-- Exact backward operator formula, before ellipticity is used. -/
theorem barrier_operator {d : ℕ}
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (mu R : ℝ) (P : KineticPoint d) :
    backwardOperator (fun _t x v => A (x, v)) (barrier mu R) P =
      Real.exp (-mu * P.time) *
        (2 * (A (P.position, P.velocity)).trace / R ^ 2 -
          mu * (2 - PDE.vecNormSq P.velocity / R ^ 2)) := by
  rw [backwardOperator_apply, barrier_timeDerivative, barrier_positionGradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [barrier_hessianContraction, fullKineticCoefficientAt_apply]
  ring


/-- The prescribed decay rate gives a nonnegative backward operator globally. -/
theorem barrier_operator_nonneg {d : ℕ} (hd : 1 ≤ d)
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R)
    (hA : ∀ q, lam • (1 : PDE.Mat d) ≤ A q) (P : KineticPoint d) :
    0 ≤ backwardOperator (fun _t x v => A (x, v))
      (barrier ((d : ℝ) * lam / R ^ 2) R) P  := by
  have barrier_trace_lower {d : ℕ} (A : PDE.Mat d) (hA : lam • 1 ≤ A) :
      (d : ℝ) * lam ≤ A.trace := by
    have hdiag : ∀ i : Fin d, lam ≤ A i i := by
      intro i
      simpa using (Matrix.le_iff.mp hA).diag_nonneg (i := i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Matrix.trace, Matrix.diag_apply] using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdiag i))
  rw [barrier_operator]
  apply mul_nonneg (Real.exp_pos _).le
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hs := sq_pos_of_pos hR
  have hfirst : 0 ≤ 2 * ((A (P.position, P.velocity)).trace - d * lam) / R ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (barrier_trace_lower _ (hA (P.position, P.velocity))))) hs.le
  have hsecond :=
    mul_nonneg (div_nonneg ((mul_pos hdpos hlam).le) hs.le) (div_nonneg (PDE.vecNormSq_nonneg P.velocity) hs.le)
  have heq : 2 * (A (P.position, P.velocity)).trace / R ^ 2 -
      (d * lam / R ^ 2) * (2 - PDE.vecNormSq P.velocity / R ^ 2) =
      2 * ((A (P.position, P.velocity)).trace - d * lam) / R ^ 2 +
        (d * lam / R ^ 2) * (PDE.vecNormSq P.velocity / R ^ 2) := by ring
  rw [heq]
  exact add_nonneg hfirst hsecond

/-- Source terminal time, fixed independently of the flattening scale. -/
def barrierTime (mu : ℝ) : ℝ := Real.log 8 / mu

/-- The chosen terminal time is positive for positive decay rate. -/
theorem barrierTime_pos {mu : ℝ} (hmu : 0 < mu) : 0 < barrierTime mu :=
  div_pos (Real.log_pos (by norm_num)) hmu

/-- The terminal exponential factor is exactly one eighth. -/
theorem barrier_terminal_factor {mu : ℝ} (hmu : 0 < mu) :
    Real.exp (-mu * barrierTime mu) = (1 / 8 : ℝ) := by
  have he : -mu * barrierTime mu = -Real.log 8 := by
    unfold barrierTime
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num


/-- A fixed smooth replacement of the positive part. -/
def timeCutoffTheta (s : ℝ) : ℝ := flatteningPsi (16 * s + 1) / 16

/-- Smoothness of the cutoff at every finite order. -/
theorem contDiff_timeCutoffTheta : ContDiff ℝ ∞ timeCutoffTheta := by
  exact (contDiff_flatteningPsi.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)).div_const 16

/-- The cutoff vanishes on the negative half-line. -/
theorem timeCutoffTheta_eq_zero (s : ℝ) (hs : s ≤ 0) : timeCutoffTheta s = 0 := by
  unfold timeCutoffTheta
  rw [flatteningPsi_eq_zero _ (by linarith)]
  norm_num

/-- The cutoff is nonnegative globally. -/
theorem timeCutoffTheta_nonneg (s : ℝ) : 0 ≤ timeCutoffTheta s :=
  div_nonneg (flatteningPsi_nonneg _) (by norm_num)

/-- The exact first derivative of the rescaled primitive. -/
theorem deriv_timeCutoffTheta (s : ℝ) :
    deriv timeCutoffTheta s = flatteningSlope (16 * s + 1) := by
  have hc := ((contDiff_flatteningSlope.continuous.integral_hasStrictDerivAt 1 (16 * s + 1)).hasDerivAt).comp s (((hasDerivAt_id s).const_mul 16).add_const 1)
  simpa only [timeCutoffTheta, flatteningPsi, id_eq, mul_one,
    mul_div_cancel_right₀ _ (by norm_num : (16 : ℝ) ≠ 0)] using! (hc.div_const 16).deriv

/-- The first derivative lies in the unit interval. -/
theorem timeCutoffTheta_deriv_bounds (s : ℝ) :
    0 ≤ deriv timeCutoffTheta s ∧ deriv timeCutoffTheta s ≤ 1 := by
  rw [deriv_timeCutoffTheta]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The second derivative is nonnegative everywhere. -/
theorem timeCutoffTheta_deriv2_nonneg (s : ℝ) :
    0 ≤ deriv (deriv timeCutoffTheta) s := by
  apply Monotone.deriv_nonneg
  intro a b h
  rw [deriv_timeCutoffTheta, deriv_timeCutoffTheta]
  exact monotone_flatteningSlope (by linarith)

/-- The source's uniform lower comparison with the positive part. -/
theorem timeCutoffTheta_lower (s : ℝ) : s - 1 / 8 ≤ timeCutoffTheta s := by
  by_cases hs : s ≤ 1 / 8
  · exact (sub_nonpos.mpr hs).trans (timeCutoffTheta_nonneg s)
  · unfold timeCutoffTheta
    rw [flatteningPsi_eq_affine _ (by linarith)]
    have h := flatteningOffset_bounds.2
    linarith

/-- The literal time-dependent function before the collar extension. -/
def timeCutoffProfile {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : ℝ :=
  timeCutoffTheta (flatProfile H flatteningPsi flatteningOffset alpha r
    (P.position, P.velocity) - barrier mu R P)

/-- Nonnegativity holds on the whole carrier before any extension. -/
theorem timeCutoffProfile_nonneg {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : 0 ≤ timeCutoffProfile H alpha r mu R P :=
  timeCutoffTheta_nonneg _

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

