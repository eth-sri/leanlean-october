module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionMatrix
import all HypoellipticAleksandrov.LinearAlgebra.LoewnerPolarization
import all HypoellipticAleksandrov.Parabolic.ExponentialConjugation

open private HypoellipticAleksandrov.Parabolic.fderiv_timeCoordinate_apply from HypoellipticAleksandrov.Parabolic.ExponentialConjugation
open private HypoellipticAleksandrov.KineticAleksandrov.Decay.contraction_one from HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionMatrix
section
open private HypoellipticAleksandrov.vecDot_mulVec_upper_of_loewner from HypoellipticAleksandrov.LinearAlgebra.LoewnerPolarization
private alias _sharedProof_383_0 := HypoellipticAleksandrov.vecDot_mulVec_upper_of_loewner
end


/-!
# The parabolic resolvent barrier

This module implements the hyperbolic-cosine barrier in Krylov--Safonov,
Lemma 3.1, specialized to the second-order operator without lower-order terms.
It proves the time derivative, velocity Hessian, matrix contraction, and exact
forward-operator formula before establishing the coefficient-uniform strict
sign under pointwise two-sided Loewner ellipticity.

The coefficient field is used only at the evaluation point. In particular,
the result requires no coefficient regularity or off-point ellipticity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Matrix
open scoped BigOperators MatrixOrder

variable {d : ℕ}

variable (a rho : ℝ)

/-- The scalar phase of the Krylov--Safonov resolvent barrier. -/
def resolventPhase   (z : TimeVelocity d) : ℝ :=
  a * Real.sqrt rho * (PDE.vecNormSq z.2 - z.1)

/-- The hyperbolic-cosine resolvent barrier. -/
def resolventBarrier   : TimeVelocity d → ℝ :=
  fun z => Real.cosh (resolventPhase a rho z)




private theorem fderiv_velocityCoordinate_apply  (i : Fin d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.2 i) z w = w.2 i := by
  have h :=
    (hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd  )
  change (fderiv ℝ ((fun f : PDE.Vec d => f i) ∘ Prod.snd) z) w = w.2 i
  rw [h.fderiv]
  rfl

private theorem fderiv_vecDot_snd_apply  (q : PDE.Vec d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => PDE.vecDot y.2 q) z w =
      PDE.vecDot w.2 q := by
  classical
  unfold PDE.vecDot

  rw [(fderiv_fun_sum fun i _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_mul_const (by fun_prop) (q i)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_velocityCoordinate_apply]
  ring

private theorem fderiv_vecNormSq_snd_apply
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => PDE.vecNormSq y.2) z w =
      2 * PDE.vecDot z.2 w.2 := by
  classical
  unfold PDE.vecNormSq PDE.vecDot

  rw [(fderiv_fun_sum fun i _ => by fun_prop)]
  simp only [ContinuousLinearMap.sum_apply]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [fderiv_velocityCoordinate_apply]
  ring

variable (a rho : ℝ)

private theorem contDiff_resolventPhase   :
    ContDiff ℝ 2 (resolventPhase (d := d) a rho) := by
  unfold resolventPhase PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The resolvent barrier is globally twice continuously differentiable. -/
theorem contDiff_resolventBarrier   :
    ContDiff ℝ 2 (resolventBarrier (d := d) a rho) := by
  unfold resolventBarrier
  exact (contDiff_resolventPhase a rho).cosh

private theorem fderiv_resolventPhase_apply
    (z w : TimeVelocity d) :
    fderiv ℝ (resolventPhase a rho) z w =
      a * Real.sqrt rho * (2 * PDE.vecDot z.2 w.2 - w.1) := by
  unfold resolventPhase
  rw [fderiv_const_mul (by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop) (a * Real.sqrt rho)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.sub_apply]
  rw [fderiv_vecNormSq_snd_apply, _root_.HypoellipticAleksandrov.Parabolic.fderiv_timeCoordinate_apply]

private theorem fderiv_resolventPhaseDirection_apply
     (w₂ z w₁ : TimeVelocity d) :
    fderiv ℝ
        (fun y : TimeVelocity d =>
          a * Real.sqrt rho *
            (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) z w₁ =
      2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2 := by
  have hdot : DifferentiableAt ℝ
      (fun y : TimeVelocity d => PDE.vecDot y.2 w₂.2) z := by
    unfold PDE.vecDot
    fun_prop
  rw [fderiv_const_mul ((hdot.const_mul 2).sub_const w₂.1)
    (a * Real.sqrt rho)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_fun_sub (hdot.const_mul 2) (differentiableAt_const w₂.1)]
  simp only [fderiv_const_apply, sub_zero]
  rw [fderiv_const_mul hdot 2]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_vecDot_snd_apply]
  ring

private theorem fderiv_resolventBarrier_apply
    (z w : TimeVelocity d) :
    fderiv ℝ (resolventBarrier a rho) z w =
      Real.sinh (resolventPhase a rho z) *
        (a * Real.sqrt rho * (2 * PDE.vecDot z.2 w.2 - w.1)) := by
  unfold resolventBarrier
  rw [fderiv_cosh
    ((contDiff_resolventPhase a rho).differentiable (by norm_num) z)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_resolventPhase_apply]

/-- The resolvent barrier has the exact negative time derivative. -/
theorem timeDerivative_resolventBarrier
    (z : TimeVelocity d) :
    timeDerivative (resolventBarrier a rho) z =
      -(a * Real.sqrt rho) * Real.sinh (resolventPhase a rho z) := by
  simp_all [timeDerivative, fderiv_resolventBarrier_apply, PDE.vecDot] <;> ring

private theorem fderiv_fderiv_resolventBarrier_apply
     (z w₁ w₂ : TimeVelocity d) :
    fderiv ℝ (fderiv ℝ (resolventBarrier a rho)) z w₁ w₂ =
      Real.cosh (resolventPhase a rho z) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₁.2 - w₁.1)) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₂.2 - w₂.1)) +
        Real.sinh (resolventPhase a rho z) *
          (2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2) := by
  let p : TimeVelocity d → ℝ := resolventPhase a rho
  let phi : TimeVelocity d → ℝ := resolventBarrier a rho
  have hp : ContDiff ℝ 2 p := contDiff_resolventPhase a rho
  have hphi : ContDiff ℝ 2 phi := contDiff_resolventBarrier a rho


  have hEvalAt := congrArg
    (fun L : TimeVelocity d →L[ℝ] ℝ => L w₁) (by
        simpa only [ContinuousLinearMap.comp_zero, zero_add] using
          ((((hphi.fderiv_right (m := 1) (by norm_num)).differentiable_one) z).hasFDerivAt.clm_apply
            (hasFDerivAt_const w₂ z)).fderiv)
  simp only [ContinuousLinearMap.flip_apply] at hEvalAt
  have hfun :
      (fun y  => fderiv ℝ phi y w₂) =
        fun y =>
          Real.sinh (p y) *
            (a * Real.sqrt rho *
              (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) := by
    funext y
    exact fderiv_resolventBarrier_apply a rho y w₂
  have hphaseDiff  :=
    hp.differentiable (by norm_num) z
  have hleft  :=
    hphaseDiff.sinh

  calc
    fderiv ℝ (fderiv ℝ (resolventBarrier a rho)) z w₁ w₂ =
        fderiv ℝ (fun y => fderiv ℝ phi y w₂) z w₁ := (id (Eq.symm hEvalAt))
    _ = fderiv ℝ
        (fun y =>
          Real.sinh (p y) *
            (a * Real.sqrt rho *
              (2 * PDE.vecDot y.2 w₂.2 - w₂.1))) z w₁ := by
      rw [hfun]
    _ = Real.cosh (resolventPhase a rho z) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₁.2 - w₁.1)) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₂.2 - w₂.1)) +
        Real.sinh (resolventPhase a rho z) *
          (2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2) := by
      rw [fderiv_fun_mul hleft (show _ by
          unfold PDE.vecDot
          fun_prop)]
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_resolventPhaseDirection_apply]
      rw [fderiv_sinh hphaseDiff]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_resolventPhase_apply]
      simp only [p]
      ring

/-- The exact velocity Hessian of the resolvent barrier. -/
theorem velocityHessian_resolventBarrier
    (z : TimeVelocity d) :
    velocityHessian (resolventBarrier a rho) z =
      (2 * (a * Real.sqrt rho) *
          Real.sinh (resolventPhase a rho z)) • (1 : PDE.Mat d) +
        (4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z)) •
            Matrix.vecMulVec z.2 z.2 := by
  classical
  ext i j
  unfold velocityHessian
  rw [fderiv_fderiv_resolventBarrier_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [PDE.vecDot, Pi.single_apply]
    ring
  ·
    simp [PDE.vecDot, Pi.single_apply, hij, (Ne.symm hij)]
    ring

variable (A : PDE.Mat d)

/-- Contraction with the identity matrix is the matrix trace. -/
alias matrixContraction_one_eq_trace := _root_.HypoellipticAleksandrov.KineticAleksandrov.Decay.contraction_one


/-- Contraction with `v vᵀ` is the quadratic form of the left matrix. -/
theorem matrixContraction_vecMulVec_eq_vecDot_mulVec
     (v : PDE.Vec d) :
    matrixContraction A (Matrix.vecMulVec v v) =
      PDE.vecDot v (A *ᵥ v) := by
  classical
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The exact contraction of a coefficient matrix with the barrier Hessian. -/
theorem matrixContraction_velocityHessian_resolventBarrier
     (a rho : ℝ) (z : TimeVelocity d) :
    matrixContraction A (velocityHessian (resolventBarrier a rho) z) =
      2 * (a * Real.sqrt rho) *
          Real.sinh (resolventPhase a rho z) * A.trace +
        4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z) *
            PDE.vecDot z.2 (A *ᵥ z.2) := by
  simp_all [velocityHessian_resolventBarrier, matrixContraction_one_eq_trace, matrixContraction_vecMulVec_eq_vecDot_mulVec]

/-- The exact project-sign resolvent expression for the barrier. -/
theorem parabolicOperator_add_resolvent_resolventBarrier
    (A : CoefficientField d) (a rho : ℝ) (z : TimeVelocity d) :
    parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z =
      rho * Real.cosh (resolventPhase a rho z) -
        (a * Real.sqrt rho) * Real.sinh (resolventPhase a rho z) *
          (1 + 2 * (coefficientAt A z).trace) -
        4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z) *
            PDE.vecDot z.2 ((coefficientAt A z) *ᵥ z.2) := by
  simp_all [timeDerivative_resolventBarrier, matrixContraction_velocityHessian_resolventBarrier, resolventBarrier] <;> ring

/-- An upper Loewner bound gives the corresponding quadratic-form bound. -/
theorem vecDot_mulVec_le_of_loewner_upper
    {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) (v : PDE.Vec d) :
    PDE.vecDot v (A *ᵥ v) ≤ Lam * PDE.vecNormSq v := (_sharedProof_383_0 hupper v)


/-- A positive lower Loewner bound makes the matrix trace nonnegative. -/
theorem trace_nonneg_of_loewner_lower
    {lam : ℝ} {A : PDE.Mat d} (hlam : 0 < lam)
    (hlower : lam • (1 : PDE.Mat d) ≤ A) :
    0 ≤ A.trace := (HypoellipticAleksandrov.posDef_of_loewner_lower hlam hlower).posSemidef.trace_nonneg

/-- An upper Loewner bound controls the matrix trace by dimension times its bound. -/
theorem trace_le_natCast_mul_of_loewner_upper
    {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) :
    A.trace ≤ (d : ℝ) * Lam := by

  have htrace := (Matrix.le_iff.mp hupper).trace_nonneg
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htrace
  nlinarith

/-- The squared Euclidean norm in the open unit coordinate cube is at most the dimension. -/
theorem vecNormSq_le_natCast_of_mem_unit_velocityCube
    {v : PDE.Vec d} (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    PDE.vecNormSq v ≤ (d : ℝ) := by
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, v i ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi

      have hsquare :=
        (sq_le_sq₀ (abs_nonneg (v i)) zero_le_one).mpr (show |v i| < 1 by
            simpa only [Pi.zero_apply, sub_zero] using hv i).le
      simpa only [sq_abs, one_pow] using hsquare
    _ = (d : ℝ) := by norm_num

private theorem resolvent_witness_pos {D Lam : ℝ}
    (hD : 0 ≤ D) (hLam : 0 ≤ Lam) :
    let C := 1 + 2 * D * Lam
    let a := 1 / (8 * C)
    0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam) := by
  dsimp only
  let C := 1 + 2 * D * Lam
  let a := 1 / (8 * C)
  change 0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam)
  have hX  := mul_nonneg hD hLam



  have haC : a * C = 1 / 8 := by
    dsimp only [a]
    field_simp [(ne_of_gt (show 0 < C by
        dsimp only [C]
        nlinarith))]

  have hscaled  :=
    mul_le_mul_of_nonneg_left (show D * Lam ≤ C ^ 2 by
        dsimp only [C]
        nlinarith [sq_nonneg (D * Lam)]) (sq_nonneg a)
  have ha2C2 : a ^ 2 * C ^ 2 = 1 / 64 := by
    calc
      a ^ 2 * C ^ 2 = (a * C) ^ 2 := by ring
      _ = (1 / 8 : ℝ) ^ 2 := by rw [haC]
      _ = 1 / 64 := by norm_num

  constructor
  · exact (by
      dsimp only [a]
      positivity)
  · rw [haC]
    nlinarith

private theorem resolvent_scalar_expression_pos
    {a rho C X tr q s : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hrho : 1 < rho)
    (htr : 0 ≤ tr) (htrC : 1 + 2 * tr ≤ C) (hqX : q ≤ X)
    (hcoef : 0 < 1 - a * C - 4 * a ^ 2 * X) :
    0 < rho * Real.cosh s -
        (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
      4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := by
  let sharedTerm_435ba0873d := (rho * Real.cosh s - a * rho * Real.cosh s * C - 4 * a ^ 2 * rho * Real.cosh s * X)
  have hrhoPos  := lt_trans zero_lt_one hrho


  have hphi  := Real.cosh_pos s


  have hsinhTerm :
      (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) <
        (a * Real.sqrt rho) * Real.cosh s * C := by
    simpa only [mul_assoc] using
      mul_lt_mul_of_pos_left (by
          calc
            Real.sinh s * (1 + 2 * tr) <
                Real.cosh s * (1 + 2 * tr) :=
              mul_lt_mul_of_pos_right (Real.sinh_lt_cosh s) (by nlinarith)
            _ ≤ Real.cosh s * C :=
              mul_le_mul_of_nonneg_left htrC hphi.le) (mul_pos ha (Real.sqrt_pos.2 hrhoPos))

  have hquadTerm  :=
    mul_le_mul_of_nonneg_left hqX (show 0 ≤ 4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s by
        positivity)


  have hphiC  := mul_nonneg hphi.le hC.le
  have hkTerm :
      (a * Real.sqrt rho) * Real.cosh s * C ≤
        a * rho * Real.cosh s * C := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show Real.sqrt rho < rho by
          rw [Real.sqrt_lt' hrhoPos]
          nlinarith).le ha.le) hphiC
  have hkSq : (a * Real.sqrt rho) ^ 2 = a ^ 2 * rho := by
    rw [mul_pow, Real.sq_sqrt hrhoPos.le]


  have hpositive  :=
    mul_pos (mul_pos hrhoPos hphi) hcoef
  calc
    0 < rho * Real.cosh s * (1 - a * C - 4 * a ^ 2 * X) := hpositive
    _ = sharedTerm_435ba0873d := by ring
    _ ≤ rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.cosh s * C -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X := (show sharedTerm_435ba0873d ≤
        rho * Real.cosh s -
            (a * Real.sqrt rho) * Real.cosh s * C -
          4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X by
            rw [hkSq]
            nlinarith)
    _ < rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := (show rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.cosh s * C -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X <
      rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q by
            nlinarith)

/-- There is a positive resolvent-barrier parameter, chosen only from the
dimension and ellipticity constants, for which the project-sign resolvent
expression is strictly positive at every point in the unit velocity cube
obeying the two pointwise Loewner bounds. -/
theorem exists_resolventBarrier_strict_sign_of_mem_velocityCube {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ a > 0, ∀ rho > 1, ∀ A : CoefficientField d, ∀ z,
      z.2 ∈ velocityCube 0 1 →
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z →
      coefficientAt A z ≤ Lam • (1 : PDE.Mat d) →
      0 < parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z := by
  let D : ℝ := d
  let C : ℝ := 1 + 2 * D * Lam
  let a : ℝ := 1 / (8 * C)

  have hLam  := lt_of_lt_of_le hlam hlamLam
  have hwitness := resolvent_witness_pos (show 0 ≤ D by positivity) hLam.le
  change 0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam) at hwitness
  obtain ⟨ha, hcoef⟩ := hwitness
  refine ⟨a, ha, ?_⟩
  intro rho hrho A z hzVelocity hlower hupper
  let M  := coefficientAt A z
  have htraceNonneg  := trace_nonneg_of_loewner_lower hlam hlower
  have htraceUpper : M.trace ≤ D * Lam := by
    exact trace_le_natCast_mul_of_loewner_upper hupper




  rw [parabolicOperator_add_resolvent_resolventBarrier]
  exact resolvent_scalar_expression_pos ha (show 0 < C by
      dsimp only [C]
      positivity) hrho htraceNonneg
    (show 1 + 2 * M.trace ≤ C by
        dsimp only [C]
        nlinarith) (by
            calc
              PDE.vecDot z.2 (M *ᵥ z.2) ≤ Lam * PDE.vecNormSq z.2 :=
                vecDot_mulVec_le_of_loewner_upper hupper z.2
              _ ≤ Lam * D := mul_le_mul_of_nonneg_left (by
                  exact vecNormSq_le_natCast_of_mem_unit_velocityCube hzVelocity) hLam.le
              _ = D * Lam := mul_comm _ _) hcoef

end HypoellipticAleksandrov.Parabolic
