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
public import HypoellipticAleksandrov.Parabolic.HarnackABP
public import HypoellipticAleksandrov.Measure.SourceDensityNearOneMeasure
public import HypoellipticAleksandrov.Parabolic.DensityNearOneGeometry
public import HypoellipticAleksandrov.Parabolic.SourceDensityToPoint
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Matrix Set Filter MeasureTheory
open scoped BigOperators MatrixOrder Topology


/-- The scalar phase of the Krylov--Safonov resolvent barrier. -/
def resolventPhase {d : ℕ} (a rho : ℝ) (z : TimeVelocity d) : ℝ :=
  a * Real.sqrt rho * (PDE.vecNormSq z.2 - z.1)

/-- The hyperbolic-cosine resolvent barrier. -/
def resolventBarrier {d : ℕ} (a rho : ℝ) : TimeVelocity d → ℝ :=
  fun z => Real.cosh (resolventPhase a rho z)

private theorem fderiv_timeCoordinate_apply {d : ℕ}
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.1) z w = w.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ)).fderiv]
  rfl

private theorem fderiv_velocityCoordinate_apply {d : ℕ} (i : Fin d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.2 i) z w = w.2 i := by
  have h :=
    (hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd (𝕜 := ℝ))
  change (fderiv ℝ ((fun f => f i) ∘ Prod.snd) z) w = w.2 i
  rw [h.fderiv]
  rfl

private theorem fderiv_vecDot_snd_apply {d : ℕ} (q : PDE.Vec d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => PDE.vecDot y.2 q) z w =
      PDE.vecDot w.2 q := by
  classical
  unfold PDE.vecDot
  have hsum :
      fderiv ℝ (fun y => ∑ i, y.2 i * q i) z =
        ∑ i, fderiv ℝ (fun y => y.2 i * q i) z :=
    fderiv_fun_sum fun i _ => by fun_prop
  rw [hsum]
  simp
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_mul_const (by fun_prop) (q i)]
  simp
  rw [fderiv_velocityCoordinate_apply]
  ring

private theorem fderiv_vecNormSq_snd_apply {d : ℕ}
    (z w : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => PDE.vecNormSq y.2) z w =
      2 * PDE.vecDot z.2 w.2 := by
  classical
  unfold PDE.vecNormSq PDE.vecDot
  have hsum :
      fderiv ℝ (fun y => ∑ i, y.2 i * y.2 i) z =
        ∑ i, fderiv ℝ (fun y => y.2 i * y.2 i) z :=
    fderiv_fun_sum fun i _ => by fun_prop
  rw [hsum]
  simp
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp
  rw [fderiv_velocityCoordinate_apply]
  ring

private theorem contDiff_resolventPhase {d : ℕ} (a rho : ℝ) :
    ContDiff ℝ 2 (resolventPhase (d := d) a rho) := by
  unfold resolventPhase PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The resolvent barrier is globally twice continuously differentiable. -/
theorem contDiff_resolventBarrier {d : ℕ} (a rho : ℝ) :
    ContDiff ℝ 2 (resolventBarrier (d := d) a rho) := by
  unfold resolventBarrier
  exact (contDiff_resolventPhase a rho).cosh

private theorem fderiv_resolventPhase_apply {d : ℕ} (a rho : ℝ)
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
  rw [fderiv_vecNormSq_snd_apply, fderiv_timeCoordinate_apply]


private theorem fderiv_resolventBarrier_apply {d : ℕ} (a rho : ℝ)
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
theorem timeDerivative_resolventBarrier {d : ℕ} (a rho : ℝ)
    (z : TimeVelocity d) :
    timeDerivative (resolventBarrier a rho) z =
      -(a * Real.sqrt rho) * Real.sinh (resolventPhase a rho z) := by
  unfold timeDerivative
  rw [fderiv_resolventBarrier_apply]
  simp [PDE.vecDot]
  ring


/-- The exact velocity Hessian of the resolvent barrier. -/
theorem velocityHessian_resolventBarrier {d : ℕ} (a rho : ℝ)
    (z : TimeVelocity d) :
    velocityHessian (resolventBarrier a rho) z =
      (2 * (a * Real.sqrt rho) *
          Real.sinh (resolventPhase a rho z)) • (1 : PDE.Mat d) +
        (4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z)) •
            Matrix.vecMulVec z.2 z.2  := by
  have fderiv_fderiv_resolventBarrier_apply (a : ℝ) (rho : ℝ) (z w₁ w₂ : TimeVelocity d) :
      fderiv ℝ (fderiv ℝ (resolventBarrier a rho)) z w₁ w₂ =
      Real.cosh (resolventPhase a rho z) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₁.2 - w₁.1)) *
          (a * Real.sqrt rho *
            (2 * PDE.vecDot z.2 w₂.2 - w₂.1)) +
        Real.sinh (resolventPhase a rho z) *
          (2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2) := by
    have fderiv_resolventPhaseDirection_apply (a : ℝ) (rho : ℝ) (w₂ z w₁ : TimeVelocity d) :
        fderiv ℝ
          (fun y =>
            a * Real.sqrt rho *
              (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) z w₁ =
        2 * (a * Real.sqrt rho) * PDE.vecDot w₁.2 w₂.2 := by
      have hdot : DifferentiableAt ℝ
          (fun y => PDE.vecDot y.2 w₂.2) z := by
        unfold PDE.vecDot
        fun_prop
      rw [fderiv_const_mul ((hdot.const_mul 2).sub_const w₂.1)
        (a * Real.sqrt rho)]
      simp
      rw [fderiv_fun_sub (hdot.const_mul 2) (differentiableAt_const w₂.1)]
      simp
      rw [fderiv_const_mul hdot 2]
      simp
      rw [fderiv_vecDot_snd_apply]
      ring
    let p : TimeVelocity d → ℝ := resolventPhase a rho
    let phi : TimeVelocity d → ℝ := resolventBarrier a rho
    have hp : ContDiff ℝ 2 p := contDiff_resolventPhase a rho
    have hphi : ContDiff ℝ 2 phi := contDiff_resolventBarrier a rho
    have hEval :
        fderiv ℝ (fun y => fderiv ℝ phi y w₂) z =
          (fderiv ℝ (fderiv ℝ phi) z).flip w₂ := by
      simpa using
        ((((hphi.fderiv_right (by norm_num)).differentiable_one) z).hasFDerivAt.clm_apply
          (hasFDerivAt_const w₂ z)).fderiv
    have hEvalAt := congrArg
      (fun L => L w₁) hEval
    simp at hEvalAt
    have hfun :
        (fun y => fderiv ℝ phi y w₂) =
          fun y =>
            Real.sinh (p y) *
              (a * Real.sqrt rho *
                (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) := by
      funext y
      simpa using fderiv_resolventBarrier_apply a rho y w₂
    have hphaseDiff :=
      hp.differentiable (by norm_num) z
    have hright : DifferentiableAt ℝ
        (fun y =>
          a * Real.sqrt rho *
            (2 * PDE.vecDot y.2 w₂.2 - w₂.1)) z := by
      unfold PDE.vecDot
      fun_prop
    calc
      fderiv ℝ (fderiv ℝ (resolventBarrier a rho)) z w₁ w₂ =
          fderiv ℝ (fun y => fderiv ℝ phi y w₂) z w₁ := by
        simpa using hEvalAt.symm
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
        rw [fderiv_fun_mul hphaseDiff.sinh hright]
        simp
        rw [fderiv_resolventPhaseDirection_apply]
        rw [fderiv_sinh hphaseDiff]
        simp [ContinuousLinearMap.smul_apply]
        rw [fderiv_resolventPhase_apply]
        simp only [p]
        ring
  classical
  ext i j
  unfold velocityHessian
  rw [fderiv_fderiv_resolventBarrier_apply]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  by_cases hij : i = j
  · subst j
    simp [PDE.vecDot, Pi.single_apply]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [PDE.vecDot, Pi.single_apply, hij, hji]
    ring

/-- Contraction with the identity matrix is the matrix trace. -/
theorem matrixContraction_one_eq_trace {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A 1 = A.trace := by
  classical
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

/-- Contraction with `v vᵀ` is the quadratic form of the left matrix. -/
theorem matrixContraction_vecMulVec_eq_vecDot_mulVec {d : ℕ}
    (A : PDE.Mat d) (v : PDE.Vec d) :
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
theorem matrixContraction_velocityHessian_resolventBarrier {d : ℕ}
    (A : PDE.Mat d) (a rho : ℝ) (z : TimeVelocity d) :
    matrixContraction A (velocityHessian (resolventBarrier a rho) z) =
      2 * (a * Real.sqrt rho) *
          Real.sinh (resolventPhase a rho z) * A.trace +
        4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z) *
            PDE.vecDot z.2 (A *ᵥ z.2) := by
  rw [velocityHessian_resolventBarrier,
    matrixContraction_add_right, matrixContraction_smul_right,
    matrixContraction_smul_right, matrixContraction_one_eq_trace,
    matrixContraction_vecMulVec_eq_vecDot_mulVec]

/-- The exact project-sign resolvent expression for the barrier. -/
theorem parabolicOperator_add_resolvent_resolventBarrier {d : ℕ}
    (A : CoefficientField d) (a rho : ℝ) (z : TimeVelocity d) :
    parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z =
      rho * Real.cosh (resolventPhase a rho z) -
        (a * Real.sqrt rho) * Real.sinh (resolventPhase a rho z) *
          (1 + 2 * (coefficientAt A z).trace) -
        4 * (a * Real.sqrt rho) ^ 2 *
          Real.cosh (resolventPhase a rho z) *
            PDE.vecDot z.2 ((coefficientAt A z) *ᵥ z.2) := by
  rw [parabolicOperator_apply, timeDerivative_resolventBarrier,
    matrixContraction_velocityHessian_resolventBarrier]
  simp only [resolventBarrier]
  ring

/-- An upper Loewner bound gives the corresponding quadratic-form bound. -/
theorem vecDot_mulVec_le_of_loewner_upper {d : ℕ}
    {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) (v : PDE.Vec d) :
    PDE.vecDot v (A *ᵥ v) ≤ Lam * PDE.vecNormSq v := by
  have hquad := (Matrix.le_iff.mp hupper).dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using
    sub_nonneg.mp hquad

/-- A positive lower Loewner bound makes the matrix trace nonnegative. -/
theorem trace_nonneg_of_loewner_lower {d : ℕ}
    {lam : ℝ} {A : PDE.Mat d} (hlam : 0 < lam)
    (hlower : lam • (1 : PDE.Mat d) ≤ A) :
    0 ≤ A.trace := by
  exact (HypoellipticAleksandrov.posDef_of_loewner_lower hlam hlower).posSemidef.trace_nonneg

/-- An upper Loewner bound controls the matrix trace by dimension times its bound. -/
theorem trace_le_natCast_mul_of_loewner_upper {d : ℕ}
    {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) :
    A.trace ≤ (d : ℝ) * Lam := by
  have htrace := (Matrix.le_iff.mp hupper).trace_nonneg
  simp [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at htrace
  nlinarith

/-- The squared Euclidean norm in the open unit coordinate cube is at most the dimension. -/
theorem vecNormSq_le_natCast_of_mem_unit_velocityCube {d : ℕ}
    {v : PDE.Vec d} (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    PDE.vecNormSq v ≤ (d : ℝ) := by
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, v i ^ 2 ≤ ∑ _i : Fin d, 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      have habs : |v i| < 1 := by
        simpa using hv i
      simpa [one_pow] using ((sq_le_sq₀ (abs_nonneg (v i)) zero_le_one).mpr habs.le)
    _ = (d : ℝ) := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem resolvent_witness_pos {D Lam : ℝ}
    (hD : 0 ≤ D) (hLam : 0 ≤ Lam) :
    let C := 1 + 2 * D * Lam
    let a := 1 / (8 * C)
    0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam) := by
  dsimp only
  let C := 1 + 2 * D * Lam
  let a := 1 / (8 * C)
  change 0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam)
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have haC : a * C = 1 / 8 := by
    dsimp only [a]
    field_simp [(ne_of_gt hC)]
  have hXC2 : D * Lam ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith [sq_nonneg (D * Lam)]
  have ha2C2 : a ^ 2 * C ^ 2 = 1 / 64 := by
    calc
      a ^ 2 * C ^ 2 = (a * C) ^ 2 := by ring
      _ = (1 / 8 : ℝ) ^ 2 := by rw [haC]
      _ = 1 / 64 := by norm_num
  have hsmall : 4 * a ^ 2 * (D * Lam) ≤ 1 / 16 := by
    nlinarith
  constructor
  · exact ha
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
  have hrhoPos := lt_trans zero_lt_one hrho
  have hkPos := mul_pos ha (Real.sqrt_pos.2 hrhoPos)
  have hphi := Real.cosh_pos s
  have hT : 0 < 1 + 2 * tr := by nlinarith
  have hsinhTrace :
      Real.sinh s * (1 + 2 * tr) < Real.cosh s * C := by
    calc
      Real.sinh s * (1 + 2 * tr) <
          Real.cosh s * (1 + 2 * tr) :=
        mul_lt_mul_of_pos_right (Real.sinh_lt_cosh s) hT
      _ ≤ Real.cosh s * C :=
        mul_le_mul_of_nonneg_left htrC hphi.le
  have hsinhTerm :
      (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) <
        (a * Real.sqrt rho) * Real.cosh s * C := by
    simpa only [mul_assoc] using
      mul_lt_mul_of_pos_left hsinhTrace hkPos
  have hquadFactor :
      0 ≤ 4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s := by
    positivity
  have hsqrtLt : Real.sqrt rho < rho := by
    rw [Real.sqrt_lt' hrhoPos]
    nlinarith
  have hkTerm :
      (a * Real.sqrt rho) * Real.cosh s * C ≤
        a * rho * Real.cosh s * C := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtLt.le ha.le) (mul_nonneg hphi.le hC.le)
  have hkSq : (a * Real.sqrt rho) ^ 2 = a ^ 2 * rho := by
    rw [mul_pow, Real.sq_sqrt hrhoPos.le]
  have hlower :
      rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.cosh s * C -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X <
      rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := by
    nlinarith
  have hlower' :
      rho * Real.cosh s - a * rho * Real.cosh s * C -
          4 * a ^ 2 * rho * Real.cosh s * X ≤
        rho * Real.cosh s -
            (a * Real.sqrt rho) * Real.cosh s * C -
          4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X := by
    rw [hkSq]
    nlinarith
  calc
    0 < rho * Real.cosh s * (1 - a * C - 4 * a ^ 2 * X) := (mul_pos (mul_pos hrhoPos hphi) hcoef)
    _ = rho * Real.cosh s - a * rho * Real.cosh s * C -
        4 * a ^ 2 * rho * Real.cosh s * X := by ring
    _ ≤ rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.cosh s * C -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * X := hlower'
    _ < rho * Real.cosh s -
          (a * Real.sqrt rho) * Real.sinh s * (1 + 2 * tr) -
        4 * (a * Real.sqrt rho) ^ 2 * Real.cosh s * q := hlower




/-- The resolvent barrier translated to the terminal point `(1, v0)`. -/
def translatedResolventBarrier {d : ℕ} (a rho : ℝ) (v0 : PDE.Vec d)
    (z : TimeVelocity d) : ℝ :=
  resolventBarrier a rho (z.1 - 1, z.2 - v0)

/-- The translated resolvent barrier normalized by its forward-boundary cosh
factor. -/
def normalizedTranslatedResolventBarrier {d : ℕ} (a rho : ℝ) (v0 : PDE.Vec d)
    (z : TimeVelocity d) : ℝ :=
  translatedResolventBarrier a rho v0 z / Real.cosh (a * Real.sqrt rho / 4)

/-- Translation from the terminal centre to the resolvent barrier coordinates. -/
def terminalTranslation {d : ℕ} (v0 : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z => z - (1, v0)

private theorem translatedResolventBarrier_eq_comp {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) :
    translatedResolventBarrier a rho v0 =
      resolventBarrier a rho ∘ terminalTranslation v0 := rfl


private theorem fderiv_terminalTranslation {d : ℕ} (v0 : PDE.Vec d)
    (z : TimeVelocity d) :
    fderiv ℝ (terminalTranslation v0) z = 1 := by
  exact ((hasFDerivAt_id z).sub_const (1, v0)).fderiv

/-- The translated resolvent barrier is globally twice continuously
differentiable. -/
theorem contDiff_translatedResolventBarrier {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) :
    ContDiff ℝ 2 (translatedResolventBarrier a rho v0)  := by
  have contDiff_terminalTranslation :
      ContDiff ℝ 2 (terminalTranslation v0) := by
    exact contDiff_id.sub contDiff_const
  rw [translatedResolventBarrier_eq_comp]
  exact (contDiff_resolventBarrier a rho).comp (contDiff_terminalTranslation)

/-- The normalized translated resolvent barrier is globally twice continuously
differentiable. -/
theorem contDiff_normalizedTranslatedResolventBarrier {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) :
    ContDiff ℝ 2 (normalizedTranslatedResolventBarrier a rho v0) := by
  unfold normalizedTranslatedResolventBarrier
  exact (contDiff_translatedResolventBarrier a rho v0).div_const _

private theorem fderiv_translatedResolventBarrier {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) (z : TimeVelocity d) :
    fderiv ℝ (translatedResolventBarrier a rho v0) z =
      fderiv ℝ (resolventBarrier a rho) (terminalTranslation v0 z) := by
  rw [translatedResolventBarrier_eq_comp]
  have hbar := (contDiff_resolventBarrier a rho).differentiable (by norm_num)
    (terminalTranslation v0 z)
  have hcomp := hbar.hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (1, v0))
  simpa [fderiv_terminalTranslation, ContinuousLinearMap.comp_id] using hcomp.fderiv

private theorem fderiv_fderiv_translatedResolventBarrier {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) (z w1 w2 : TimeVelocity d) :
    fderiv ℝ (fderiv ℝ (translatedResolventBarrier a rho v0)) z w1 w2 =
      fderiv ℝ (fderiv ℝ (resolventBarrier a rho))
        (terminalTranslation v0 z) w1 w2 := by
  have hfirst : fderiv ℝ (translatedResolventBarrier a rho v0) =
      fun x => fderiv ℝ (resolventBarrier a rho) (terminalTranslation v0 x) := by
    funext x
    exact fderiv_translatedResolventBarrier a rho v0 x
  rw [hfirst]
  have hbar := ((contDiff_resolventBarrier a rho).fderiv_right
    (by norm_num)).differentiable_one (terminalTranslation v0 z)
  have hcomp := hbar.hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (1, v0))
  simpa [Function.comp_def, fderiv_terminalTranslation, ContinuousLinearMap.comp_id] using (congrArg (fun L => L w1 w2) hcomp.fderiv)

private theorem timeDerivative_translatedResolventBarrier {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) (z : TimeVelocity d) :
    timeDerivative (translatedResolventBarrier a rho v0) z =
      timeDerivative (resolventBarrier a rho) (terminalTranslation v0 z) := by
  unfold timeDerivative
  rw [fderiv_translatedResolventBarrier]

private theorem velocityHessian_translatedResolventBarrier {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) (z : TimeVelocity d) :
    velocityHessian (translatedResolventBarrier a rho v0) z =
      velocityHessian (resolventBarrier a rho) (terminalTranslation v0 z) := by
  ext i j
  unfold velocityHessian
  exact fderiv_fderiv_translatedResolventBarrier a rho v0 z
    (0, Pi.single i 1) (0, Pi.single j 1)



/-- Exact translation of the project operator to the coefficient matrix at
the original point. -/
theorem parabolicOperator_translatedResolventBarrier {d : ℕ}
    (A : CoefficientField d) (a rho : ℝ) (v0 : PDE.Vec d) (z : TimeVelocity d) :
    parabolicOperator A (translatedResolventBarrier a rho v0) z =
      parabolicOperator (fun _ _ => coefficientAt A z) (resolventBarrier a rho)
        (terminalTranslation v0 z) := by
  rw [parabolicOperator_apply, parabolicOperator_apply,
    timeDerivative_translatedResolventBarrier,
    velocityHessian_translatedResolventBarrier]
  rfl

/-- Exact normalization of the translated resolvent operator. -/
theorem parabolicOperator_add_resolvent_normalizedTranslatedResolventBarrier
    {d : ℕ} (A : CoefficientField d) (a rho : ℝ) (v0 : PDE.Vec d)
    (z : TimeVelocity d) :
    parabolicOperator A (normalizedTranslatedResolventBarrier a rho v0) z +
        rho * normalizedTranslatedResolventBarrier a rho v0 z =
      (Real.cosh (a * Real.sqrt rho / 4))⁻¹ *
        (parabolicOperator (fun _ _ => coefficientAt A z) (resolventBarrier a rho)
          (terminalTranslation v0 z) +
          rho * resolventBarrier a rho (terminalTranslation v0 z))   := by
  have velocityHessian_div_const {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ) (z : TimeVelocity d) :
      velocityHessian (fun x => u x / c) z = c⁻¹ • velocityHessian u z := by
    have hfirst : fderiv ℝ (fun x => c⁻¹ * u x) =
        fun x => c⁻¹ • fderiv ℝ u x := by
      funext x
      simpa using fderiv_const_mul (hu.differentiable (by norm_num) x) c⁻¹
    ext i j
    rw [Matrix.smul_apply]
    unfold velocityHessian
    rw [show (fun x => u x / c) = fun x => c⁻¹ * u x by
      funext x; ring, hfirst]
    have hscaled :
        fderiv ℝ (fun x => c⁻¹ • fderiv ℝ u x) z = c⁻¹ • fderiv ℝ (fderiv ℝ u) z :=
      (((hu.fderiv_right (by norm_num)).differentiable_one z).hasFDerivAt.const_smul c⁻¹).fderiv
    rw [hscaled]
    simp [_root_.smul_apply]
  have timeDerivative_div_const {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ) (z : TimeVelocity d) :
      timeDerivative (fun x => u x / c) z = timeDerivative u z / c := by
    unfold timeDerivative
    rw [show (fun x => u x / c) = fun x => c⁻¹ * u x by
      funext x; ring]
    rw [fderiv_const_mul (hu.differentiable (by norm_num) z)]
    simp [_root_.smul_apply]
    ring
  let c : ℝ := Real.cosh (a * Real.sqrt rho / 4)
  have hcont := contDiff_translatedResolventBarrier a rho v0
  change parabolicOperator A (fun x => translatedResolventBarrier a rho v0 x / c) z +
      rho * (translatedResolventBarrier a rho v0 z / c) = _
  rw [parabolicOperator_apply, timeDerivative_div_const
    (hcont.of_le (by norm_num)), velocityHessian_div_const hcont]
  calc
    _ = c⁻¹ * (parabolicOperator A (translatedResolventBarrier a rho v0) z +
        rho * translatedResolventBarrier a rho v0 z) := by
      rw [matrixContraction_smul_right, parabolicOperator_apply]
      ring
    _ = c⁻¹ *
        (parabolicOperator (fun _ _ => coefficientAt A z) (resolventBarrier a rho)
          (terminalTranslation v0 z) +
          rho * resolventBarrier a rho (terminalTranslation v0 z)) := by
      rw [parabolicOperator_translatedResolventBarrier,
        translatedResolventBarrier_eq_comp]
      simp only [Function.comp_apply]
    _ = _ := rfl

/-- The translated normalized barrier has the exact reciprocal-cosh value at
its terminal centre. -/
theorem normalizedTranslatedResolventBarrier_target {d : ℕ}
    (a rho : ℝ) (v0 : PDE.Vec d) :
    normalizedTranslatedResolventBarrier a rho v0 (1, v0) =
      (Real.cosh (a * Real.sqrt rho / 4))⁻¹ := by
  simp [normalizedTranslatedResolventBarrier, translatedResolventBarrier,
    resolventBarrier, resolventPhase, PDE.vecNormSq, PDE.vecDot]


private theorem resolventPhase_localABPAffine {d : ℕ} (a rho : ℝ)
    (v0 : PDE.Vec d) (w : TimeVelocity d) :
    resolventPhase a rho (terminalTranslation v0 (localABPAffine v0 w)) =
      (a * Real.sqrt rho / 4) * (PDE.vecNormSq w.2 + 1 - w.1) := by
  unfold resolventPhase terminalTranslation localABPAffine parabolicAffine
  simp [PDE.vecNormSq_smul]
  ring

private theorem one_le_normalizedTranslatedResolventBarrier_localABPAffine
    {d : ℕ} {a rho : ℝ} {v0 : PDE.Vec d} (w : TimeVelocity d)
    (ha : 0 < a) (hrho : 1 < rho)
    (hbracketFinal : 1 ≤ PDE.vecNormSq w.2 + 1 - w.1) :
    1 ≤ normalizedTranslatedResolventBarrier a rho v0 (localABPAffine v0 w) := by
  have hsqrt := Real.sqrt_pos.2 (lt_trans zero_lt_one hrho)
  have hfactor : 0 ≤ a * Real.sqrt rho / 4 := by positivity
  have harg :=
    calc
      a * Real.sqrt rho / 4 = (a * Real.sqrt rho / 4) * 1 := by ring
      _ ≤ (a * Real.sqrt rho / 4) * (PDE.vecNormSq w.2 + 1 - w.1) :=
        mul_le_mul_of_nonneg_left hbracketFinal hfactor
  have hbracketNonneg :=
    zero_le_one.trans hbracketFinal
  have hargNonneg :=
    mul_nonneg hfactor hbracketNonneg
  have hdenomNonneg := hfactor
  have hcosh : Real.cosh (a * Real.sqrt rho / 4) ≤
      Real.cosh ((a * Real.sqrt rho / 4) *
        (PDE.vecNormSq w.2 + 1 - w.1)) := by
    rw [Real.cosh_le_cosh]
    simpa only [abs_of_nonneg hdenomNonneg, abs_of_nonneg hargNonneg] using harg
  change 1 ≤ Real.cosh (resolventPhase a rho
      (terminalTranslation v0 (localABPAffine v0 w))) /
      Real.cosh (a * Real.sqrt rho / 4)
  rw [resolventPhase_localABPAffine]
  exact (le_div_iff₀ (Real.cosh_pos _)).mpr (by simpa using hcosh)




private theorem parabolicOperator_add_of_contDiffAt {d : Nat}
    (B : CoefficientField d) (u v : TimeVelocity d → Real)
    (z : TimeVelocity d) (hu : ContDiffAt Real 2 u z)
    (hv : ContDiffAt Real 2 v z) :
    parabolicOperator B (fun y ↦ u y + v y) z =
      parabolicOperator B u z + parabolicOperator B v z := by
  have huDiff := hu.differentiableAt (by norm_num)
  have hvDiff := hv.differentiableAt (by norm_num)
  have hfirst :
      fderiv Real (fun y ↦ u y + v y) =ᶠ[nhds z]
        fun y ↦ fderiv Real u y + fderiv Real v y := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)]
      with y huy hvy
    exact fderiv_fun_add (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))
  have huFirstDiff :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvFirstDiff :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond :
      fderiv Real (fderiv Real (fun y ↦ u y + v y)) z =
        fderiv Real (fderiv Real u) z + fderiv Real (fderiv Real v) z := by
    calc
      fderiv Real (fderiv Real (fun y ↦ u y + v y)) z =
          fderiv Real (fun y ↦ fderiv Real u y + fderiv Real v y) z :=
        hfirst.fderiv_eq
      _ = fderiv Real (fderiv Real u) z + fderiv Real (fderiv Real v) z :=
        fderiv_fun_add huFirstDiff hvFirstDiff
  have htime : timeDerivative (fun y ↦ u y + v y) z =
      timeDerivative u z + timeDerivative v z := by
    unfold timeDerivative
    rw [fderiv_fun_add huDiff hvDiff]
    rfl
  have hhessian : velocityHessian (fun y ↦ u y + v y) z =
      velocityHessian u z + velocityHessian v z := by
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, parabolicOperator_apply,
    htime, hhessian, HypoellipticAleksandrov.matrixContraction_add_right]
  ring

private theorem exists_rho_gt_one_inv_cosh_le
    (a eps : Real) (ha : 0 < a) (heps : 0 < eps) :
    ∃ rho : Real, 1 < rho ∧
      (Real.cosh (a * Real.sqrt rho / 4))⁻¹ ≤ eps := by
  let x : Real := Real.arcosh (max 1 eps⁻¹)
  let s : Real := 2 + 4 * x / a
  let rho : Real := s ^ 2
  have hmax : 1 ≤ max 1 eps⁻¹ := le_max_left _ _
  have hx : 0 ≤ x := Real.arcosh_nonneg hmax
  have hs : 1 < s := by
    dsimp only [s]
    have : 0 ≤ 4 * x / a := div_nonneg (mul_nonneg (by norm_num) hx) ha.le
    linarith
  have hs0 : 0 ≤ s := hs.le.trans' zero_le_one
  have hrho : 1 < rho := by
    dsimp only [rho]
    nlinarith
  have hsqrt : Real.sqrt rho = s := by
    dsimp only [rho]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs0]
  have harg : x ≤ a * Real.sqrt rho / 4 := by
    rw [hsqrt]
    dsimp only [s]
    field_simp [ha.ne']
    nlinarith [ha]
  have harg0 : 0 ≤ a * Real.sqrt rho / 4 := by positivity
  have hcosh : eps⁻¹ ≤ Real.cosh (a * Real.sqrt rho / 4) := by
    calc
      eps⁻¹ ≤ max 1 eps⁻¹ := le_max_right _ _
      _ = Real.cosh x := (Real.cosh_arcosh hmax).symm
      _ ≤ Real.cosh (a * Real.sqrt rho / 4) := by
        rw [Real.cosh_le_cosh]
        simpa only [abs_of_nonneg hx, abs_of_nonneg harg0] using harg
  refine ⟨rho, hrho, ?_⟩
  exact (inv_le_comm₀ (Real.cosh_pos _) heps).2 hcosh

private theorem exists_eta_for_near_one_error
    (d : Nat) (C rho eps : Real)
    (hC : 0 < C) (hrho : 0 < rho) (heps : 0 < eps) :
    ∃ eta : Real, 0 < eta ∧ eta < 1 ∧
      C * (1 / 2 : Real) ^ ((d : Real) / ((d : Real) + 1)) * rho *
        Real.rpow (eta * (2 : Real) ^ d) (1 / ((d : Real) + 1)) ≤ eps := by
  let n : Nat := d + 1
  let K : Real :=
    C * (1 / 2 : Real) ^ ((d : Real) / ((d : Real) + 1)) * rho
  let q : Real := 2 ^ d
  let x : Real := eps / K
  let eta0 : Real := x ^ n / q
  let eta : Real := min (1 / 2) eta0
  have hhalf : 0 < (1 / 2 : Real) := by norm_num
  have hpow : 0 < (1 / 2 : Real) ^ ((d : Real) / ((d : Real) + 1)) :=
    Real.rpow_pos_of_pos hhalf _
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hn : n ≠ 0 := by
    dsimp only [n]
    omega
  have heta0 : 0 < eta0 := by
    dsimp only [eta0]
    positivity
  have heta : 0 < eta := lt_min (by norm_num) heta0
  have heta_lt_one : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have heta_bound : eta * q ≤ x ^ n := by
    have := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : Real) eta0) hq.le
    dsimp only [eta0] at this
    field_simp [hq.ne'] at this
    simpa only [eta, mul_comm] using this
  have hp : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hbase : 0 ≤ eta * q := mul_nonneg heta.le hq.le
  have hrpow : Real.rpow (eta * q) (1 / ((d : Real) + 1)) ≤ x := by
    calc
      Real.rpow (eta * q) (1 / ((d : Real) + 1)) ≤
          Real.rpow (x ^ n) (1 / ((d : Real) + 1)) :=
        Real.rpow_le_rpow hbase heta_bound hp
      _ = x := by
        have hcast : (n : Real) = (d : Real) + 1 := by
          dsimp only [n]
          norm_num
        rw [show 1 / ((d : Real) + 1) = ((n : Real))⁻¹ by
          rw [hcast]
          exact one_div _]
        exact Real.pow_rpow_inv_natCast hx.le hn
  refine ⟨eta, heta, heta_lt_one, ?_⟩
  change K * Real.rpow (eta * q) (1 / ((d : Real) + 1)) ≤ eps
  calc
    K * Real.rpow (eta * q) (1 / ((d : Real) + 1)) ≤ K * x :=
      mul_le_mul_of_nonneg_left hrpow hK.le
    _ = eps := by
      dsimp only [x]
      field_simp [hK.ne']



/-- For every target value strictly between zero and one, a sufficiently
near-one superlevel density gives the source-aware terminal lower bound. -/
theorem exists_sourceDensityToPoint_near_one
    (d : Nat) (hd : 0 < d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) (g : Real)
    (hg0 : 0 < g) (hg1 : g < 1) :
    ∃ beta : Real, 0 < beta ∧ beta < 1 ∧
      ∃ C : Real, 0 < C ∧
        SourceDensityToPoint d lam Lam beta g C      := by
  have exists_resolventBarrier_strict_sign_of_mem_velocityCube :
      ∃ a > 0, ∀ rho > 1, ∀ A : CoefficientField d, ∀ z,
      z.2 ∈ velocityCube 0 1 →
      lam • 1 ≤ coefficientAt A z →
      coefficientAt A z ≤ Lam • 1 →
      0 < parabolicOperator A (resolventBarrier a rho) z +
        rho * resolventBarrier a rho z := by
    let D : ℝ := d
    let C : ℝ := 1 + 2 * D * Lam
    let a : ℝ := 1 / (8 * C)
    have hD : 0 ≤ D := by positivity
    have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
    have hwitness := resolvent_witness_pos hD hLam.le
    change 0 < a ∧ 0 < 1 - a * C - 4 * a ^ 2 * (D * Lam) at hwitness
    obtain ⟨ha, hcoef⟩ := hwitness
    refine ⟨a, ha, ?_⟩
    intro rho hrho A z hzVelocity hlower hupper
    let M : PDE.Mat d := coefficientAt A z
    have htraceNonneg : 0 ≤ M.trace := by
      exact trace_nonneg_of_loewner_lower hlam hlower
    have htraceUpper : M.trace ≤ D * Lam := by
      simpa only [D] using trace_le_natCast_mul_of_loewner_upper hupper
    have hnorm : PDE.vecNormSq z.2 ≤ D := by
      simpa only [D] using vecNormSq_le_natCast_of_mem_unit_velocityCube hzVelocity
    have hquadUpper :
        PDE.vecDot z.2 (M *ᵥ z.2) ≤ D * Lam := by
      calc
        PDE.vecDot z.2 (M *ᵥ z.2) ≤ Lam * PDE.vecNormSq z.2 :=
          vecDot_mulVec_le_of_loewner_upper hupper z.2
        _ ≤ Lam * D := mul_le_mul_of_nonneg_left hnorm hLam.le
        _ = D * Lam := mul_comm _ _
    have hC : 0 < C := by
      dsimp only [C]
      positivity
    have htraceC : 1 + 2 * M.trace ≤ C := by
      dsimp only [C]
      nlinarith
    rw [parabolicOperator_add_resolvent_resolventBarrier]
    exact resolvent_scalar_expression_pos ha hC hrho htraceNonneg
      htraceC hquadUpper hcoef
  have nonneg_on_localABPForwardBoundary {d : Nat} (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real) (hU : IsOpen U) (hclosed : parabolicClosedBox 1 1 0 0 ⊆ U) (hu : ContDiffOn Real 2 u U) (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0)) (v0 : PDE.Vec d) (hv0 : v0 ∈ velocityClosedCube 0 (1 / 2 : Real)) :
      ∀ z ∈ localABPForwardBoundary v0, 0 ≤ u z := by
    intro z hz
    have hzK : z ∈ localABPClosure v0 :=
      localABPForwardBoundary_subset_closure v0 hz
    have hzU : z ∈ U :=
      hclosed (localABPClosure_subset_parabolicClosedBox_one hv0 hzK)
    have hzClosure : z ∈ closure (localABPInterior v0) :=
      localABPForwardBoundary_subset_closure_interior v0 hz
    have hmaps : MapsTo u (localABPInterior v0) (Ici 0) := by
      intro y hy
      exact hnonneg y (localABPInterior_subset_parabolicBox_one hv0 hy)
    have hcont : ContinuousAt u z :=
      (contDiffAt_of_contDiffOn_of_isOpen hU hu hzU).continuousAt
    have hzImage : u z ∈ closure (Ici 0) :=
      hcont.continuousWithinAt.mem_closure hzClosure hmaps
    simpa only [isClosed_Ici.closure_eq, Set.mem_Ici] using hzImage
  have sub_center_mem_velocityCube_of_mem_localABPInterior {v0 : PDE.Vec d} {z : TimeVelocity d} (hz : z ∈ localABPInterior v0) :
      z.2 - v0 ∈ velocityCube 0 1 := by
    rcases hz with ⟨w, hw, rfl⟩
    have hwv := (mem_parabolicInterior_iff.mp hw).2.2
    have hwcube := euclideanBall_subset_velocityCube (by norm_num) hwv
    have heq : (localABPAffine v0 w).2 - v0 = (1 / 2 : Real) • w.2 := by
      simp [localABPAffine, parabolicAffine]
    rw [heq]
    intro i
    have hi := hwcube i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero] at hi ⊢
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : Real))]
    nlinarith [abs_nonneg (w.2 i)]
  have one_le_normalizedTranslatedResolventBarrier_on_localABPForwardBoundary {a : ℝ} {rho : ℝ} {v0 : PDE.Vec d} (ha : 0 < a) (hrho : 1 < rho) {z : TimeVelocity d} (hz : z ∈ localABPForwardBoundary v0) :
      1 ≤ normalizedTranslatedResolventBarrier a rho v0 z := by
    rcases hz with ⟨w, hw, rfl⟩
    rcases mem_forwardParabolicBoundary_iff.mp hw with hinitial | hlateral
    · rcases hinitial with ⟨ht, _⟩
      apply one_le_normalizedTranslatedResolventBarrier_localABPAffine w ha hrho
      rw [ht]
      linarith [PDE.vecNormSq_nonneg w.2]
    · rcases hlateral with ⟨_, ht1, hSphere⟩
      apply one_le_normalizedTranslatedResolventBarrier_localABPAffine w ha hrho
      have hnorm : PDE.vecNormSq w.2 = 1 := by
        change PDE.euclideanSqDist w.2 0 = 1 ^ 2 at hSphere
        simpa [PDE.euclideanSqDist] using hSphere
      rw [hnorm]
      linarith
  have exists_normalizedTranslatedResolventBarrier_strict_sign :
      ∃ a > 0, ∀ rho > 1, ∀ A : CoefficientField d, ∀ z v0,
      z.2 - v0 ∈ velocityCube 0 1 →
      lam • 1 ≤ coefficientAt A z →
      coefficientAt A z ≤ Lam • 1 →
      0 < parabolicOperator A (normalizedTranslatedResolventBarrier a rho v0) z +
        rho * normalizedTranslatedResolventBarrier a rho v0 z := by
    obtain ⟨a, ha, hsign⟩ :=
      exists_resolventBarrier_strict_sign_of_mem_velocityCube
    refine ⟨a, ha, ?_⟩
    intro rho hrho A z v0 hz hlower hupper
    rw [parabolicOperator_add_resolvent_normalizedTranslatedResolventBarrier]
    have hcosh : 0 < Real.cosh (a * Real.sqrt rho / 4) := Real.cosh_pos _
    apply mul_pos (inv_pos.mpr hcosh)
    exact hsign rho hrho (fun _ _ => coefficientAt A z) (terminalTranslation v0 z) (by
      simpa only [terminalTranslation, Prod.snd_sub, Pi.zero_apply] using hz) hlower hupper
  obtain ⟨CABP, hCABP, hABP⟩ :=
    exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure
      d hd lam hlam
  obtain ⟨a, ha, hbarrier⟩ :=
    exists_normalizedTranslatedResolventBarrier_strict_sign
  let Csource : Real :=
    CABP * (1 / 2 : Real) ^ ((d : Real) / ((d : Real) + 1))
  have hCsource : 0 < Csource := by
    dsimp only [Csource]
    positivity
  let eps : Real := (1 - g) / 4
  have heps : 0 < eps := by
    dsimp only [eps]
    have hone : 0 < (1 : Real) := hg0.trans hg1
    have hfour : 0 < (4 : Real) := hone.trans (by norm_num)
    exact div_pos (sub_pos.mpr hg1) hfour
  obtain ⟨rho, hrho, htargetBarrier⟩ :=
    exists_rho_gt_one_inv_cosh_le a eps ha heps
  have hrhoPos : 0 < rho := zero_lt_one.trans hrho
  obtain ⟨eta, heta, hetaOne, herror⟩ :=
    exists_eta_for_near_one_error d CABP rho eps hCABP hrhoPos heps
  let beta : Real := 1 - eta
  have hbeta : 0 < beta := by
    dsimp only [beta]
    linarith
  have hbetaOne : beta < 1 := by
    dsimp only [beta]
    linarith
  refine ⟨beta, hbeta, hbetaOne, Csource, hCsource, ?_⟩
  intro U B Fsrc u hU hclosed hB hu hFsrc hu_nonneg hFsrc_nonneg
    hlower hupper hsuper hdensity v0 hv0
  let psi : TimeVelocity d → Real :=
    normalizedTranslatedResolventBarrier a rho v0
  let w : TimeVelocity d → Real := fun z ↦ -(u z + psi z - 1 + eps)
  let Ftot : TimeVelocity d → Real :=
    fun z ↦ Fsrc z + rho * max (1 - u z) 0
  have hQU : parabolicBox 1 1 0 0 ⊆ U := by
    intro z hz
    apply hclosed
    rcases hz with ⟨⟨ht0, ht1⟩, hzv⟩
    exact ⟨⟨ht0.le, ht1.le⟩, fun i ↦ (hzv i).le⟩
  have hKU : localABPClosure v0 ⊆ U :=
    (localABPClosure_subset_parabolicClosedBox_one hv0).trans hclosed
  have hpsi : ContDiffOn Real 2 psi U := by
    dsimp only [psi]
    exact (contDiff_normalizedTranslatedResolventBarrier a rho v0).contDiffOn
  have hw : ContDiffOn Real 2 w U := by
    dsimp only [w]
    fun_prop
  have hFtot : ContinuousOn Ftot U := by
    dsimp only [Ftot]
    exact hFsrc.add (continuousOn_const.mul
      ((continuousOn_const.sub hu.continuousOn).sup continuousOn_const))
  have hlowClosure : HasLowerEllipticityOn lam B (localABPClosure v0) :=
    hasLowerEllipticityOn_localABPClosure hclosed hB hlower hv0
  have hFtot_nonneg : IsNonnegativeOn Ftot (localABPInterior v0) := by
    intro z hz
    have hzQ : z ∈ parabolicBox 1 1 0 0 :=
      localABPInterior_subset_parabolicBox_one hv0 hz
    dsimp only [Ftot]
    exact add_nonneg (hFsrc_nonneg z hzQ)
      (mul_nonneg hrhoPos.le (le_max_right _ _))
  have hineq : ∀ z ∈ localABPInterior v0,
      parabolicOperator B w z + rho * w z ≤ Ftot z := by
    intro z hz
    have hzQ : z ∈ parabolicBox 1 1 0 0 :=
      localABPInterior_subset_parabolicBox_one hv0 hz
    have hzU : z ∈ U := hQU hzQ
    have huAt : ContDiffAt Real 2 u z :=
      contDiffAt_of_contDiffOn_of_isOpen hU hu hzU
    have hpsiAt : ContDiffAt Real 2 psi z :=
      contDiffAt_of_contDiffOn_of_isOpen hU hpsi hzU
    have hadd : parabolicOperator B (fun y ↦ u y + psi y) z =
        parabolicOperator B u z + parabolicOperator B psi z :=
      parabolicOperator_add_of_contDiffAt B u psi z huAt hpsiAt
    have hconst :
        parabolicOperator B (fun y ↦ u y + psi y - 1 + eps) z =
          parabolicOperator B (fun y ↦ u y + psi y) z := by
      calc
        parabolicOperator B (fun y ↦ u y + psi y - 1 + eps) z =
            parabolicOperator B (fun y ↦ (u y + psi y) + (-1 + eps)) z := by
          congr 2
          funext y
          ring
        _ = parabolicOperator B (fun y ↦ u y + psi y) z :=
          parabolicOperator_add_const B (fun y ↦ u y + psi y) (-1 + eps) z
    have hop : parabolicOperator B w z + rho * w z =
        -parabolicOperator B u z -
            (parabolicOperator B psi z + rho * psi z) +
          rho * (1 - u z - eps) := by
      dsimp only [w]
      rw [parabolicOperator_neg, hconst, hadd]
      ring
    have hsourceOperator : -parabolicOperator B u z ≤ Fsrc z := by
      have hsup := hsuper z hzQ
      linarith
    have hpsiOperator :
        0 < parabolicOperator B psi z + rho * psi z := by
      apply hbarrier rho hrho B z v0
      · exact sub_center_mem_velocityCube_of_mem_localABPInterior hz
      · exact hlower z hzQ
      · exact hupper z hzQ
    have hscalar : rho * (1 - u z - eps) ≤ rho * max (1 - u z) 0 := by
      apply mul_le_mul_of_nonneg_left _ hrhoPos.le
      exact (sub_le_self (1 - u z) heps.le).trans (le_max_left _ _)
    rw [hop]
    dsimp only [Ftot]
    linarith only [hsourceOperator, hpsiOperator, hscalar]
  have hboundary : ∀ z ∈ localABPForwardBoundary v0, w z ≤ 0 := by
    intro z hz
    have huz : 0 ≤ u z :=
      nonneg_on_localABPForwardBoundary U u hU hclosed hu hu_nonneg v0 hv0 z hz
    have hpsiz : 1 ≤ psi z := by
      dsimp only [psi]
      exact one_le_normalizedTranslatedResolventBarrier_on_localABPForwardBoundary
        ha hrho hz
    dsimp only [w]
    linarith
  have habp := hABP U B w Ftot v0 rho hU hKU hB hw hFtot hlowClosure
    hFtot_nonneg hineq hboundary
  let E : Set (TimeVelocity d) :=
    parabolicBox 1 1 0 0 ∩ {z | u z < 1}
  have hnorm :=
    exp_neg_quarter_mul_parabolicLpNormOn_localABP_weighted_source_add_one_sub_le
      d hd rho hrhoPos.le U Fsrc u hclosed hu hFsrc hu_nonneg hFsrc_nonneg v0 hv0
  have habpLow : w (1, v0) ≤
      Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0) +
        Csource * rho *
          Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := by
    calc
      w (1, v0) ≤ Csource *
          (Real.exp (-rho / 4) *
            parabolicLpNormOn d
              (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * Ftot z)
              (localABPInterior v0)) := by
        simpa only [Csource, mul_assoc] using habp
      _ ≤ Csource *
          (parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0) +
            rho * Real.rpow (volume E).toReal
              (1 / ((d : Real) + 1))) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [Ftot, E] using hnorm
        · exact hCsource.le
      _ = Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0) +
          Csource * rho *
            Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := by
        ring
  have hvolume := volume_parabolicBox_inter_lt_one_toReal_le_one_sub_mul
    d beta U u hQU hu hdensity
  have hEvolume : (volume E).toReal ≤ eta * 2 ^ d := by
    dsimp only [E]
    rw [volume_parabolicBox_one_toReal] at hvolume
    simpa only [beta, sub_sub_cancel] using hvolume
  have hexponent : 0 ≤ 1 / ((d : Real) + 1) := by positivity
  have hrpowVolume :
      Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) ≤
        Real.rpow (eta * 2 ^ d) (1 / ((d : Real) + 1)) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hEvolume hexponent
  have hsourcePref : 0 ≤ Csource * rho :=
    mul_nonneg hCsource.le hrhoPos.le
  have habpError : w (1, v0) ≤
      Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0) + eps := by
    calc
      w (1, v0) ≤ Csource * parabolicLpNormOn d Fsrc
          (parabolicBox 1 1 0 0) + Csource * rho *
            Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := habpLow
      _ ≤ Csource * parabolicLpNormOn d Fsrc
          (parabolicBox 1 1 0 0) + Csource * rho *
            Real.rpow (eta * 2 ^ d) (1 / ((d : Real) + 1)) :=
        by simpa [add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_left hrpowVolume hsourcePref)
            (Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0)))
      _ ≤ Csource * parabolicLpNormOn d Fsrc
          (parabolicBox 1 1 0 0) + eps := by
        simpa [add_comm] using
          (add_le_add_left (by
              dsimp only [Csource]
              simpa only [mul_assoc, one_div, Real.rpow_eq_pow] using herror)
            (Csource * parabolicLpNormOn d Fsrc (parabolicBox 1 1 0 0)))
  have hpsiTarget : psi (1, v0) ≤ eps := by
    dsimp only [psi]
    rw [normalizedTranslatedResolventBarrier_target]
    exact htargetBarrier
  dsimp only [w] at habpError
  have hepsFormula : 4 * eps = 1 - g := by
    dsimp only [eps]
    ring
  linarith

end HypoellipticAleksandrov.Parabolic

