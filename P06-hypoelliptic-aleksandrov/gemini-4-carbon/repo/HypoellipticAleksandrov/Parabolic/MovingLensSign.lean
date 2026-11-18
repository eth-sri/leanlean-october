module

public import HypoellipticAleksandrov.Parabolic.MovingLensGeometry
public import HypoellipticAleksandrov.Parabolic.Operator
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Matrix Filter Topology
open scoped BigOperators MatrixOrder

noncomputable section


/-- The rank-one velocity matrix formed from the moving-lens displacement. -/
def movingLensDisplacementOuter {d : ℕ} (y : PDE.Vec d) (z : TimeVelocity d) : PDE.Mat d :=
  fun i j => movingLensDisplacement y z i * movingLensDisplacement y z j

/-- The source rational barrier on a moving lens. -/
def movingLensBarrier {d : ℕ} (xi eps : ℝ) (n : ℕ) (y : PDE.Vec d) :
    TimeVelocity d → ℝ :=
  fun z =>
    (1 - movingLensRadiusSq xi eps y z) ^ 2 /
      (movingLensDenominator xi eps z.1) ^ n

/-- Pointwise `C²` regularity of the moving radius under a nonzero denominator. -/
theorem contDiffAt_movingLensRadiusSq {d : ℕ} {xi eps : ℝ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    ContDiffAt ℝ 2 (movingLensRadiusSq xi eps y) z := by
  unfold movingLensRadiusSq
  apply ContDiffAt.div
  · unfold PDE.vecNormSq PDE.vecDot
    apply ContDiffAt.sum
    intro i _
    unfold movingLensDisplacement
    fun_prop
  · unfold movingLensDenominator
    fun_prop
  · exact hden

/-- Pointwise `C²` regularity of the moving barrier under a nonzero denominator. -/
theorem contDiffAt_movingLensBarrier {d : ℕ} {xi eps : ℝ} {n : ℕ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    ContDiffAt ℝ 2 (movingLensBarrier xi eps n y) z := by
  unfold movingLensBarrier
  apply ContDiffAt.div
  · exact (contDiffAt_const.sub (contDiffAt_movingLensRadiusSq hden)).pow 2
  · unfold movingLensDenominator
    fun_prop
  · exact pow_ne_zero n hden

private theorem fderiv_timeCoordinate_apply {d : ℕ}
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => q.1) z w = w.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ)).fderiv]
  rfl

private theorem fderiv_velocityCoordinate_apply {d : ℕ} (i : Fin d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => q.2 i) z w = w.2 i := by
  have h :=
    (hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd (𝕜 := ℝ))
  change (fderiv ℝ ((fun f => f i) ∘ Prod.snd) z) w = w.2 i
  rw [h.fderiv]
  rfl

private theorem fderiv_movingLensDenominator_apply {d : ℕ} (xi eps : ℝ)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => movingLensDenominator xi eps q.1) z w =
      xi * w.1 := by
  unfold movingLensDenominator
  rw [fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_const_mul (by fun_prop) xi]
  simp [ContinuousLinearMap.smul_apply, fderiv_timeCoordinate_apply, fderiv_const_apply]

private theorem fderiv_movingLensDisplacement_apply {d : ℕ} (y : PDE.Vec d)
    (i : Fin d) (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => movingLensDisplacement y q i) z w =
      w.2 i - w.1 * y i := by
  unfold movingLensDisplacement
  change fderiv ℝ (fun q => q.2 i - q.1 * y i) z w = _
  have htime :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).differentiableAt
  have hvelocity : DifferentiableAt ℝ (fun q => q.2 i) z := by
    exact ((hasFDerivAt_apply (𝕜 := ℝ) i z.2).comp z
      (hasFDerivAt_snd (𝕜 := ℝ))).differentiableAt
  rw [fderiv_fun_sub hvelocity (htime.mul_const (y i)),
    fderiv_fun_mul htime (differentiableAt_const (y i))]
  simp [fderiv_velocityCoordinate_apply, fderiv_timeCoordinate_apply]
  ring

private theorem fderiv_movingLensDisplacementNormSq_apply {d : ℕ} (y : PDE.Vec d)
    (z w : TimeVelocity d) :
    fderiv ℝ (fun q : TimeVelocity d => PDE.vecNormSq (movingLensDisplacement y q)) z w =
      2 * (PDE.vecDot (movingLensDisplacement y z) w.2 -
        w.1 * PDE.vecDot (movingLensDisplacement y z) y) := by
  classical
  unfold PDE.vecNormSq PDE.vecDot
  have hdispDiff (i : Fin d) : DifferentiableAt ℝ
      (fun q => movingLensDisplacement y q i) z := by
    unfold movingLensDisplacement
    fun_prop
  have hsum :
      fderiv ℝ (fun q =>
        ∑ i, movingLensDisplacement y q i * movingLensDisplacement y q i) z =
        ∑ i, fderiv ℝ (fun q =>
          movingLensDisplacement y q i * movingLensDisplacement y q i) z :=
    fderiv_fun_sum fun i _ => (hdispDiff i).mul (hdispDiff i)
  rw [hsum]
  simp
  calc
    ∑ i, (fderiv ℝ
        (fun q => movingLensDisplacement y q i * movingLensDisplacement y q i) z) w =
        ∑ i, 2 * movingLensDisplacement y z i * (w.2 i - w.1 * y i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_fun_mul (hdispDiff i) (hdispDiff i)]
      simp
      rw [fderiv_movingLensDisplacement_apply]
      ring
    _ = 2 * (∑ i, movingLensDisplacement y z i * w.2 i -
        w.1 * ∑ i, movingLensDisplacement y z i * y i) := by
      calc
        ∑ i, 2 * movingLensDisplacement y z i * (w.2 i - w.1 * y i) =
            ∑ i, (2 * movingLensDisplacement y z i * w.2 i -
              2 * w.1 * (movingLensDisplacement y z i * y i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 2 * ∑ i, movingLensDisplacement y z i * w.2 i -
            2 * w.1 * ∑ i, movingLensDisplacement y z i * y i := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
          apply congrArg₂ (· - ·)
          · apply Finset.sum_congr rfl
            intro i _
            ring
          · rfl
        _ = _ := by ring

private theorem differentiableAt_movingLensDenominator {d : ℕ} (xi eps : ℝ)
    (z : TimeVelocity d) :
    DifferentiableAt ℝ (fun q : TimeVelocity d => movingLensDenominator xi eps q.1) z := by
  unfold movingLensDenominator
  fun_prop

private theorem fderiv_movingLensDenominatorInv_apply {d : ℕ} (xi eps : ℝ)
    (z w : TimeVelocity d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fun q : TimeVelocity d => (movingLensDenominator xi eps q.1)⁻¹) z w =
      -(xi * w.1) / (movingLensDenominator xi eps z.1) ^ 2 := by
  let q : TimeVelocity d → ℝ := fun a => movingLensDenominator xi eps a.1
  have hinv := (hasFDerivAt_inv hden).comp z ((differentiableAt_movingLensDenominator xi eps z).hasFDerivAt)
  change fderiv ℝ ((fun x => x⁻¹) ∘ q) z w = _
  rw [hinv.fderiv]
  simp
  rw [fderiv_movingLensDenominator_apply]
  simp only [div_eq_mul_inv]
  ring

private theorem fderiv_movingLensDenominatorInvPow_apply {d : ℕ} (xi eps : ℝ)
    (n : ℕ) (z w : TimeVelocity d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fun q : TimeVelocity d =>
      (movingLensDenominator xi eps q.1)⁻¹ ^ n) z w =
      (n : ℝ) * (movingLensDenominator xi eps z.1)⁻¹ ^ (n - 1) *
        (-(xi * w.1) / (movingLensDenominator xi eps z.1) ^ 2) := by
  rw [fderiv_fun_pow n]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_movingLensDenominatorInv_apply xi eps z w hden]
    ring
  · exact (differentiableAt_movingLensDenominator xi eps z).inv hden

private theorem fderiv_movingLensRadiusSq_apply {d : ℕ} (xi eps : ℝ)
    (y : PDE.Vec d) (z w : TimeVelocity d)
    (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (movingLensRadiusSq xi eps y) z w =
      (2 * (PDE.vecDot (movingLensDisplacement y z) w.2 -
          w.1 * PDE.vecDot (movingLensDisplacement y z) y)) /
          movingLensDenominator xi eps z.1 -
        movingLensRadiusSq xi eps y z * (xi * w.1) /
          movingLensDenominator xi eps z.1 := by
  have hnum : DifferentiableAt ℝ
      (fun q => PDE.vecNormSq (movingLensDisplacement y q)) z := by
    unfold PDE.vecNormSq PDE.vecDot movingLensDisplacement
    fun_prop
  have hinv : DifferentiableAt ℝ
      (fun q => (movingLensDenominator xi eps q.1)⁻¹) z := by
    exact (differentiableAt_movingLensDenominator xi eps z).inv hden
  unfold movingLensRadiusSq
  change fderiv ℝ (fun q =>
    PDE.vecNormSq (movingLensDisplacement y q) *
      (movingLensDenominator xi eps q.1)⁻¹) z w = _
  rw [fderiv_fun_mul hnum hinv]
  simp
  rw [fderiv_movingLensDisplacementNormSq_apply,
    fderiv_movingLensDenominatorInv_apply xi eps z w hden]
  field_simp [hden]
  ring

private theorem fderiv_movingLensBarrier_apply {d : ℕ} (xi eps : ℝ) (n : ℕ)
    (y : PDE.Vec d) (z w : TimeVelocity d)
    (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (movingLensBarrier xi eps n y) z w =
      2 * (movingLensRadiusSq xi eps y z - 1) *
          fderiv ℝ (movingLensRadiusSq xi eps y) z w *
          (movingLensDenominator xi eps z.1)⁻¹ ^ n +
        (1 - movingLensRadiusSq xi eps y z) ^ 2 *
          fderiv ℝ (fun q : TimeVelocity d =>
            (movingLensDenominator xi eps q.1)⁻¹ ^ n) z w := by
  have hr : DifferentiableAt ℝ (movingLensRadiusSq xi eps y) z :=
    (contDiffAt_movingLensRadiusSq hden).differentiableAt (by norm_num)
  have hq : DifferentiableAt ℝ
      (fun q => (movingLensDenominator xi eps q.1)⁻¹ ^ n) z :=
    ((differentiableAt_movingLensDenominator xi eps z).inv hden).pow n
  unfold movingLensBarrier
  have hrewrite :
      (fun q =>
        (1 - movingLensRadiusSq xi eps y q) ^ 2 /
          (movingLensDenominator xi eps q.1) ^ n) =
        fun q => (1 - movingLensRadiusSq xi eps y q) ^ 2 *
          (movingLensDenominator xi eps q.1)⁻¹ ^ n := by
    funext q
    rw [div_eq_mul_inv, inv_pow]
  rw [hrewrite]
  have hbase : DifferentiableAt ℝ
      (fun q => 1 - movingLensRadiusSq xi eps y q) z :=
    (differentiableAt_const 1).sub hr
  have hnum : DifferentiableAt ℝ
      (fun q => (1 - movingLensRadiusSq xi eps y q) ^ 2) z :=
    hbase.pow 2
  have hmul := congrArg (fun L => L w)
    (fderiv_fun_mul hnum hq)
  change fderiv ℝ (fun q =>
    (1 - movingLensRadiusSq xi eps y q) ^ 2 *
      (movingLensDenominator xi eps q.1)⁻¹ ^ n) z w = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul] at hmul
  rw [hmul]
  rw [fderiv_fun_pow 2 hbase]
  simp
  rw [fderiv_fun_sub (differentiableAt_const 1) hr]
  simp
  ring



private theorem fderiv_movingLensBarrier_velocity_apply {d : ℕ}
    (xi eps : ℝ) (n : ℕ) (y : PDE.Vec d) (z : TimeVelocity d)
    (j : Fin d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (movingLensBarrier xi eps n y) z (0, Pi.single j 1) =
      4 * (movingLensRadiusSq xi eps y z - 1) *
        movingLensDisplacement y z j /
          (movingLensDenominator xi eps z.1) ^ (n + 1) := by
  rw [fderiv_movingLensBarrier_apply xi eps n y z (0, Pi.single j 1) hden,
    fderiv_movingLensRadiusSq_apply xi eps y z (0, Pi.single j 1) hden,
    fderiv_movingLensDenominatorInvPow_apply xi eps n z (0, Pi.single j 1) hden]
  simp [PDE.vecDot, Pi.single_apply]
  cases n with
  | zero =>
    norm_num
    field_simp [hden]
    ring
  | succ n =>
    field_simp [hden]
    ring

private theorem fderiv_fderiv_movingLensBarrier_velocity_apply {d : ℕ}
    (xi eps : ℝ) (n : ℕ) (y : PDE.Vec d) (z : TimeVelocity d)
    (i j : Fin d) (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    fderiv ℝ (fderiv ℝ (movingLensBarrier xi eps n y)) z
      (0, Pi.single i 1) (0, Pi.single j 1) =
      8 * movingLensDisplacement y z i * movingLensDisplacement y z j /
          (movingLensDenominator xi eps z.1) ^ (n + 2) +
        4 * (movingLensRadiusSq xi eps y z - 1) /
          (movingLensDenominator xi eps z.1) ^ (n + 1) * if i = j then 1 else 0  := by
  have fderiv_fderiv_apply_eq_fderiv_eval {w : TimeVelocity d → ℝ} {z direction₁ direction₂ : TimeVelocity d} (hw : ContDiffAt ℝ 2 w z) :
      fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ =
      fderiv ℝ (fun a => fderiv ℝ w a direction₂) z direction₁ := by
    have hDw :=
      (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hEval :
        fderiv ℝ (fun a => fderiv ℝ w a direction₂) z =
          (fderiv ℝ (fderiv ℝ w) z).flip direction₂ := by
      simpa using
        ((hDw.hasFDerivAt.clm_apply (hasFDerivAt_const direction₂ z)).fderiv)
    simpa using (congrArg (fun L => L direction₁) hEval).symm
  let b := movingLensBarrier xi eps n y
  let direction₁ : TimeVelocity d := (0, Pi.single i 1)
  let direction₂ : TimeVelocity d := (0, Pi.single j 1)
  have hdenCont : ContinuousAt
      (fun a => movingLensDenominator xi eps a.1) z := by
    unfold movingLensDenominator
    fun_prop
  have hfirst :
      (fun a => fderiv ℝ b a direction₂) =ᶠ[𝓝 z]
        fun a => 4 * (movingLensRadiusSq xi eps y a - 1) *
          movingLensDisplacement y a j /
            (movingLensDenominator xi eps a.1) ^ (n + 1) := by
    filter_upwards [(hdenCont.eventually_ne hden)] with a ha
    dsimp only [b, direction₂]
    exact fderiv_movingLensBarrier_velocity_apply xi eps n y a j ha
  have hr : DifferentiableAt ℝ (movingLensRadiusSq xi eps y) z :=
    (contDiffAt_movingLensRadiusSq hden).differentiableAt (by norm_num)
  have hdisp : DifferentiableAt ℝ
      (fun a => movingLensDisplacement y a j) z := by
    unfold movingLensDisplacement
    fun_prop
  have hq : DifferentiableAt ℝ
      (fun a =>
        (movingLensDenominator xi eps a.1)⁻¹ ^ (n + 1)) z :=
    ((differentiableAt_movingLensDenominator xi eps z).inv hden).pow (n + 1)
  calc
    fderiv ℝ (fderiv ℝ b) z direction₁ direction₂ =
        fderiv ℝ (fun a => fderiv ℝ b a direction₂) z direction₁ :=
      fderiv_fderiv_apply_eq_fderiv_eval (contDiffAt_movingLensBarrier hden)
    _ = fderiv ℝ (fun a => 4 * (movingLensRadiusSq xi eps y a - 1) *
        movingLensDisplacement y a j /
          (movingLensDenominator xi eps a.1) ^ (n + 1)) z direction₁ := by
      exact congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L direction₁) hfirst.fderiv_eq
    _ = 8 * movingLensDisplacement y z i * movingLensDisplacement y z j /
          (movingLensDenominator xi eps z.1) ^ (n + 2) +
        4 * (movingLensRadiusSq xi eps y z - 1) /
          (movingLensDenominator xi eps z.1) ^ (n + 1) * if i = j then 1 else 0 := by
      have hrewrite :
          (fun a => 4 * (movingLensRadiusSq xi eps y a - 1) *
            movingLensDisplacement y a j /
              (movingLensDenominator xi eps a.1) ^ (n + 1)) =
            fun a => (4 * (movingLensRadiusSq xi eps y a - 1) *
              movingLensDisplacement y a j) *
                (movingLensDenominator xi eps a.1)⁻¹ ^ (n + 1) := by
        funext a
        rw [div_eq_mul_inv, inv_pow]
      rw [hrewrite]
      have hprod : DifferentiableAt ℝ (fun a =>
          4 * (movingLensRadiusSq xi eps y a - 1) *
            movingLensDisplacement y a j) z :=
        ((differentiableAt_const 4).mul (hr.sub_const 1)).mul hdisp
      rw [fderiv_fun_mul hprod hq]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      have hscalar : DifferentiableAt ℝ (fun a =>
          4 * (movingLensRadiusSq xi eps y a - 1)) z :=
        (differentiableAt_const 4).mul (hr.sub_const 1)
      rw [fderiv_fun_mul hscalar hdisp]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [fderiv_fun_mul (differentiableAt_const 4) (hr.sub_const 1)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, fderiv_const_apply]
      rw [fderiv_fun_sub hr (differentiableAt_const 1)]
      simp only [fderiv_const_apply, sub_zero]
      rw [fderiv_movingLensRadiusSq_apply xi eps y z direction₁ hden,
        fderiv_movingLensDisplacement_apply,
        fderiv_movingLensDenominatorInvPow_apply xi eps (n + 1) z direction₁ hden]
      dsimp only [direction₁]
      simp [PDE.vecDot, Pi.single_apply]
      by_cases hij : i = j
      · subst j
        simp
        ring
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji]
        ring


/-- Contraction with the identity is the matrix trace. -/
theorem movingLens_matrixContraction_one_eq_trace {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A 1 = A.trace := by
  classical
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

/-- Contraction with the moving displacement outer product is its quadratic form. -/
theorem matrixContraction_movingLensDisplacementOuter {d : ℕ} (A : PDE.Mat d)
    (y : PDE.Vec d) (z : TimeVelocity d) :
    matrixContraction A (movingLensDisplacementOuter y z) =
      PDE.vecDot (movingLensDisplacement y z)
        (A *ᵥ movingLensDisplacement y z) := by
  classical
  unfold movingLensDisplacementOuter matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact contraction of the moving-lens barrier Hessian with an arbitrary
matrix.  No symmetry or ellipticity assumption on the matrix is used. -/
theorem matrixContraction_velocityHessian_movingLensBarrier {d : ℕ}
    (A : PDE.Mat d) {xi eps : ℝ} {n : ℕ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    matrixContraction A (velocityHessian (movingLensBarrier xi eps n y) z) =
      8 * PDE.vecDot (movingLensDisplacement y z)
          (A *ᵥ movingLensDisplacement y z) /
          (movingLensDenominator xi eps z.1) ^ (n + 2) +
        4 * (movingLensRadiusSq xi eps y z - 1) * A.trace /
          (movingLensDenominator xi eps z.1) ^ (n + 1)  := by
  have velocityHessian_movingLensBarrier :
      velocityHessian (movingLensBarrier xi eps n y) z =
      (8 / (movingLensDenominator xi eps z.1) ^ (n + 2)) •
          movingLensDisplacementOuter y z +
        (4 * (movingLensRadiusSq xi eps y z - 1) /
          (movingLensDenominator xi eps z.1) ^ (n + 1)) • 1 := by
    ext i j
    unfold velocityHessian
    rw [fderiv_fderiv_movingLensBarrier_velocity_apply xi eps n y z i j hden]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      movingLensDisplacementOuter, smul_eq_mul]
    ring
  rw [velocityHessian_movingLensBarrier,
    HypoellipticAleksandrov.matrixContraction_add_right,
    HypoellipticAleksandrov.matrixContraction_smul_right,
    HypoellipticAleksandrov.matrixContraction_smul_right,
    matrixContraction_movingLensDisplacementOuter,
    movingLens_matrixContraction_one_eq_trace]
  ring

/-- The project-sign moving-lens barrier identity.  Since
`P_A = ∂t - A : Dv²`, this is the source identity for `-P_A`. -/
theorem movingLensBarrier_neg_parabolicOperator_identity {d : ℕ}
    (A : CoefficientField d) {xi eps : ℝ} {n : ℕ} {y : PDE.Vec d}
    {z : TimeVelocity d} (hden : movingLensDenominator xi eps z.1 ≠ 0) :
    (movingLensDenominator xi eps z.1) ^ (n + 1) *
        (-parabolicOperator A (movingLensBarrier xi eps n y) z) =
      (n : ℝ) * xi * (1 - movingLensRadiusSq xi eps y z) ^ 2 +
        8 * (PDE.vecDot (movingLensDisplacement y z)
          (coefficientAt A z *ᵥ movingLensDisplacement y z) /
          movingLensDenominator xi eps z.1) +
        2 * (movingLensRadiusSq xi eps y z - 1) *
          (xi * movingLensRadiusSq xi eps y z +
            2 * PDE.vecDot (movingLensDisplacement y z) y +
            2 * (coefficientAt A z).trace)  := by
  have timeDerivative_movingLensBarrier :
      timeDerivative (movingLensBarrier xi eps n y) z =
      (-2 * (movingLensRadiusSq xi eps y z - 1) *
          (2 * PDE.vecDot (movingLensDisplacement y z) y +
            xi * movingLensRadiusSq xi eps y z) -
        (n : ℝ) * xi * (1 - movingLensRadiusSq xi eps y z) ^ 2) /
          (movingLensDenominator xi eps z.1) ^ (n + 1) := by
    unfold timeDerivative
    rw [fderiv_movingLensBarrier_apply xi eps n y z (1, 0) hden,
      fderiv_movingLensRadiusSq_apply xi eps y z (1, 0) hden,
      fderiv_movingLensDenominatorInvPow_apply xi eps n z (1, 0) hden]
    simp only [Pi.zero_apply, mul_zero, PDE.vecDot, Finset.sum_const_zero]
    unfold movingLensRadiusSq
    cases n with
    | zero =>
      norm_num
      field_simp [hden]
      ring
    | succ n =>
      simp only [Nat.cast_succ, Nat.succ_sub_one, inv_pow]
      field_simp [hden]
      ring
  rw [parabolicOperator_apply,
    timeDerivative_movingLensBarrier,
    matrixContraction_velocityHessian_movingLensBarrier (coefficientAt A z) hden]
  field_simp [hden]
  ring

end




/-- The fixed source lens slope used for the principal-part sign argument. -/
def movingLensSignXi (kappa : ℝ) : ℝ :=
  kappa ^ 3 / 2

/-- A uniform upper bound for the signed lower-order bracket in the barrier
identity. -/
def movingLensSignB (d : ℕ) (lam Lam kappa : ℝ) : ℝ :=
  let _ := lam
  movingLensSignXi kappa + 1 + (d : ℝ) * kappa ^ (-4 : ℤ) +
    2 * (d : ℝ) * |Lam|

/-- The two-region radius threshold for the moving-lens sign argument. -/
def movingLensSignR0 (d : ℕ) (lam Lam kappa : ℝ) : ℝ :=
  (movingLensSignB d lam Lam kappa + 2 * lam) /
    (movingLensSignB d lam Lam kappa + 4 * lam)

/-- The natural exponent selected uniformly before every coefficient and lens
datum. -/
def movingLensSignExponent (d : ℕ) (lam Lam kappa : ℝ) : ℕ :=
  1 + ⌈2 * movingLensSignB d lam Lam kappa /
    (movingLensSignXi kappa * (1 - movingLensSignR0 d lam Lam kappa) ^ 2)⌉₊

private theorem movingLensSignXi_pos {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity

private theorem movingLensSignB_pos (d : ℕ) {lam Lam kappa : ℝ}
    (hkappa : 0 < kappa) :
    0 < movingLensSignB d lam Lam kappa := by
  unfold movingLensSignB
  have hxi := movingLensSignXi_pos hkappa
  have hpow : 0 ≤ kappa ^ (-4 : ℤ) := by positivity
  positivity

private theorem movingLensSignR0_mem_Ioo (d : ℕ) {lam Lam kappa : ℝ}
    (hlam : 0 < lam) (hkappa : 0 < kappa) :
    movingLensSignR0 d lam Lam kappa ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold movingLensSignR0
  have hB := movingLensSignB_pos d (lam := lam) (Lam := Lam) hkappa
  have hden : 0 < movingLensSignB d lam Lam kappa + 4 * lam := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [div_lt_iff₀ hden]
    linarith

private theorem vecDot_mulVec_lower_of_loewner {d : ℕ} {lam : ℝ}
    {M : PDE.Mat d} (hlower : lam • (1 : PDE.Mat d) ≤ M)
    (v : PDE.Vec d) :
    lam * PDE.vecNormSq v ≤ PDE.vecDot v (M *ᵥ v) := by
  have hgap : (M - lam • 1).PosSemidef := Matrix.le_iff.mp hlower
  have hquad := hgap.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad


private theorem two_vecDot_le_vecNormSq_add {d : ℕ} (v w : PDE.Vec d) :
    2 * PDE.vecDot v w ≤ PDE.vecNormSq v + PDE.vecNormSq w := by
  have hcs : PDE.vecDot v w ^ 2 ≤ PDE.vecNormSq v * PDE.vecNormSq w :=
    PDE.sq_vecDot_le_vecNormSq_mul_vecNormSq v w
  have hv : 0 ≤ PDE.vecNormSq v := PDE.vecNormSq_nonneg v
  have hw : 0 ≤ PDE.vecNormSq w := PDE.vecNormSq_nonneg w
  nlinarith [sq_nonneg (PDE.vecNormSq v - PDE.vecNormSq w)]


private theorem vecNormSq_displacement_lt_one_of_normalized_data {d : ℕ}
    {xi eps kappa : ℝ} {y : PDE.Vec d} {z : TimeVelocity d}
    (hden : 0 < movingLensDenominator xi eps z.1)
    (hden_lt : movingLensDenominator xi eps z.1 < kappa ^ 2)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (hr : movingLensRadiusSq xi eps y z < 1) :
    PDE.vecNormSq (movingLensDisplacement y z) < 1 := by
  have hkappa_sq : kappa ^ 2 ≤ 1 := by nlinarith
  exact ((movingLensRadiusSq_lt_one_iff hden).mp hr).trans (hden_lt.trans_le hkappa_sq)

private theorem movingLensSign_bracket_le (d : ℕ) {lam Lam kappa eps : ℝ}
    {y : PDE.Vec d} {z : TimeVelocity d}
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (hden : 0 < movingLensDenominator (movingLensSignXi kappa) eps z.1)
    (hden_lt : movingLensDenominator (movingLensSignXi kappa) eps z.1 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hr_lt : movingLensRadiusSq (movingLensSignXi kappa) eps y z < 1)
    {M : PDE.Mat d} (hupper : M ≤ Lam • (1 : PDE.Mat d)) :
    movingLensSignXi kappa * movingLensRadiusSq (movingLensSignXi kappa) eps y z +
        2 * PDE.vecDot (movingLensDisplacement y z) y + 2 * M.trace ≤
      movingLensSignB d lam Lam kappa  := by
  have trace_le_natCast_mul_of_loewner_upper :
      M.trace ≤ (d : ℝ) * Lam := by
    have hgap : (Lam • 1 - M).PosSemidef := Matrix.le_iff.mp hupper
    have htrace := hgap.trace_nonneg
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul] at htrace
    linarith
  have hdisp := vecNormSq_displacement_lt_one_of_normalized_data hden hden_lt
    hkappa hkappa_one hr_lt
  have hdot := two_vecDot_le_vecNormSq_add (movingLensDisplacement y z) y
  have habs : Lam ≤ |Lam| := le_abs_self Lam
  have hxi : 0 ≤ movingLensSignXi kappa := (movingLensSignXi_pos hkappa).le
  unfold movingLensSignB
  nlinarith

private theorem movingLensSign_lower_bound {d : ℕ} {lam kappa eps : ℝ}
    {y : PDE.Vec d} {z : TimeVelocity d} {M : PDE.Mat d}
    (hden : 0 < movingLensDenominator (movingLensSignXi kappa) eps z.1)
    (hlower : lam • (1 : PDE.Mat d) ≤ M) :
    8 * (PDE.vecDot (movingLensDisplacement y z)
      (M *ᵥ movingLensDisplacement y z) /
      movingLensDenominator (movingLensSignXi kappa) eps z.1) ≥
      8 * lam * movingLensRadiusSq (movingLensSignXi kappa) eps y z := by
  unfold movingLensRadiusSq
  have hdiv := (div_le_div_iff_of_pos_right hden).mpr (vecDot_mulVec_lower_of_loewner hlower (movingLensDisplacement y z))
  calc
    8 * (PDE.vecDot (movingLensDisplacement y z)
        (M *ᵥ movingLensDisplacement y z) /
        movingLensDenominator (movingLensSignXi kappa) eps z.1) ≥
        8 * (lam * PDE.vecNormSq (movingLensDisplacement y z) /
          movingLensDenominator (movingLensSignXi kappa) eps z.1) := by
      exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = 8 * lam * (PDE.vecNormSq (movingLensDisplacement y z) /
          movingLensDenominator (movingLensSignXi kappa) eps z.1) := by ring

private theorem movingLensSign_two_region_positive (d : ℕ) {lam Lam kappa : ℝ}
    (hlam : 0 < lam) (hkappa : 0 < kappa)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < 1) :
    0 < (movingLensSignExponent d lam Lam kappa : ℝ) * movingLensSignXi kappa *
        (1 - r) ^ 2 + 8 * lam * r -
      2 * movingLensSignB d lam Lam kappa * (1 - r) := by
  have hB := movingLensSignB_pos d (lam := lam) (Lam := Lam) hkappa
  have hxi := movingLensSignXi_pos hkappa
  have hr0 := movingLensSignR0_mem_Ioo d (Lam := Lam) hlam hkappa
  let B := movingLensSignB d lam Lam kappa
  let xi := movingLensSignXi kappa
  let r0 := movingLensSignR0 d lam Lam kappa
  let n := movingLensSignExponent d lam Lam kappa
  have hden : 0 < B + 4 * lam := by dsimp [B]; linarith
  have hlinearR0 : 0 < 8 * lam * r0 - 2 * B * (1 - r0) := by
    have heq : 8 * lam * r0 - 2 * B * (1 - r0) = 4 * lam := by
      dsimp only [r0]
      unfold movingLensSignR0
      field_simp [hden.ne']
      ring
    rw [heq]
    linarith
  by_cases hhigh : r0 < r
  · have hlinear : 0 < 8 * lam * r - 2 * B * (1 - r) := by
      nlinarith [hlinearR0]
    have hpow : 0 ≤ (n : ℝ) * xi * (1 - r) ^ 2 := by positivity
    linarith
  · have hlow : r ≤ r0 := le_of_not_gt hhigh
    have hgap : 0 < 1 - r0 := by linarith [hr0.2]
    have hx : 0 < xi * (1 - r0) ^ 2 := by positivity
    have hceil : 2 * B / (xi * (1 - r0) ^ 2) ≤ (⌈2 * B /
        (xi * (1 - r0) ^ 2)⌉₊ : ℝ) := Nat.le_ceil _
    have hceilMul : 2 * B ≤
        (⌈2 * B / (xi * (1 - r0) ^ 2)⌉₊ : ℝ) *
          (xi * (1 - r0) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hceil hx.le
      rw [div_mul_cancel₀ _ hx.ne'] at hmul
      exact hmul
    have hn : 2 * B < (n : ℝ) * xi * (1 - r0) ^ 2 := by
      simp only [n, movingLensSignExponent, Nat.cast_add, Nat.cast_one]
      nlinarith
    have hmono : (1 - r0) ^ 2 ≤ (1 - r) ^ 2 := by nlinarith
    have hfirst : 2 * B < (n : ℝ) * xi * (1 - r) ^ 2 := by
      exact lt_of_lt_of_le hn (mul_le_mul_of_nonneg_left hmono
        (mul_nonneg (Nat.cast_nonneg n) hxi.le))
    have hlast : 2 * B * (1 - r) ≤ 2 * B := by
      nlinarith
    nlinarith

/-- Under only pointwise two-sided Loewner ellipticity, the fixed source
moving-lens barrier is a strict project-sign subsolution on the normalized
small-denominator lens core. -/
theorem parabolicOperator_movingLensBarrier_lt_zero_of_pointwise_loewner
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (A : CoefficientField d) (y : PDE.Vec d) (z : TimeVelocity d) (eps : ℝ)
    (hden_pos : 0 < movingLensDenominator (movingLensSignXi kappa) eps z.1)
    (hden_lt : movingLensDenominator (movingLensSignXi kappa) eps z.1 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hr_lt : movingLensRadiusSq (movingLensSignXi kappa) eps y z < 1)
    (hlower : lam • (1 : PDE.Mat d) ≤ coefficientAt A z)
    (hupper : coefficientAt A z ≤ Lam • (1 : PDE.Mat d)) :
    parabolicOperator A
      (movingLensBarrier (movingLensSignXi kappa) eps
        (movingLensSignExponent d lam Lam kappa) y) z < 0  := by
  have movingLensRadiusSq_nonneg_of_den_pos {xi : ℝ} {eps : ℝ} {z : TimeVelocity d} (hden : 0 < movingLensDenominator xi eps z.1) :
      0 ≤ movingLensRadiusSq xi eps y z := by
    unfold movingLensRadiusSq
    exact div_nonneg (PDE.vecNormSq_nonneg _) hden.le
  let xi := movingLensSignXi kappa
  let n := movingLensSignExponent d lam Lam kappa
  let r := movingLensRadiusSq xi eps y z
  let q := movingLensDenominator xi eps z.1
  let h := movingLensDisplacement y z
  let M := coefficientAt A z
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, xi, q]
    exact movingLensRadiusSq_nonneg_of_den_pos hden_pos
  have hbracket : xi * r + 2 * PDE.vecDot h y + 2 * M.trace ≤
      movingLensSignB d lam Lam kappa := by
    dsimp [xi, r, q, h, M]
    exact movingLensSign_bracket_le d hkappa hkappa_one hden_pos hden_lt hy hr_lt hupper
  have hquad := movingLensSign_lower_bound (y := y) hden_pos hlower
  have hscalar := movingLensSign_two_region_positive d (Lam := Lam) hlam hkappa
    hr_nonneg hr_lt
  have hqpow : 0 < q ^ (n + 1) := pow_pos hden_pos _
  have _ := hlamLam
  have hidentity := movingLensBarrier_neg_parabolicOperator_identity
    (A := A) (xi := xi) (eps := eps) (n := n) (y := y) (z := z) hden_pos.ne'
  have hfactor : 0 ≤ 2 * (1 - r) := by linarith
  have hbracketTerm : 2 * (r - 1) * (xi * r + 2 * PDE.vecDot h y + 2 * M.trace) ≥
      -2 * movingLensSignB d lam Lam kappa * (1 - r) := by
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    nlinarith
  have hscaled : 0 < q ^ (n + 1) *
      (-parabolicOperator A (movingLensBarrier xi eps n y) z) := by
    rw [hidentity]
    dsimp [xi, n, r, q, h, M] at hquad hscalar hbracket hbracketTerm ⊢
    nlinarith
  have hnegative : 0 < -parabolicOperator A (movingLensBarrier xi eps n y) z :=
    pos_of_mul_pos_right hscaled hqpow.le
  exact neg_pos.mp (by simpa only [xi, n] using hnegative)


end HypoellipticAleksandrov.Parabolic

