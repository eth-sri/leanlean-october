module

public import HypoellipticAleksandrov.Parabolic.HarnackABP
public import HypoellipticAleksandrov.Parabolic.ResolventBarrier
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Aesop
import Mathlib.Tactic.Ring



/-!
# Translated resolvent barriers for the near-one argument

The barrier in this module is the resolvent barrier based at the terminal
point `(1, v0)`, normalized to have value the reciprocal cosh factor there.
All operator identities are pointwise in the coefficient field.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic


open scoped MatrixOrder

variable {d : ℕ}

variable (a rho : ℝ) (v0 : PDE.Vec d) (z : TimeVelocity d)

/-- The resolvent barrier translated to the terminal point `(1, v0)`. -/
def translatedResolventBarrier   : ℝ :=
  resolventBarrier a rho (z.1 - 1, z.2 - v0)

/-- The translated resolvent barrier normalized by its forward-boundary cosh
factor. -/
def normalizedTranslatedResolventBarrier   : ℝ :=
  translatedResolventBarrier a rho v0 z / Real.cosh (a * Real.sqrt rho / 4)

/-- Translation from the terminal centre to the resolvent barrier coordinates. -/
def terminalTranslation  (v0 : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z => z - (1, v0)

private theorem translatedResolventBarrier_eq_comp  (a rho : ℝ)
    (v0 : PDE.Vec d) :
    translatedResolventBarrier a rho v0 =
      resolventBarrier a rho ∘ terminalTranslation v0 := rfl

variable (v0 : PDE.Vec d)

private theorem contDiff_terminalTranslation   :
    ContDiff ℝ 2 (terminalTranslation v0) := contDiff_id.sub contDiff_const



variable (a rho : ℝ) (v0 : PDE.Vec d)

/-- The translated resolvent barrier is globally twice continuously
differentiable. -/
theorem contDiff_translatedResolventBarrier   :
    ContDiff ℝ 2 (translatedResolventBarrier a rho v0) := by
  rw [translatedResolventBarrier_eq_comp]
  exact (contDiff_resolventBarrier a rho).comp (contDiff_terminalTranslation v0)

/-- The normalized translated resolvent barrier is globally twice continuously
differentiable. -/
theorem contDiff_normalizedTranslatedResolventBarrier   :
    ContDiff ℝ 2 (normalizedTranslatedResolventBarrier a rho v0) := by
  unfold normalizedTranslatedResolventBarrier
  exact (contDiff_translatedResolventBarrier a rho v0).div_const _

private theorem fderiv_translatedResolventBarrier   (z : TimeVelocity d) :
    fderiv ℝ (translatedResolventBarrier a rho v0) z =
      fderiv ℝ (resolventBarrier a rho) (terminalTranslation v0 z) := by
  rw [translatedResolventBarrier_eq_comp]
  have hbar := (contDiff_resolventBarrier a rho).differentiable (by norm_num)
    (terminalTranslation v0 z)
  have hcomp := hbar.hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (1, v0))
  simpa only [ContinuousLinearMap.comp_id] using hcomp.fderiv

private theorem fderiv_fderiv_translatedResolventBarrier   (z w1 w2 : TimeVelocity d) :
    fderiv ℝ (fderiv ℝ (translatedResolventBarrier a rho v0)) z w1 w2 =
      fderiv ℝ (fderiv ℝ (resolventBarrier a rho))
        (terminalTranslation v0 z) w1 w2 := by
  have hfirst : fderiv ℝ (translatedResolventBarrier a rho v0) =
      fun x => fderiv ℝ (resolventBarrier a rho) (terminalTranslation v0 x) := by
    funext x
    exact fderiv_translatedResolventBarrier a rho v0 x
  rw [hfirst]
  have hbar := ((contDiff_resolventBarrier a rho).fderiv_right (m := 1)
    (by norm_num)).differentiable_one (terminalTranslation v0 z)
  have hcomp := hbar.hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (1, v0))
  have hcompApply := congrArg (fun L : TimeVelocity d →L[ℝ] TimeVelocity d →L[ℝ] ℝ =>
    L w1 w2) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using hcompApply

variable (z : TimeVelocity d)

private theorem timeDerivative_translatedResolventBarrier    :
    timeDerivative (translatedResolventBarrier a rho v0) z =
      timeDerivative (resolventBarrier a rho) (terminalTranslation v0 z) := by
  unfold timeDerivative
  rw [fderiv_translatedResolventBarrier]

private theorem velocityHessian_translatedResolventBarrier    :
    velocityHessian (translatedResolventBarrier a rho v0) z =
      velocityHessian (resolventBarrier a rho) (terminalTranslation v0 z) := by
  ext <;> simp_all [velocityHessian, fderiv_fderiv_translatedResolventBarrier] <;> ring

variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem timeDerivative_div_const
    (hu : ContDiff ℝ 1 u) (c : ℝ) (z : TimeVelocity d) :
    timeDerivative (fun x => u x / c) z = timeDerivative u z / c := by
  unfold timeDerivative
  rw [show (fun x => u x / c) = fun x => c⁻¹ * u x by
    funext x; ring]
  rw [fderiv_const_mul (hu.differentiable (by norm_num) z)]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

private theorem velocityHessian_div_const
    (hu : ContDiff ℝ 2 u) (c : ℝ) (z : TimeVelocity d) :
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


  rw [(show fderiv ℝ (fun x => c⁻¹ • fderiv ℝ u x) z = c⁻¹ • fderiv ℝ (fderiv ℝ u) z from ((((hu.fderiv_right (m := 1) (by norm_num)).differentiable_one z)).hasFDerivAt.const_smul c⁻¹).fderiv)]
  simp only [_root_.smul_apply, smul_eq_mul]

variable (A : CoefficientField d) (a rho : ℝ) (v0 : PDE.Vec d) (z : TimeVelocity d)

/-- Exact translation of the project operator to the coefficient matrix at
the original point. -/
theorem parabolicOperator_translatedResolventBarrier
     :
    parabolicOperator A (translatedResolventBarrier a rho v0) z =
      parabolicOperator (fun _ _ => coefficientAt A z) (resolventBarrier a rho)
        (terminalTranslation v0 z) := by
  simp_all [timeDerivative_translatedResolventBarrier, velocityHessian_translatedResolventBarrier] <;> aesop

/-- Exact normalization of the translated resolvent operator. -/
theorem parabolicOperator_add_resolvent_normalizedTranslatedResolventBarrier
      :
    parabolicOperator A (normalizedTranslatedResolventBarrier a rho v0) z +
        rho * normalizedTranslatedResolventBarrier a rho v0 z =
      (Real.cosh (a * Real.sqrt rho / 4))⁻¹ *
        (parabolicOperator (fun _ _ => coefficientAt A z) (resolventBarrier a rho)
          (terminalTranslation v0 z) +
          rho * resolventBarrier a rho (terminalTranslation v0 z)) := by
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
      rfl
    _ = _ := rfl

/-- The translated normalized barrier has the exact reciprocal-cosh value at
its terminal centre. -/
theorem normalizedTranslatedResolventBarrier_target
    (a rho : ℝ) (v0 : PDE.Vec d) :
    normalizedTranslatedResolventBarrier a rho v0 (1, v0) =
      (Real.cosh (a * Real.sqrt rho / 4))⁻¹ := by
  simp [normalizedTranslatedResolventBarrier, translatedResolventBarrier,
    resolventBarrier, resolventPhase, PDE.vecNormSq, PDE.vecDot]

/-- A parameter chosen before the coefficient, point, and centre gives a
strictly positive normalized translated resolvent expression. -/
theorem exists_normalizedTranslatedResolventBarrier_strict_sign
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ a > 0, ∀ rho > 1, ∀ A : CoefficientField d, ∀ z v0,
      z.2 - v0 ∈ velocityCube 0 1 →
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z →
      coefficientAt A z ≤ Lam • (1 : PDE.Mat d) →
      0 < parabolicOperator A (normalizedTranslatedResolventBarrier a rho v0) z +
        rho * normalizedTranslatedResolventBarrier a rho v0 z := by
  obtain ⟨a, ha, hsign⟩ :=
    exists_resolventBarrier_strict_sign_of_mem_velocityCube lam Lam hlam hlamLam
  refine ⟨a, ha, ?_⟩
  intro rho hrho A z v0 hz hlower hupper
  rw [parabolicOperator_add_resolvent_normalizedTranslatedResolventBarrier]

  apply mul_pos (inv_pos.mpr (Real.cosh_pos _))
  exact hsign rho hrho (fun _ _ => coefficientAt A z) (terminalTranslation v0 z) (hz) hlower hupper

private theorem resolventPhase_localABPAffine  (a rho : ℝ)
    (v0 : PDE.Vec d) (w : TimeVelocity d) :
    resolventPhase a rho (terminalTranslation v0 (localABPAffine v0 w)) =
      (a * Real.sqrt rho / 4) * (PDE.vecNormSq w.2 + 1 - w.1) := by
  unfold resolventPhase terminalTranslation localABPAffine parabolicAffine
  simp [PDE.vecNormSq_smul]
  ring

variable {a rho : ℝ} {v0 : PDE.Vec d}

private theorem one_le_normalizedTranslatedResolventBarrier_localABPAffine
      (w : TimeVelocity d)
    (ha : 0 < a) (hrho : 1 < rho)
    (hbracketFinal : 1 ≤ PDE.vecNormSq w.2 + 1 - w.1) :
    1 ≤ normalizedTranslatedResolventBarrier a rho v0 (localABPAffine v0 w) := by


  have hfactor : 0 ≤ a * Real.sqrt rho / 4 := by positivity
  have harg : a * Real.sqrt rho / 4 ≤
      (a * Real.sqrt rho / 4) * (PDE.vecNormSq w.2 + 1 - w.1) :=
    calc
      a * Real.sqrt rho / 4 = (a * Real.sqrt rho / 4) * 1 := by ring
      _ ≤ (a * Real.sqrt rho / 4) * (PDE.vecNormSq w.2 + 1 - w.1) :=
        mul_le_mul_of_nonneg_left hbracketFinal hfactor



  have hcosh : Real.cosh (a * Real.sqrt rho / 4) ≤
      Real.cosh ((a * Real.sqrt rho / 4) *
        (PDE.vecNormSq w.2 + 1 - w.1)) := by
    rw [Real.cosh_le_cosh]
    simpa only [abs_of_nonneg hfactor, abs_of_nonneg (mul_nonneg hfactor (zero_le_one.trans hbracketFinal))] using harg
  change 1 ≤ Real.cosh (resolventPhase a rho
      (terminalTranslation v0 (localABPAffine v0 w))) /
      Real.cosh (a * Real.sqrt rho / 4)
  rw [resolventPhase_localABPAffine]
  exact (le_div_iff₀ (Real.cosh_pos _)).mpr (by simpa using hcosh)

/-- The normalized translated barrier is at least one on the actual initial
or lateral boundary of the local round ABP cylinder. -/
theorem one_le_normalizedTranslatedResolventBarrier_on_localABPForwardBoundary

    (ha : 0 < a) (hrho : 1 < rho) {z : TimeVelocity d}
    (hz : z ∈ localABPForwardBoundary v0) :
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
      change PDE.euclideanSqDist w.2 (0 ) = 1 ^ 2 at hSphere
      simpa [PDE.euclideanSqDist] using hSphere
    rw [hnorm]
    linarith

end HypoellipticAleksandrov.Parabolic
