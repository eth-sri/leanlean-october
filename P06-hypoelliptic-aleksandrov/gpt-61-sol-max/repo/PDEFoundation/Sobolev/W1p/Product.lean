module

public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.W1p.Algebra
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Smooth multipliers on representative-level `W^{1,p}`

A smooth scalar multiplier preserves `W^{1,p}` when its value and coordinate
gradient are essentially bounded on the domain. The stored weak gradient is
the exact product-rule expression

`φ Du + u Dφ`.

The exponent hypothesis `1 ≤ p` is needed only to obtain the local
integrability required by the raw distributional product rule.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Multiply a representative-level Sobolev function by a smooth multiplier
whose value and first coordinate derivatives are essentially bounded on the
domain. -/
noncomputable def mulContDiffMemLpTop [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    W1pFunction U p where
  toFun := fun x => φ x * u x
  grad := fun x =>
    φ x • u.grad x + u x • classicalGradient φ x
  memLp := by
    simpa only [mul_comm] using u.memLp.fun_mul hφTop
  gradMemLp := by
    intro i
    have hfirst :
        MemLpOn U p (fun x => φ x * u.grad x i) := by
      simpa only [mul_comm] using
        (u.gradMemLp i).fun_mul hφTop
    have hsecond :
        MemLpOn U p
          (fun x => u x * classicalGradient φ x i) :=
      by
        simpa only [mul_comm] using
          u.memLp.fun_mul (hDφTop i)
    exact hfirst.add hsecond
  hasWeakGradient := by
    convert u.hasWeakGradient.mul_contDiff hφ
      u.locallyIntegrable_toFun u.locallyIntegrable_grad using 1
    funext x i
    rfl

@[simp]
theorem mulContDiffMemLpTop_toFun [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    (u.mulContDiffMemLpTop hφ hφTop hDφTop).toFun =
      fun x => φ x * u x :=
  rfl

@[simp]
theorem mulContDiffMemLpTop_grad [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x :=
  rfl

/-- Exact multiplier cost for the value component. -/
theorem eLpNormOn_mulContDiffMemLpTop_toFun_le
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    eLpNormOn U p
        (u.mulContDiffMemLpTop hφ hφTop hDφTop).toFun ≤
      eLpNormOn U ∞ φ * eLpNormOn U p u.toFun := MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (f := u.toFun) p hφTop.aestronglyMeasurable

/-- Coordinatewise gradient cost of a smooth `L∞` multiplier. Both terms in
the product rule remain visible. -/
theorem eLpNormOn_mulContDiffMemLpTop_grad_coord_le
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i))
    (i : Fin d) :
    eLpNormOn U p
        (fun x =>
          (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i) ≤
      eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) +
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := (Trans.trans
  (Trans.trans (Eq.refl (eLpNormOn U p fun x => (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i))
    (MeasureTheory.eLpNorm_add_le Fact.out))
  (add_le_add (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p (MeasureTheory.MemLp.aestronglyMeasurable hφTop))
    (Trans.trans
      (MeasureTheory.eLpNorm_congr_ae
        (Filter.Eventually.of_forall fun x =>
          of_eq_true
            (Eq.trans
              (congrFun' (congrArg Eq (congrFun' (funext fun x => mul_comm (u.toFun x) (classicalGradient φ x i)) x))
                (classicalGradient φ x i * u.toFun x))
              (eq_self (classicalGradient φ x i * u.toFun x)))))
      (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p (MeasureTheory.MemLp.aestronglyMeasurable (hDφTop i))))))

/-- Compact support supplies the required `L∞` hypotheses automatically. -/
noncomputable def mulContDiffHasCompactSupport
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) :
    W1pFunction U p := by
  have hφTop : MemLpOn U ∞ φ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U
  have hDφTop :
      ∀ i : Fin d,
        MemLpOn U ∞
          (fun x => classicalGradient φ x i) := by
    intro i
    have hDφCont :
        Continuous (fun x => classicalGradient φ x i) := by
      simpa only [classicalGradient_apply] using
        (hφ.continuous_fderiv (by simp)).clm_apply
          continuous_const
    have hDφCompact :
        HasCompactSupport
          (fun x => classicalGradient φ x i) := by
      simpa only [classicalGradient_apply] using
        hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact
      (hDφCont.memLp_of_hasCompactSupport hDφCompact).restrict U
  exact u.mulContDiffMemLpTop hφ hφTop hDφTop

@[simp]
theorem mulContDiffHasCompactSupport_toFun
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).toFun =
      fun x => φ x * u x := by
  rfl

@[simp]
theorem mulContDiffHasCompactSupport_grad
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x := by
  rfl

end W1pFunction

end PDE
