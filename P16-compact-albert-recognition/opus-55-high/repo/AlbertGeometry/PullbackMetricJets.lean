/-
The actual ambient normalized log-Hessian pulled
back along the original actual level chart. Derivatives below are literal
Frechet derivatives of the actual bilinear metric field. Whole-neighborhood
identities precede every differentiation. No connection/curvature jet is input.
-/
module

public import AlbertGeometry.LevelChartJets

@[expose] public section
open scoped ContDiff Topology

namespace AlbertGeometry.Cubic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section CanonicalPullbackMetricNorms

local instance pullbackMetricDualNormedAddCommGroup (P : SymmetricTrilinearForm E) (e : E) :
    NormedAddCommGroup (tangentSpace P e →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance pullbackMetricDualNormedSpace (P : SymmetricTrilinearForm E) (e : E) :
    NormedSpace ℝ (tangentSpace P e →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance pullbackMetricBilinearNormedAddCommGroup (P : SymmetricTrilinearForm E) (e : E) :
    NormedAddCommGroup (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance pullbackMetricBilinearNormedSpace (P : SymmetricTrilinearForm E) (e : E) :
    NormedSpace ℝ (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance pullbackMetricTrilinearNormedAddCommGroup (P : SymmetricTrilinearForm E) (e : E) :
    NormedAddCommGroup (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance pullbackMetricTrilinearNormedSpace (P : SymmetricTrilinearForm E) (e : E) :
    NormedSpace ℝ (tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Genuine pullback of the ambient -D²logN/3, not Hessian of log(N∘χ). -/
def pullbackMetric (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  (logHessianForm P (levelChartPoint P e he x)).bilinearComp
    (levelChartD1 P e he x) (levelChartD1 P e he x)

/-- Literal derivative of the actual bilinear metric field. -/
def pullbackMetricD1 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  fderiv ℝ (pullbackMetric P e he) x

/-- Literal derivative of that actual derivative field. -/
def pullbackMetricD2 (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ]
      tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  fderiv ℝ (pullbackMetricD1 P e he) x

/-- Smooth cubic expression later identified with the ACTUAL metric on U. -/
def pullbackMetricFormula (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (x : tangentSpace P e) :
    tangentSpace P e →L[ℝ] tangentSpace P e →L[ℝ] ℝ :=
  ((-2 : ℝ) • fullyCurried P (levelChartPoint P e he x)).bilinearComp
    (levelChartD1 P e he x) (levelChartD1 P e he x)

theorem contDiffAt_metric_bilinearComp
    {X Y Z A B F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → A →L[ℝ] B →L[ℝ] F}
    {g : X → Y →L[ℝ] A} {h : X → Z →L[ℝ] B} {x : X}
    (hf : ContDiffAt ℝ ⊤ f x)
    (hg : ContDiffAt ℝ ⊤ g x) (hh : ContDiffAt ℝ ⊤ h x) :
    ContDiffAt ℝ ⊤ (fun y => (f y).bilinearComp (g y) (h y)) x := by
  have := (LinearIsometryEquiv.contDiff (F := Y →L[ℝ] Z →L[ℝ] F)
    (ContinuousLinearMap.flipₗᵢ ℝ Z Y F)).contDiffAt.comp x
    (((LinearIsometryEquiv.contDiff (ContinuousLinearMap.flipₗᵢ ℝ Y B F)).contDiffAt.comp x (hf.clm_comp hg)).clm_comp hh)
  exact this

/-- Internal chain certificate only; no arbitrary derivative is assumed. -/
def metricTrilinearDerivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : SymmetricTrilinearForm E) (a b c : E) (da db dc : X →L[ℝ] E) :
    X →L[ℝ] ℝ :=
  (fullyCurried P a b).comp dc +
    ((fullyCurried P a).comp db).flip c +
    (((fullyCurried P).comp da).flip b).flip c

theorem hasFDerivAt_metricTrilinear
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : SymmetricTrilinearForm E) {a b c : X → E}
    {da db dc : X →L[ℝ] E} {x : X}
    (ha : HasFDerivAt a da x) (hb : HasFDerivAt b db x) (hc : HasFDerivAt c dc x) :
    HasFDerivAt (fun y => P.form ![a y, b y, c y])
      (metricTrilinearDerivative P (a x) (b x) (c x) da db dc) x := by
  have h := HasFDerivAt.comp (G := E →L[ℝ] E →L[ℝ] ℝ) x (fullyCurried P).hasFDerivAt ha
  have h := (h.clm_apply hb).clm_apply hc
  simp [Function.comp_apply, fullyCurried_apply] at h
  exact h.congr_fderiv (by ext; simp [metricTrilinearDerivative]; ring)

variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
local notation "χ" => levelChartPoint P e he
local notation "Dχ" => levelChartD1 P e he
local notation "DDχ" => levelChartD2 P e he
local notation "DDDχ" => levelChartD3 P e he
local notation "U" => smoothLevelChartDomain P e he
local notation "G" => pullbackMetric P e he
local notation "DG" => pullbackMetricD1 P e he
local notation "DDG" => pullbackMetricD2 P e he
local notation "a" => logHessianForm P e

@[simp] theorem pullbackMetric_apply (x u w : W) :
    G x u w = logHessianForm P (χ x) (Dχ x u) (Dχ x w) :=
  ContinuousLinearMap.bilinearComp_apply _ _ _ _ _

/-- Whole-domain identity from Nχ=1 and DNχ Dχ=0, before metric derivatives. -/
theorem pullbackMetric_eq_formula (x : W) (hx : x ∈ U) :
    G x = pullbackMetricFormula P e he x := by
  have hN := levelChartPoint_on_level P e he x (smoothLevelChartDomain_subset P e he hx)
  have hpos : 0 < diagonalCubic P.form (χ x) := by rw [hN]; norm_num
  ext u w
  rw [pullbackMetric_apply, logHessianForm_apply P hpos, hN,
    levelChartD1_norm P e he x hx u, levelChartD1_norm P e he x hx w,
    cubicHessian_apply]
  simp [pullbackMetricFormula, ContinuousLinearMap.bilinearComp_apply,
    smul_eq_mul, fullyCurried_apply]
  ring

theorem pullbackMetric_cubic_apply (x : W) (hx : x ∈ U) (u w : W) :
    G x u w = -2 * P.form ![χ x, Dχ x u, Dχ x w] := by
  rw [pullbackMetric_eq_formula P e he x hx]
  simp [pullbackMetricFormula, ContinuousLinearMap.bilinearComp_apply,
    smul_eq_mul, fullyCurried_apply]

/-- Smoothness follows on this same fixed U from the actual cubic identity. -/
theorem contDiffAt_pullbackMetric (x : W) (hx : x ∈ U) : ContDiffAt ℝ ⊤ G x := by
  have hF := (ContinuousLinearMap.contDiff (F := E →L[ℝ] E →L[ℝ] ℝ) ((-2 : ℝ) • fullyCurried P)).contDiffAt.comp x
    (contDiffAt_levelChartPoint_smoothDomain P e he ⊤ x hx)
  have h := contDiffAt_metric_bilinearComp hF (contDiffAt_levelChartD1 P e he x hx)
    (contDiffAt_levelChartD1 P e he x hx)
  exact (h : ContDiffAt ℝ ⊤ (pullbackMetricFormula P e he) x).congr_of_eventuallyEq
    (Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => pullbackMetric_eq_formula P e he y hy))

theorem hasFDerivAt_pullbackMetric (x : W) (hx : x ∈ U) : HasFDerivAt G (DG x) x :=
  ((contDiffAt_pullbackMetric P e he x hx).differentiableAt (by simp)).hasFDerivAt

theorem hasFDerivAt_pullbackMetricD1 (x : W) (hx : x ∈ U) :
    HasFDerivAt DG (DDG x) x :=
  (((contDiffAt_pullbackMetric P e he x hx).fderiv_right (m := ⊤) (by simp)).differentiableAt (by simp)).hasFDerivAt

/-- First actual metric derivative, established throughout U before differentiating again. -/
theorem pullbackMetricD1_formula (x : W) (hx : x ∈ U) (s u w : W) :
    DG x s u w = -2 *
      (P.form ![χ x, Dχ x u, DDχ x s w] +
        P.form ![χ x, DDχ x s u, Dχ x w] +
        P.form ![Dχ x s, Dχ x u, Dχ x w]) := by
  have hχ := hasFDerivAt_levelChartD0 P e he x hx
  have hD := hasFDerivAt_levelChartD1 P e he x hx
  have hf := (hasFDerivAt_metricTrilinear P hχ
    (eval_const_hasFDerivAt hD u)
    (eval_const_hasFDerivAt hD w)).const_smul (-2 : ℝ)
  have hc : (fun y => G y u w) =ᶠ[𝓝 x]
      (fun y => (-2 : ℝ) • P.form ![χ y, Dχ y u, Dχ y w]) :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => by
        simpa [Set.mem_ofPred_eq, smul_eq_mul] using
          pullbackMetric_cubic_apply P e he y hy u w)
  have hg := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt (hasFDerivAt_pullbackMetric P e he x hx) u) w
  have h := congrArg (fun L => L s)
    (hg.unique (hf.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, metricTrilinearDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, fullyCurried_apply] using h

section AlignedLevelChartVectorEvaluation

attribute [local instance] levelChartLinearNormedAddCommGroup levelChartLinearNormedSpace
  levelChartBilinearNormedAddCommGroup levelChartBilinearNormedSpace

/-- Actual second metric derivative: differentiate the whole-U first formula. -/
theorem pullbackMetricD2_formula (x : W) (hx : x ∈ U) (t s u w : W) :
    DDG x t s u w = -2 *
      ((P.form ![χ x, Dχ x u, DDDχ x t s w] +
        P.form ![χ x, DDχ x t u, DDχ x s w] +
        P.form ![Dχ x t, Dχ x u, DDχ x s w]) +
      (P.form ![χ x, DDχ x s u, DDχ x t w] +
        P.form ![χ x, DDDχ x t s u, Dχ x w] +
        P.form ![Dχ x t, DDχ x s u, Dχ x w]) +
      (P.form ![Dχ x s, Dχ x u, DDχ x t w] +
        P.form ![Dχ x s, DDχ x t u, Dχ x w] +
        P.form ![DDχ x t s, Dχ x u, Dχ x w])) := by
  have hχ := hasFDerivAt_levelChartD0 P e he x hx
  have hD := hasFDerivAt_levelChartD1 P e he x hx
  have hDD := hasFDerivAt_levelChartD2 P e he x hx
  have hDu := eval_const_hasFDerivAt hD u
  have hDw := eval_const_hasFDerivAt hD w
  have hDs := eval_const_hasFDerivAt hD s
  have hKs := eval_const_hasFDerivAt hDD s
  have hKsu := eval_const_hasFDerivAt hKs u
  have hKsw := eval_const_hasFDerivAt hKs w
  have hA := hasFDerivAt_metricTrilinear P hχ hDu hKsw
  have hB := hasFDerivAt_metricTrilinear P hχ hKsu hDw
  have hC := hasFDerivAt_metricTrilinear P hDs hDu hDw
  have hf := ((hA.add hB).add hC).const_smul (-2 : ℝ)
  have hc : (fun y => DG y s u w) =ᶠ[𝓝 x]
      (fun y => (-2 : ℝ) •
        (P.form ![χ y, Dχ y u, DDχ y s w] +
          P.form ![χ y, DDχ y s u, Dχ y w] +
          P.form ![Dχ y s, Dχ y u, Dχ y w])) :=
    Filter.mem_of_superset ((isOpen_smoothLevelChartDomain P e he).mem_nhds hx)
      (fun y hy => by
        simpa [Set.mem_ofPred_eq, smul_eq_mul] using
          pullbackMetricD1_formula P e he y hy s u w)
  have hg := eval_const_hasFDerivAt
    (eval_const_hasFDerivAt
      (eval_const_hasFDerivAt (hasFDerivAt_pullbackMetricD1 P e he x hx) s) u) w
  have h := congrArg (fun L => L t)
    (hg.unique (hf.congr_of_eventuallyEq hc))
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, metricTrilinearDerivative, ContinuousLinearMap.comp_apply, fullyCurried_apply] using h

end AlignedLevelChartVectorEvaluation

/-- The zero metric is the restriction of the actual ambient metric. -/
theorem pullbackMetric_zero (u w : W) : G 0 u w = a (u : E) (w : E) := by simp [pullbackMetric_apply, levelChartPoint_zero, levelChartD1_zero]

theorem metric_p_smul (r : ℝ) (x y z : E) :
    P.form ![r • x, y, z] = r * P.form ![x, y, z] ∧ P.form ![x, r • y, z] = r * P.form ![x, y, z] ∧
      P.form ![x, y, r • z] = r * P.form ![x, y, z] := by
  simp [← fullyCurried_apply, map_smul, smul_eq_mul, and_self]

include he in
theorem metric_p_tangent :
    (∀ u : W, P.form ![e, e, (u : E)] = 0) ∧ (∀ u : W, P.form ![e, (u : E), e] = 0) ∧
      (∀ u w : W, P.form ![e, (u : E), (w : E)] = -a u w / 2) ∧
      (∀ u w : W, P.form ![(u : E), e, (w : E)] = -a u w / 2) ∧
      (∀ u w : W, P.form ![(u : E), (w : E), e] = -a u w / 2) ∧ P.form ![e, e, e] = 1 := by
  have h1 (u : W) : P.form ![e, e, (u : E)] = 0 := by
    have h : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
    rw [fderiv_diagonalCubic_apply_symmetric] at h
    linarith
  have h2 (u w : W) : P.form ![e, (u : E), (w : E)] = -a u w / 2 := by
    have h := cubicHessian_tangent_at_one P e he u w
    rw [cubicHessian_apply] at h
    linarith
  have h3 : (fun _ => e) = ![e, e, e] := by
    ext i
    fin_cases i <;> rfl
  refine ⟨h1, fun u => ?_, h2, fun u w => ?_, fun u w => ?_, by simpa [diagonalCubic, h3] using he⟩
  · rw [P.swap23]
    exact h1 u
  · rw [P.swap12]
    exact h2 u w
  · rw [P.swap23, P.swap12]
    exact h2 u w

/-- Actual first metric derivative at zero is the tangent cubic -2P. -/
theorem pullbackMetricD1_zero (s u w : W) :
    DG 0 s u w = -2 * P.form ![(s : E), (u : E), (w : E)] := by
  rw [pullbackMetricD1_formula P e he 0 (zero_mem_smoothLevelChartDomain P e he)]
  simp [levelChartPoint_zero, levelChartD1_zero, levelChartD2_zero,
    metric_p_smul, metric_p_tangent P e he, mul_zero, zero_add, add_zero]

/-- The actual second metric derivative has no unproved prescribed coefficient.
Six normal terms cancel in pairs, leaving the factor a(t,s)a(u,w). -/
theorem pullbackMetricD2_zero (t s u w : W) :
    DDG 0 t s u w = a (t : E) (s : E) * a (u : E) (w : E) := by
  rw [pullbackMetricD2_formula P e he 0 (zero_mem_smoothLevelChartDomain P e he)]
  simp only [levelChartPoint_zero, levelChartD1_zero, levelChartD2_zero,
    levelChartD3_zero, metric_p_smul, metric_p_tangent P e he]
  ring

end CanonicalPullbackMetricNorms

end
end AlbertGeometry.Cubic
