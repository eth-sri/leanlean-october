module

public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.W1p.Algebra
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import PDEFoundation.Sobolev.W1p.Truncation
public import PDEFoundation.Sobolev.W1p.ZeroBoundary
public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.H1.ZeroBoundary

@[expose] public noncomputable section

namespace PDE
section
open scoped ENNReal

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Multiply a representative-level Sobolev function by a smooth multiplier
whose value and first coordinate derivatives are essentially bounded on the
domain. -/
noncomputable def mulContDiffMemLpTop [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
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
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      classicalGradient_apply]

@[simp]
theorem mulContDiffMemLpTop_toFun [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
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
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
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
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    eLpNormOn U p
        (u.mulContDiffMemLpTop hφ hφTop hDφTop).toFun ≤
      eLpNormOn U ∞ φ * eLpNormOn U p u.toFun := by
  exact
    MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (f := u.toFun) p hφTop.aestronglyMeasurable

/-- Coordinatewise gradient cost of a smooth `L∞` multiplier. Both terms in
the product rule remain visible. -/
theorem eLpNormOn_mulContDiffMemLpTop_grad_coord_le
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
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
          eLpNormOn U p u.toFun := by
  let first : Vec d → ℝ :=
    fun x => φ x * u.grad x i
  let second : Vec d → ℝ :=
    fun x => u x * classicalGradient φ x i
  have hfirstMem : MemLpOn U p first := by
    simpa only [first, mul_comm] using
      (u.gradMemLp i).fun_mul hφTop
  have hsecondMem : MemLpOn U p second := by
    simpa only [second, mul_comm] using
      u.memLp.fun_mul (hDφTop i)
  have hfirstBound :
      eLpNormOn U p first ≤
        eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) := by
    exact
      MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
        (f := fun x => u.grad x i) p hφTop.aestronglyMeasurable
  have hsecondBound :
      eLpNormOn U p second ≤
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
    calc
      eLpNormOn U p second =
          eLpNormOn U p
            (fun x => classicalGradient φ x i * u x) := by
        apply MeasureTheory.eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [second, mul_comm]
      _ ≤ eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
        exact
          MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
            (f := u.toFun) p (hDφTop i).aestronglyMeasurable
  calc
    eLpNormOn U p
        (fun x =>
          (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i) =
        eLpNormOn U p (first + second) := rfl
    _ ≤ eLpNormOn U p first + eLpNormOn U p second := by
      exact MeasureTheory.eLpNorm_add_le Fact.out
    _ ≤ eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) +
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun :=
      add_le_add hfirstBound hsecondBound

/-- Compact support supplies the required `L∞` hypotheses automatically. -/
noncomputable def mulContDiffHasCompactSupport
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
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
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).toFun =
      fun x => φ x * u x := by
  simp only [mulContDiffHasCompactSupport,
    mulContDiffMemLpTop_toFun]

@[simp]
theorem mulContDiffHasCompactSupport_grad
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x := by
  simp only [mulContDiffHasCompactSupport,
    mulContDiffMemLpTop_grad]

end W1pFunction

end
section
open scoped ENNReal

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Multiply an `H¹` representative by a smooth multiplier whose value and
coordinate gradient are essentially bounded on the domain.

This is the LIH-compatible `p = 2` specialization of
`W1pFunction.mulContDiffMemLpTop`.
-/
noncomputable def mulContDiffMemLpTop
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    H1Function U :=
  (W1pFunction.mulContDiffMemLpTop
    u.toW1pFunction hφ hφTop hDφTop).toH1Function



/-- A smooth compactly supported multiplier preserves representative-level
`H¹`; compact support supplies the required `L∞` hypotheses. -/
noncomputable def mulContDiffHasCompactSupport
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    H1Function U :=
  (W1pFunction.mulContDiffHasCompactSupport
    u.toW1pFunction hφ hφCompact).toH1Function

@[simp]
theorem mulContDiffHasCompactSupport_toFun
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).toFun =
      fun x => φ x * u x := by
  simp only [mulContDiffHasCompactSupport,
    W1pFunction.toH1Function_toFun,
    W1pFunction.mulContDiffHasCompactSupport_toFun,
    H1Function.toW1pFunction_apply]

@[simp]
theorem mulContDiffHasCompactSupport_grad
    (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x := by
  simp only [mulContDiffHasCompactSupport,
    W1pFunction.toH1Function_grad,
    W1pFunction.mulContDiffHasCompactSupport_grad,
    H1Function.toW1pFunction_grad,
    H1Function.toW1pFunction_apply]

end H1Function

end
section
open scoped ENNReal Topology

open Filter MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U inner outer : Set (Vec d)}
variable {p : ℝ≥0∞} {K : ℝ}

/-- The zero Sobolev function has a constant zero supported smooth approximation. -/
noncomputable def zeroSupportedSmoothApproximation [Fact (1 ≤ p)] :
    (0 : W1pFunction U p).SupportedSmoothApproximation :=
  { approx := fun _ => 0
    approx_smooth := fun _ => contDiff_zero_fun
    approx_hasCompactSupport := fun _ => HasCompactSupport.zero
    approx_tsupport_subset := fun _ => by simp only [tsupport_zero, Set.empty_subset]
    tendsto_value := by
      simpa only [zero_toFun, sub_self, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    tendsto_grad := fun i => by
      have hZero :
          (fun n : ℕ =>
            eLpNorm
              (fun x =>
                (fderiv ℝ (0 : Vec d → ℝ) x) (basisVec i) -
                  (0 : W1pFunction U p).grad x i)
              p (volumeOn U)) = fun _ => 0 := by
        funext n
        calc
          eLpNorm
              (fun x =>
                (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i) -
                  (0 : W1pFunction U p).grad x i)
              p (volumeOn U) =
              eLpNorm (0 : Vec d → ℝ) p (volumeOn U) := by
            apply eLpNorm_congr_ae
            exact Eventually.of_forall fun x => by
              change (fderiv ℝ (0 : Vec d → ℝ) x) (basisVec i) - 0 = 0
              rw [fderiv_zero]
              simp only [Pi.zero_apply, zero_apply, sub_zero]
          _ = 0 := eLpNorm_zero
      simpa only [hZero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) }

/-- A globally smooth multiplier supported in `U` turns a finite-exponent
Sobolev representative into one with a supported smooth approximation. -/
noncomputable def supportedSmoothApproximation_mulContDiffHasCompactSupport
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφCompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    (u.mulContDiffHasCompactSupport hφ hφCompact).SupportedSmoothApproximation := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  by_cases htsupport : tsupport φ = ∅
  · have hφZero : φ = 0 := tsupport_eq_empty_iff.mp htsupport
    have hMulZero : u.mulContDiffHasCompactSupport hφ hφCompact = 0 := by
      have hGradientZero : classicalGradient (0 : Vec d → ℝ) = 0 := by
        funext x i
        rw [classicalGradient_apply, fderiv_zero]
        rfl
      apply W1pFunction.ext
      · rw [mulContDiffHasCompactSupport_toFun, hφZero, zero_toFun]
        funext x
        simp only [Pi.zero_apply, zero_mul]
      · rw [mulContDiffHasCompactSupport_grad, hφZero, hGradientZero, zero_grad]
        funext x
        ext i
        simp only [Pi.zero_apply, zero_smul, smul_zero, Pi.add_apply, add_zero]
    simpa only [hMulZero] using (zeroSupportedSmoothApproximation (U := U) (p := p))
  · let x0 : Vec d := Classical.choose (Set.nonempty_iff_ne_empty.mpr htsupport)
    have hx0 : x0 ∈ tsupport φ :=
      Classical.choose_spec (Set.nonempty_iff_ne_empty.mpr htsupport)
    have hx0U : x0 ∈ U := hφU hx0
    have hnhds : ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ U :=
      Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0U)
    let r : ℝ := Classical.choose hnhds / 2
    have hr : 0 < r := by
      dsimp only [r]
      exact half_pos (Classical.choose_spec hnhds).1
    have hball : Metric.closedBall x0 r ⊆ U := by
      apply (Metric.closedBall_subset_ball (half_lt_self (Classical.choose_spec hnhds).1)).trans
      exact (Classical.choose_spec hnhds).2
    let v : ℕ → W1pFunction U p :=
      convexApproxSmoothW1p hU hp u x0 hr
    refine
      { approx := fun n => φ * (v n).toFun
        approx_smooth := fun n => hφ.mul
          (contDiff_convexApproxSmoothW1p_toFun hU hp u x0 hr n)
        approx_hasCompactSupport := fun n => by
          simpa only [Pi.mul_apply, mul_comm] using hφCompact.mul_left
            (f := (v n).toFun)
        approx_tsupport_subset := fun n =>
          (tsupport_mul_subset_left (f := φ) (g := (v n).toFun)).trans hφU
        tendsto_value := ?_
        tendsto_grad := ?_ }
    · have hRaw :
          Tendsto
            (fun n =>
              eLpNormOn U p
                ((v n - u).mulContDiffHasCompactSupport hφ hφCompact).toFun)
            atTop (𝓝 0) := by
        let C : ℝ≥0∞ := eLpNormOn U ∞ φ
        have hCFinite : C ≠ ∞ := by
          dsimp only [C]
          exact ((hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U).eLpNorm_lt_top.ne
        have hConv :=
          tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp hpTop u hball hr
        have hUpper :
            Tendsto
              (fun n => C * eLpNormOn U p (fun x => (v n).toFun x - u.toFun x))
              atTop (𝓝 0) := by
          have h := ENNReal.Tendsto.const_mul hConv (Or.inr hCFinite)
          rw [mul_zero] at h
          exact h
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds hUpper (Eventually.of_forall fun _ => zero_le) ?_
        exact Eventually.of_forall fun n => by
          exact
            (v n - u).eLpNormOn_mulContDiffMemLpTop_toFun_le
              hφ
              ((hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U)
              (fun i => by
                have hContinuous : Continuous (fun x => classicalGradient φ x i) := by
                  simpa only [classicalGradient_apply] using
                    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
                have hCompact : HasCompactSupport (fun x => classicalGradient φ x i) := by
                  simpa only [classicalGradient_apply] using
                    hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
                exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U)
      refine hRaw.congr' ?_
      filter_upwards with n
      apply congrArg (fun f => eLpNorm f p (volumeOn U))
      funext x
      simp only [v, mulContDiffHasCompactSupport_toFun, sub_toFun,
        Pi.mul_apply, Pi.sub_apply]
      ring
    · intro i
      have hValue :=
        tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp hpTop u hball hr
      have hGradient :=
        tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
          hU hp hpTop u hball hr i
      have hφTop : MemLpOn U ∞ φ :=
        (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U
      have hDφTop : ∀ j : Fin d, MemLpOn U ∞
          (fun x => classicalGradient φ x j) := by
        intro j
        have hContinuous : Continuous (fun x => classicalGradient φ x j) := by
          simpa only [classicalGradient_apply] using
            (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
        have hCompact : HasCompactSupport (fun x => classicalGradient φ x j) := by
          simpa only [classicalGradient_apply] using
            hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec j)
        exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U
      have hUpper :
          Tendsto
            (fun n =>
              eLpNormOn U ∞ φ *
                  eLpNormOn U p (fun x => (v n).grad x i - u.grad x i) +
                eLpNormOn U ∞ (fun x => classicalGradient φ x i) *
                  eLpNormOn U p (fun x => (v n).toFun x - u.toFun x))
            atTop (𝓝 0) := by
        have hφFinite : eLpNormOn U ∞ φ ≠ ∞ := hφTop.eLpNorm_lt_top.ne
        have hDφFinite : eLpNormOn U ∞ (fun x => classicalGradient φ x i) ≠ ∞ :=
          (hDφTop i).eLpNorm_lt_top.ne
        have h := (ENNReal.Tendsto.const_mul hGradient (Or.inr hφFinite)).add
          (ENNReal.Tendsto.const_mul hValue (Or.inr hDφFinite))
        rw [mul_zero, mul_zero, add_zero] at h
        exact h
      have hRaw :
          Tendsto
            (fun n => eLpNormOn U p
              (fun x => ((v n - u).mulContDiffHasCompactSupport hφ hφCompact).grad x i))
            atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds hUpper (Eventually.of_forall fun _ => zero_le) ?_
        exact Eventually.of_forall fun n =>
          (v n - u).eLpNormOn_mulContDiffMemLpTop_grad_coord_le hφ hφTop hDφTop i
      refine hRaw.congr' ?_
      filter_upwards with n
      apply congrArg (fun f => eLpNorm f p (volumeOn U))
      funext x
      rw [fderiv_mul
        (hφ.differentiable (by simp) x)
        ((contDiff_convexApproxSmoothW1p_toFun hU hp u x0 hr n).differentiable
          (by simp) x)]
      simp only [v, mulContDiffHasCompactSupport_grad, sub_toFun, sub_grad,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        add_apply, smul_apply]
      rw [← classicalGradient_apply, ← classicalGradient_apply]
      have hGrad :
          classicalGradient (convexApproxSmoothW1p hU hp u x0 hr n).toFun =
            (convexApproxSmoothW1p hU hp u x0 hr n).grad := by
        rw [convexApproxSmoothW1p_toFun]
        exact (convexApproxSmoothW1p_grad hU hp u x0 hr n).symm
      rw [hGrad]
      ring


end W1pFunction

end

namespace H1Function

variable {d : ℕ} {U inner outer : Set (Vec d)} {K : ℝ}

/-- Multiplication by a globally smooth compactly supported function whose
topological support lies in `U` has an explicit supported smooth
approximation. -/
noncomputable def
    supportedSmoothApproximation_mulContDiffHasCompactSupport
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).SupportedSmoothApproximation := by
  exact
    u.toW1pFunction.supportedSmoothApproximation_mulContDiffHasCompactSupport
      hU (by norm_num) (by norm_num) hφ hφCompact hφU

/-- LIH-compatible constructor: a globally smooth compactly supported
multiplier turns an `H1Function` into a concrete `H10Function`. -/
noncomputable def mulContDiffHasCompactSupportToH10
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    H10Function U :=
  (u.mulContDiffHasCompactSupport hφ hφCompact).toH10Function
    (u.supportedSmoothApproximation_mulContDiffHasCompactSupport
      hU hφ hφCompact hφU)

@[simp]
theorem mulContDiffHasCompactSupportToH10_toH1Function
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (u.mulContDiffHasCompactSupportToH10
      hU hφ hφCompact hφU).toH1Function =
        u.mulContDiffHasCompactSupport hφ hφCompact :=
  rfl

@[simp]
theorem mulContDiffHasCompactSupportToH10_toFun
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (u.mulContDiffHasCompactSupportToH10
      hU hφ hφCompact hφU).toH1Function.toFun =
        fun x => φ x * u x := by
  rw [mulContDiffHasCompactSupportToH10_toH1Function,
    mulContDiffHasCompactSupport_toFun]

@[simp]
theorem mulContDiffHasCompactSupportToH10_grad
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (u.mulContDiffHasCompactSupportToH10
      hU hφ hφCompact hφU).toH1Function.grad =
        fun x =>
          φ x • u.grad x + u x • classicalGradient φ x := by
  rw [mulContDiffHasCompactSupportToH10_toH1Function,
    mulContDiffHasCompactSupport_grad]

end H1Function

end PDE

