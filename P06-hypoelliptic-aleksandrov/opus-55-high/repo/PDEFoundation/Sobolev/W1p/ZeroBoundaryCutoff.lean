module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Sobolev.W1p.Cutoff
public import PDEFoundation.Sobolev.W1p.Truncation
public import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-!
# Compactly supported multipliers have zero boundary values

This file combines finite-exponent smooth density on bounded open convex
domains with multiplication by globally smooth compactly supported functions.
The quantitative-cutoff theorem is a direct corollary of this common bridge.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

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
    approx_tsupport_subset := fun _ => by simp
    tendsto_value := by
      simp
    tendsto_grad := fun i => by
      have hZero :
          (fun n : ℕ =>
            eLpNorm
              (fun x =>
                (fderiv ℝ (0) x) (basisVec i) -
                  (0 : W1pFunction U p).grad x i)
              p (volumeOn U)) = fun _ => 0 := by
        simp
      simp }

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
      aesop
    simpa only [hMulZero] using (zeroSupportedSmoothApproximation (U := U) (p := p))
  · let x0 : Vec d := Classical.choose (Set.nonempty_iff_ne_empty.mpr htsupport)
    have hx0 : x0 ∈ tsupport φ :=
      Classical.choose_spec (Set.nonempty_iff_ne_empty.mpr htsupport)
    have hx0U : x0 ∈ U := hφU hx0
    have hnhds : ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ U :=
      Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0U)
    let r : ℝ := Classical.choose hnhds / 2
    have hr : 0 < r := by
      grind
    have hball : Metric.closedBall x0 r ⊆ U := by
      apply (Metric.closedBall_subset_ball (half_lt_self (Classical.choose_spec hnhds).1)).trans
      grind
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
        let C  := eLpNormOn U ∞ φ
        have hCFinite : C ≠ ∞ := ((hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U).eLpNorm_lt_top.ne
        have hConv :=
          tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp hpTop u hball hr
        have hUpper :
            Tendsto
              (fun n => C * eLpNormOn U p (fun x => (v n).toFun x - u.toFun x))
              atTop (𝓝 0) := by
          have h := ENNReal.Tendsto.const_mul hConv (Or.inr hCFinite)
          aesop
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
                    hφCompact.fderiv_apply (𝕜 := ℝ) _
                exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U)
      refine hRaw.congr' ?_
      filter_upwards with n
      apply congrArg (fun f => eLpNorm f p (volumeOn U))
      funext x
      simp only [mulContDiffHasCompactSupport_toFun, sub_toFun,
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
            hφCompact.fderiv_apply (𝕜 := ℝ) _
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
        have hDφFinite : eLpNormOn U ∞ _ ≠ ∞ :=
          (hDφTop i).eLpNorm_lt_top.ne
        have h := (ENNReal.Tendsto.const_mul hGradient (Or.inr hφFinite)).add
          (ENNReal.Tendsto.const_mul hValue (Or.inr hDφFinite))
        aesop
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
      simp only [mulContDiffHasCompactSupport_grad, sub_toFun, sub_grad,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        add_apply, smul_apply]
      rw [← classicalGradient_apply, ← classicalGradient_apply]
      have hGrad :
          classicalGradient (convexApproxSmoothW1p hU hp u x0 hr n).toFun =
            (convexApproxSmoothW1p hU hp u x0 hr n).grad := by
        simp
      rw [hGrad]
      ring

/-- The squared-cutoff positive part has the literal expected value
representative. -/
@[simp]
theorem mulCutoff_sq_positivePartSubConst_toFun
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (k : ℝ)
    (η : QuantitativeSmoothCutoff inner outer K) :
    ((u.positivePartSubConst hU hp hpTop k).mulCutoff η.sq hp).toFun =
      fun x => η x ^ 2 * max (u.toFun x - k) 0 := by
  simp

end W1pFunction

end PDE
