module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1: regularity of `ρ`

* `continuous_rho` (in `Prop21Rho`): `x ↦ ρ_Δ(x)` is continuous;
* `analyticAt_rho`: for fixed `Δ < -1`, `x ↦ ρ_Δ(x)` is real analytic.  The cosine series
  `R(α) = 1/2 + ∑ cos(mα)/cosh(λ m)` extends to a holomorphic function on the strip
  `|Im z| < λ/2` (`differentiableOn_RsechC`, Weierstrass M-test), and `k^{-1}`, `Ξ_λ` are explicit
  analytic functions;
* `continuousOn_rho_joint`: `(Δ, x) ↦ ρ_Δ(x)` is jointly continuous on `{Δ < -1} × ℝ`.

*Joint real-analyticity in `(Δ, x)` is not proved here*: it needs holomorphy of a series of
functions of two complex variables (Osgood's lemma), which is not available in Mathlib.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    simp [Complex.norm_exp]
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    simp [Complex.norm_exp]
  calc _
      ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 := by
        rw [norm_div]; simp only [Complex.norm_ofNat]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ _ := by
        have a1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
        have a2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
        linarith

/-- The holomorphic extension of the cosine series of `R` to a horizontal strip. -/
noncomputable def RsechC (lam : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + ∑' n : ℕ, (secCoeff lam n) * Complex.cos ((n + 1 : ℕ) * z)

section
variable {lam : ℝ} (hlam : 0 < lam) (α : ℝ)
include hlam

theorem differentiableOn_RsechC :
    DifferentiableOn ℂ (RsechC lam) {z : ℂ | |z.im| < lam / 2} := by
  have hr1 : Real.exp (-(lam / 2)) < 1 := by grind [Real.exp_lt_one_iff]
  have hu : Summable (fun n : ℕ => 2 * Real.exp (-(lam / 2)) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left (2 * Real.exp (-(lam / 2)))
    grind
  have h := Complex.differentiableOn_tsum_of_summable_norm (U := {z : ℂ | |z.im| < lam / 2})
    (F := fun n z => (secCoeff lam n) * Complex.cos ((n + 1 : ℕ) * z)) hu
    (fun n => (by fun_prop : Differentiable ℂ (fun z : ℂ =>
      (secCoeff lam n) * Complex.cos ((n + 1 : ℕ) * z))).differentiableOn)
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
    (fun n z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (secCoeff_pos lam n)]
      have h1 := norm_cos_le_exp_abs_im ((n + 1 : ℕ) * z)
      have h2 : |((n + 1 : ℕ) * z).im| ≤ (n + 1 : ℕ) * (lam / 2) := by
        have : ((n + 1 : ℕ) * z).im = (n + 1 : ℕ) * z.im := by
          simp
        rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (le_of_lt hz) (Nat.cast_nonneg _)
      have h3 : Real.exp |((n + 1 : ℕ) * z).im| ≤ Real.exp (lam / 2) ^ (n + 1) := by
        calc _ ≤ Real.exp ((n + 1 : ℕ) * (lam / 2)) :=
              Real.exp_le_exp.2 h2
          _ = _ := by rw [← Real.exp_nat_mul]
      have h5 : 2 * Real.exp (-(lam / 2)) ^ (n + 1) =
          2 * Real.exp (-lam) ^ (n + 1) * Real.exp (lam / 2) ^ (n + 1) := by
        rw [mul_assoc, ← mul_pow, ← Real.exp_add]; ring_nf
      rw [h5]
      calc _
          ≤ _ := by
            apply mul_le_mul (secCoeff_le hlam n) (h1.trans h3) (norm_nonneg _) (by positivity))
  exact (differentiableOn_const _).add h

theorem RsechC_ofReal :
    RsechC lam α = (Rsech lam α : ℝ) := by
  have h := Rsech_eq_trigSeries hlam α
  unfold trigSeries at h
  have e : ∀ n : ℕ, secCoeff lam n * Real.cos ((n + 1 : ℕ) * α) +
      (fun _ : ℕ => 0) n * Real.sin ((n + 1 : ℕ) * α) =
      secCoeff lam n * Real.cos ((n + 1 : ℕ) * α) := fun n => by simp
  simp_rw [e] at h
  rw [h]
  unfold RsechC
  push_cast
  rfl

/-- `α ↦ R_λ(α)` is real analytic. -/
theorem analyticAt_Rsech : AnalyticAt ℝ (Rsech lam) α := by
  have hU : {z : ℂ | |z.im| < lam / 2} ∈ 𝓝 ↑α := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    · simp; positivity
  have h2 := ((differentiableOn_RsechC hlam).analyticAt hU).re_ofReal
  simp_all [RsechC_ofReal hlam, Complex.ofReal_re]

theorem analyticAt_Xi : AnalyticAt ℝ (Xi lam) α := by
  have h2 := Real.one_lt_cosh.mpr hlam.ne'
  have := Real.cos_le_one α
  exact analyticAt_const.div (analyticAt_const.sub Real.analyticAt_cos) (by linarith)

end

/-- **Analyticity of `ρ_Δ` in `x`** (fixed `Δ < -1`). -/
theorem analyticAt_rho {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : AnalyticAt ℝ (rho Δ) x := by
  have hlam := lamOf_pos hΔ
  have hk := analyticAt_kInv hlam x
  have hR :=
    (analyticAt_Rsech hlam _).comp hk
  have hX :=
    (analyticAt_Xi hlam _).comp hk
  have  := funext (rho_eq hΔ)
  rw [this]
  refine hR.div (analyticAt_const.mul hX) ?_
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity

/-! ### Joint continuity in `(Δ, x)` -/

end PottsDiscontinuity.Bethe
