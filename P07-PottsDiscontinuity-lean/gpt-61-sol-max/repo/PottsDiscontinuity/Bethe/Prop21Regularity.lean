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
  
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  calc ‖(Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2‖
      ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 := by
        rw [norm_div]; simp only [Complex.norm_ofNat]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ Real.exp |z.im| := by
        
        have a1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
        have a2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
        linarith

/-- The holomorphic extension of the cosine series of `R` to a horizontal strip. -/
noncomputable def RsechC (lam : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + ∑' n : ℕ, (secCoeff lam n : ℂ) * Complex.cos (((n + 1 : ℕ) : ℂ) * z)

section

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

theorem differentiableOn_RsechC  :
    DifferentiableOn ℂ (RsechC lam) {z : ℂ | |z.im| < lam / 2} := by
  have hr : 0 < Real.exp (-(lam / 2)) := Real.exp_pos _
  have hr1 : Real.exp (-(lam / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  
  
  have h := Complex.differentiableOn_tsum_of_summable_norm (U := {z : ℂ | |z.im| < lam / 2})
    (F := fun n z =>  secCoeff lam n  * Complex.cos ( (n + 1 : ℕ)  * z)) (by
                                                                              have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-(lam / 2)))
                                                                              all_goals grind : Summable  fun n  => 2 * Real.exp (-(lam / 2)) ^ (n + 1))
    (fun n => (by fun_prop : Differentiable ℂ  fun z : ℂ =>
      (secCoeff lam n : ℂ) * Complex.cos (((n + 1 : ℕ) : ℂ) * z) ).differentiableOn)
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
    (fun n z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (secCoeff_pos lam n)]
      
      
      
      
      
      rw [(by
             rw [mul_assoc, ← mul_pow, ← Real.exp_add];  ring_nf : 2 * Real.exp (-(lam / 2)) ^ (n + 1) =
          2 * Real.exp (-lam) ^ (n + 1) * Real.exp (lam / 2) ^ (n + 1))]
      calc secCoeff lam n * ‖Complex.cos ( (n + 1 : ℕ)  * z)‖
          ≤  2 * Real.exp (-lam) ^ (n + 1)  * Real.exp (lam / 2) ^ (n + 1) := by
            apply mul_le_mul (secCoeff_le hlam n) ((norm_cos_le_exp_abs_im ( (n + 1 : ℕ)  * z)).trans (by
                                                                                                             calc Real.exp |(((n + 1 : ℕ) : ℂ) * z).im| ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (lam / 2)) :=
                                                                                                                   Real.exp_le_exp.2 (by
                                                                                                                                        
                                                                                                                                        rw [(by
                                                                                                                                               rw [Complex.mul_im]; simp : (((n + 1 : ℕ) : ℂ) * z).im = ((n + 1 : ℕ) : ℝ) * z.im), abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
                                                                                                                                        exact mul_le_mul_of_nonneg_left (le_of_lt hz) (Nat.cast_nonneg _))
                                                                                                               _ = Real.exp (lam / 2) ^ (n + 1) := by rw [← Real.exp_nat_mul])) (norm_nonneg _) (by positivity))
  
  exact (differentiableOn_const _).add h

theorem RsechC_ofReal  (α : ℝ) :
    RsechC lam (α : ℂ) = ((Rsech lam α : ℝ) : ℂ) := by
  have h := Rsech_eq_trigSeries hlam α
  unfold trigSeries at h
  have e : ∀ n , secCoeff lam n * Real.cos ( (n + 1 : ℕ)  * α) +
      (fun _  =>  0 ) n * Real.sin ( (n + 1 : ℕ)  * α) =
      secCoeff lam n * Real.cos ( (n + 1 )  * α) := fun n => by simp
  simp_rw [e] at h
  rw [h]
  unfold RsechC
  push_cast
  rfl

/-- `α ↦ R_λ(α)` is real analytic. -/
theorem analyticAt_Rsech  (α : ℝ) : AnalyticAt ℝ (Rsech lam) α := by
  
  
  have h2 := ((differentiableOn_RsechC hlam).analyticAt (by
                                                           apply IsOpen.mem_nhds
                                                           · exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
                                                           · simp; positivity : {z : ℂ | |z.im| < lam / 2} ∈ 𝓝 (α : ℂ))).re_ofReal
  
  rwa [(by
          simp_all [RsechC_ofReal] : (fun x : ℝ => (RsechC lam (x )).re) = Rsech lam)] at h2

theorem analyticAt_Xi  (α : ℝ) : AnalyticAt ℝ (Xi lam) α := by
  
  have h2  := Real.one_lt_cosh.mpr hlam.ne'
  have := Real.cos_le_one α
  exact analyticAt_const.div (analyticAt_const.sub Real.analyticAt_cos) (by linarith)

end

/-- **Analyticity of `ρ_Δ` in `x`** (fixed `Δ < -1`). -/
theorem analyticAt_rho {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : AnalyticAt ℝ (rho Δ) x := by
  have hlam := lamOf_pos hΔ
  have hk := analyticAt_kInv hlam x
  
  
  have : rho Δ = fun y => Rsech (lamOf Δ) (kInv (lamOf Δ) y) /
      (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) y)) := funext (rho_eq hΔ)
  rw [this]
  refine ((analyticAt_Rsech hlam (kInv (lamOf Δ) x)).comp hk).div (analyticAt_const.mul ((analyticAt_Xi hlam (kInv (lamOf Δ) x)).comp hk)) ?_
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity

/-! ### Joint continuity in `(Δ, x)` -/

end PottsDiscontinuity.Bethe
