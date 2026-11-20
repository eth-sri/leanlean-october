module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Defs
public import PottsDiscontinuity.Bethe.FourierTrig
public import PottsDiscontinuity.Bethe.FourierSech

/-!
# Proposition 2.1 for `ρ`: the explicit solution of (cBE_Δ) and its uniqueness

Source: arXiv:1611.09877v2, Proposition 2.1 and its proof (§2.1), with the Fourier computations of
§4 (`R̂(m) = 1/(2 cosh(λ m))`).

* `Rsech lam α = (π/(2λ)) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))` is `R = 2πρ(k)k'`;
* `rho Δ x`: the explicit density of (2.1) (`x = k(α)`, `α = kInv x`);
* `Rsech_add_xiConv`: `R + (1/2π) Ξ_{2λ} * R = Ξ_λ` (existence half: the hyperbolic-secant
  transform / Poisson summation gives the cosine series of `R` with coefficients `1/cosh(λ m)`);
* `rho_isCBESolution`: `ρ` solves (cBE_Δ) at every `x ∈ [-π, π]`;
* `eq_rho_of_isCBESolution_of_integrableOn`, `eq_rho_of_isCBESolution`: every integrable
  (in particular every `L²`) solution of (cBE_Δ) equals `ρ` on `[-π, π]` (uniqueness half: the
  positive definiteness of the Poisson kernel replaces the division by `1 + Ξ̂_{2λ}(m)`).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The periodised hyperbolic secant `R(α) = (π/(2λ)) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`
(the function `𝓡` of §4, equal to `2π ρ(k(α)) k'(α)`). -/
noncomputable def Rsech (lam α : ℝ) : ℝ :=
  (π / (2 * lam)) * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))

/-- The cosine-coefficient sequence `1/cosh(λ m)`, `m = n + 1`. -/
noncomputable def secCoeff (lam : ℝ) (n : ℕ) : ℝ := 1 / Real.cosh (lam * ((n + 1 : ℕ) : ℝ))

theorem secCoeff_pos (lam : ℝ) (n : ℕ) : 0 < secCoeff lam n := by
  unfold secCoeff; positivity

theorem one_add_exp_two_mul_div_cosh {lam : ℝ} (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * secCoeff lam n = 2 * Real.exp (-lam) ^ (n + 1) := by
  unfold secCoeff
  set q : ℝ := Real.exp (-lam) ^ (n + 1) with hq
  have hq0 : 0 < q := by positivity
  have h1 : Real.exp (-(2 * lam)) ^ (n + 1) = q ^ 2 := by
    have e : Real.exp (-(2 * lam)) = Real.exp (-lam) ^ 2 := by
      rw [← Real.exp_nat_mul]; simp
    simp [hq, e, ← pow_mul, mul_comm 2 (n + 1)]
  have h2 : Real.exp (-(lam * ((n + 1 : ℕ) : ℝ))) = q := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) = (q⁻¹ + q) / 2 := by
    have e : Real.exp (lam * ((n + 1 : ℕ) : ℝ)) = q⁻¹ := by
      simp [← h2, Real.exp_neg]
    rw [Real.cosh_eq, h2, e]
  rw [h1, h3]
  field_simp

theorem secCoeff_le {lam : ℝ} (_hlam : 0 < lam) (n : ℕ) :
    secCoeff lam n ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  rw [← one_add_exp_two_mul_div_cosh, add_mul, one_mul, le_add_iff_nonneg_right]
  exact mul_nonneg (by positivity) (secCoeff_pos lam n).le

theorem summable_secCoeff {lam : ℝ} (hlam : 0 < lam) : Summable (secCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by simp_all
  have hs : Summable (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
    grind
  exact Summable.of_nonneg_of_le (fun n => (secCoeff_pos lam n).le) (secCoeff_le hlam) hs

theorem Rsech_eq_trigSeries {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) α := by
  have h := (periodic_sech_eq_cos_series hlam α).tsum_eq
  unfold trigSeries Rsech
  grind only [secCoeff]

/-- The explicit density solves the Poisson convolution equation. -/
theorem Rsech_add_xiConv {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α + xiConv (2 * lam) (Rsech lam) α = Xi lam α := by
  rw [funext (Rsech_eq_trigSeries hlam),
    trigSeries_add_xiConv (by positivity) (summable_secCoeff hlam) summable_zero, trigSeries]
  simp only [one_add_exp_two_mul_div_cosh, mul_zero, zero_mul, add_zero]
  linarith [(hasSum_Xi_cos hlam α).tsum_eq]

/-! ### The explicit density `ρ_Δ` of (2.1) -/

/-- The explicit solution of (cBE_Δ) given by (2.1): for `x = k(α)`,
`ρ(x) = (1/(4 λ k'(α))) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`, with `λ = λ(Δ)` and `α = k^{-1}(x)`. -/
noncomputable def rho (Δ x : ℝ) : ℝ :=
  1 / (4 * lamOf Δ * deriv (kMap (lamOf Δ)) (kInv (lamOf Δ) x)) *
    ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + kInv (lamOf Δ) x) / (2 * lamOf Δ))

theorem rho_eq {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) :
    rho Δ x = Rsech (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  unfold rho Rsech
  rw [deriv_kMap hlam]
  grind

theorem Rtrans_rho {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ) :
    Rtrans Δ (rho Δ) α = Rsech (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  have hX := Xi_pos hlam α
  rw [Rtrans_eq hΔ, rho_eq hΔ, kInv_kMap hlam]
  field_simp

/-- **Proposition 2.1, existence for `ρ`**: the explicit `ρ` of (2.1) solves (cBE_Δ) for every
`x ∈ [-π, π]`. -/
theorem rho_isCBESolution {Δ : ℝ} (hΔ : Δ < -1) : IsCBESolution Δ (rho Δ) := by
  rw [isCBESolution_iff hΔ]
  intro α _
  have hR := funext (Rtrans_rho hΔ)
  rw [hR]
  exact Rsech_add_xiConv (lamOf_pos hΔ) α

/-! ### Uniqueness: transfer between the variables `x` and `α` -/

theorem integrableOn_Xi_mul_comp {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) :
    IntegrableOn (fun β => Xi lam β * f (kMap lam β)) (Icc (-π) π) volume := by
  have himg : kMap lam '' Icc (-π) π = Icc (-π) π := (bijOn_kMap hlam).image_eq
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn f).1 (by simp_all)
  refine h.congr_fun (fun β _ => ?_) measurableSet_Icc
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]

theorem xiConv_add {μ : ℝ} (hμ : 0 < μ) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (-π) π) (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    xiConv μ (fun β => f β + g β) α = xiConv μ f α + xiConv μ g α := by
  simp only [xiConv, mul_add, intervalIntegral.integral_add (intervalIntegrable_Xi_mul hμ hf α)
    (intervalIntegrable_Xi_mul hμ hg α)]

theorem continuous_Rsech {lam : ℝ} (hlam : 0 < lam) : Continuous (Rsech lam) := by
  have : Rsech lam = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) :=
    funext (Rsech_eq_trigSeries hlam)
  rw [this]
  exact continuous_trigSeries (summable_secCoeff hlam) summable_zero _

theorem continuous_rho {Δ : ℝ} (hΔ : Δ < -1) : Continuous (rho Δ) := by
  have hlam := lamOf_pos hΔ
  have : rho Δ = fun x => Rsech (lamOf Δ) (kInv (lamOf Δ) x) /
      (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := funext (rho_eq hΔ)
  rw [this]
  have hk := continuous_kInv hlam
  refine ((continuous_Rsech hlam).comp hk).div
    (continuous_const.mul ((continuous_Xi hlam).comp hk)) (fun x => ?_)
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity

end PottsDiscontinuity.Bethe
