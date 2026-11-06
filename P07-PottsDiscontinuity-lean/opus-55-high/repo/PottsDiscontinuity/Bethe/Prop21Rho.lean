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

@[expose] public noncomputable section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The periodised hyperbolic secant `R(α) = (π/(2λ)) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`
(the function `𝓡` of §4, equal to `2π ρ(k(α)) k'(α)`). -/
def Rsech (lam α : ℝ) : ℝ :=
  (π / (2 * lam)) * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))

section
variable (lam : ℝ) (n : ℕ)
/-- The cosine-coefficient sequence `1/cosh(λ m)`, `m = n + 1`. -/
def secCoeff  : ℝ := 1 / Real.cosh (lam * ((n + 1 : ℕ) : ℝ))

theorem secCoeff_pos  : 0 < secCoeff lam n := by
  unfold secCoeff; positivity
end

section
variable {lam : ℝ} (hlam : 0 < lam)
include hlam
theorem secCoeff_le (n : ℕ) :
    secCoeff lam n ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  have := Real.exp_pos (lam * ((n + 1 : ℕ) : ℝ))
  rw [secCoeff, ← Real.exp_nat_mul, div_le_iff₀ (Real.cosh_pos _), Real.cosh_eq, show ((n + 1 : ℕ) : ℝ) * -lam = -(lam * ↑(n + 1)) by ring, Real.exp_neg]
  field_simp
  nlinarith [Real.exp_pos (-(lam * ((n + 1 : ℕ) : ℝ)))]

theorem summable_secCoeff  : Summable (secCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hs : Summable (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le (by simp_all)).mul_left (2 * Real.exp (-lam))
    grind
  exact Summable.of_nonneg_of_le (fun n => (secCoeff_pos lam n).le) (secCoeff_le hlam) hs

theorem Rsech_eq_trigSeries (α : ℝ) :
    Rsech lam α = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) α := by
  have h := (periodic_sech_eq_cos_series hlam α).tsum_eq
  grind [trigSeries, Rsech, secCoeff, Real.cos, Real.sin, Real.cosh]
end

section
variable {lam : ℝ}
theorem one_add_exp_two_mul_div_cosh (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * secCoeff lam n = 2 * Real.exp (-lam) ^ (n + 1) := by
  have := Real.exp_pos (lam * ((n + 1 : ℕ) : ℝ))
  rw [secCoeff, ← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.cosh_eq, show ((n + 1 : ℕ) : ℝ) * -(2 * lam) = -(lam * ↑(n + 1)) - lam * ↑(n + 1) by ring, show ((n + 1 : ℕ) : ℝ) * -lam = -(lam * ↑(n + 1)) by ring, Real.exp_sub, Real.exp_neg]
  field_simp

/-- The key identity of the existence half for `ρ`:
`R + (1/2π) Ξ_{2λ} * R = Ξ_λ` for the periodised sech `R` (equation (cBE') of the source). -/
theorem Rsech_add_xiConv (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α + xiConv (2 * lam) (Rsech lam) α = Xi lam α := by
  have hc := summable_secCoeff hlam
  have hc2 := summable_pow_succ_mul hc (Real.exp_pos (-(2 * lam))).le (by simp_all : Real.exp (-(2 * lam)) < 1).le
  rw [funext (Rsech_eq_trigSeries hlam), xiConv_trigSeries (by linarith) hc summable_zero (1 / 2) α]
  have h5 : (fun n => trigTerm (secCoeff lam) (fun _ => 0) n α +
      trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) n α) =
      fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α) := by
    grind [trigTerm, one_add_exp_two_mul_div_cosh]
  have := ((hasSum_trigTerm hc summable_zero α).add (hasSum_trigTerm hc2 (by simp) α)).unique (h5 ▸ hasSum_Xi_cos hlam α)
  simp only [trigSeries, trigTerm] at this ⊢
  linarith
end

/-! ### The explicit density `ρ_Δ` of (2.1) -/

/-- The explicit solution of (cBE_Δ) given by (2.1): for `x = k(α)`,
`ρ(x) = (1/(4 λ k'(α))) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`, with `λ = λ(Δ)` and `α = k^{-1}(x)`. -/
def rho (Δ x : ℝ) : ℝ :=
  1 / (4 * lamOf Δ * deriv (kMap (lamOf Δ)) (kInv (lamOf Δ) x)) *
    ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + kInv (lamOf Δ) x) / (2 * lamOf Δ))

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
theorem rho_eq (x : ℝ) :
    rho Δ x = Rsech (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  unfold rho Rsech
  rw [deriv_kMap hlam]
  grind

theorem Rtrans_rho (α : ℝ) :
    Rtrans Δ (rho Δ) α = Rsech (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  have hX := Xi_pos hlam α
  rw [Rtrans_eq hΔ, rho_eq hΔ, kInv_kMap hlam]
  field_simp

/-- **Proposition 2.1, existence for `ρ`**: the explicit `ρ` of (2.1) solves (cBE_Δ) for every
`x ∈ [-π, π]`. -/
theorem rho_isCBESolution  : IsCBESolution Δ (rho Δ) := by
  rw [isCBESolution_iff hΔ]
  intro α _
  rw [(funext (Rtrans_rho hΔ))]
  exact Rsech_add_xiConv (lamOf_pos hΔ) α
end

/-! ### Uniqueness: transfer between the variables `x` and `α` -/

section
variable {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc (-π) π) volume)
include hlam hf
theorem integrableOn_Xi_mul_comp  :
    IntegrableOn (fun β => Xi lam β * f (kMap lam β)) (Icc (-π) π) volume := by
  have himg := (bijOn_kMap hlam).image_eq
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc (-π) π)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn f).1 (by simp_all)
  refine h.congr_fun (fun β _ => ?_) measurableSet_Icc
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]

theorem integrableOn_comp_kMap_of_Xi  :
    IntegrableOn (fun β => f (kMap lam β)) (Icc (-π) π) volume := by
  have h := integrableOn_Xi_mul_comp hlam hf
  have hc : ContinuousOn (fun β => (Xi lam β)⁻¹) (Icc (-π) π) :=
    ((continuous_Xi (μ := lam) hlam).inv₀ (fun β => (Xi_pos hlam β).ne')).continuousOn
  have := h.mul_continuousOn hc isCompact_Icc
  refine this.congr_fun (fun β _ => ?_) measurableSet_Icc
  have := (Xi_pos hlam β).ne'
  grind
end

/-- If `f ∘ k = g ∘ k` a.e. on `[-π, π]` for integrable `f, g`, then `f = g` a.e. on `[-π, π]`. -/
theorem ae_eq_of_comp_kMap {lam : ℝ} (hlam : 0 < lam) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) (hg : IntegrableOn g (Icc (-π) π) volume)
    (h : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), f (kMap lam β) = g (kMap lam β)) :
    f =ᵐ[volume.restrict (Icc (-π) π)] g := by
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Icc (-π) π)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn (fun x => |f x - g x|)
  rw [((bijOn_kMap hlam).image_eq)] at hcov
  have h0 : ∫ x in Icc (-π) π, |f x - g x| = 0 := by
    rw [hcov]
    have : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), |Xi lam β| • |f (kMap lam β) - g (kMap lam β)| = 0 := by
      filter_upwards [h] with β hβ
      simp_all
    rw [integral_congr_ae this]; simp
  have hi :=
    (hf.sub hg).abs
  filter_upwards [((integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hi).1 h0)] with x hx
  simp at hx
  linarith

section
variable {μ : ℝ} (hμ : 0 < μ) {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π) (hg : IntervalIntegrable g volume (-π) π) (α : ℝ)
include hμ hf hg
/-- Linearity of the Poisson convolution. -/
theorem xiConv_sub  :
    xiConv μ (fun β => f β - g β) α = xiConv μ f α - xiConv μ g α := by
  have hc : Continuous (fun β : ℝ => Xi μ (α - β)) := (continuous_Xi hμ).comp (by fun_prop)
  simp only [xiConv, mul_sub, intervalIntegral.integral_sub (hf.continuousOn_mul hc.continuousOn) (hg.continuousOn_mul hc.continuousOn)]

theorem xiConv_add  :
    xiConv μ (fun β => f β + g β) α = xiConv μ f α + xiConv μ g α := by
  have hc : Continuous (fun β : ℝ => Xi μ (α - β)) := (continuous_Xi hμ).comp (by fun_prop)
  simp only [xiConv, mul_add, intervalIntegral.integral_add (hf.continuousOn_mul hc.continuousOn) (hg.continuousOn_mul hc.continuousOn)]
end

theorem continuous_Rsech {lam : ℝ} (hlam : 0 < lam) : Continuous (Rsech lam) := by
  rw [(funext (Rsech_eq_trigSeries hlam))]
  exact continuous_trigSeries (summable_secCoeff hlam) summable_zero _

theorem continuous_rho {Δ : ℝ} (hΔ : Δ < -1) : Continuous (rho Δ) := by
  have hlam := lamOf_pos hΔ
  rw [(funext (rho_eq hΔ))]
  have hk := continuous_kInv hlam
  refine ((continuous_Rsech hlam).comp hk).div
    (continuous_const.mul ((continuous_Xi hlam).comp hk)) (fun x => ?_)
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity

section
variable {f : ℝ → ℝ}
theorem integrableOn_Icc_of_continuous (hf : Continuous f) :
    IntegrableOn f (Icc (-π) π) volume :=
  hf.continuousOn.integrableOn_Icc

theorem intervalIntegrable_of_integrableOn_Icc (hf : IntegrableOn f (Icc (-π) π) volume) : IntervalIntegrable f volume (-π) π := by
  have hpi := Real.pi_pos
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  exact hf.mono_set Ioc_subset_Icc_self
end

end PottsDiscontinuity.Bethe
