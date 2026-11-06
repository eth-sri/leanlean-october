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
   π / (2 * lam)  * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))

/-- The cosine-coefficient sequence `1/cosh(λ m)`, `m = n + 1`. -/
noncomputable def secCoeff (lam : ℝ) (n : ℕ) : ℝ := 1 / Real.cosh (lam * ((n + 1 : ℕ) : ℝ))

theorem secCoeff_pos (lam : ℝ) (n : ℕ) : 0 < secCoeff lam n := by
  unfold secCoeff; positivity

section

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

theorem secCoeff_le  (n : ℕ) :
    secCoeff lam n ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  unfold secCoeff
  
  have h1 : Real.exp (lam *  (n + 1 : ℕ) ) ≤ 2 * Real.cosh (lam *  (n + 1 : ℕ) ) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(lam *  (n + 1 : ℕ) ))
    linarith
  
  rw [(by
         rw [← Real.exp_nat_mul]
         grind : Real.exp (-lam) ^ (n + 1) = Real.exp (-(lam * ((n + 1 : ℕ) )))), one_div, Real.exp_neg]
  
  
  rw [inv_eq_one_div, div_le_iff₀ (Real.cosh_pos _)]
  rw [show 2 * (Real.exp (lam *  (n + 1 : ℕ) ))⁻¹ * Real.cosh (lam *  (n + 1 : ℕ) ) =
    2 * Real.cosh (lam *  (n + 1 : ℕ) ) / Real.exp (lam *  (n + 1 : ℕ) ) by ring]
  rw [le_div_iff₀ (Real.exp_pos _)]
  linarith

theorem summable_secCoeff  : Summable (secCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  
  exact Summable.of_nonneg_of_le (fun n => (secCoeff_pos lam n).le) (secCoeff_le hlam) (by
                                                                                          have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
                                                                                          grind)

theorem Rsech_eq_trigSeries  (α : ℝ) :
    Rsech lam α = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) α := by
  have h := (periodic_sech_eq_cos_series hlam α).tsum_eq
  unfold trigSeries Rsech
  have : ∀ n , secCoeff lam n * Real.cos ( (n + 1 : ℕ)  * α) + 0 * Real.sin ( (n + 1 : ℕ)  * α) =
      Real.cos ( (n + 1 : ℕ)  * α) / Real.cosh (lam *  (n + 1 : ℕ) ) := by
    intro n; unfold secCoeff; ring
  simp_rw [this]
  linarith

end

theorem one_add_exp_two_mul_div_cosh {lam : ℝ} (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * secCoeff lam n = 2 * Real.exp (-lam) ^ (n + 1) := by
  unfold secCoeff
  set q : ℝ := Real.exp (-lam) ^ (n + 1) with hq
  
  have h1 : Real.exp (-(2 * lam)) ^ (n + 1) = q ^ 2 := by
    have e : Real.exp (-(2 * lam)) = Real.exp (-lam) ^ 2 := by
      rw [← Real.exp_nat_mul]
      simp_all
    rw [e, ← pow_mul, mul_comm 2 (n + 1), pow_mul]
  have h2 : Real.exp (-(lam *  (n + 1 : ℕ) )) = q := by
    rw [hq, ← Real.exp_nat_mul]
    grind
  have h3 : Real.cosh (lam *  (n + 1 : ℕ) ) = (q⁻¹ + q) / 2 := by
    have e : Real.exp (lam *  (n + 1 : ℕ) ) = q⁻¹ := by
      rw [← h2, Real.exp_neg, inv_inv]
    rw [Real.cosh_eq, h2, e]
  rw [h1, h3]
  field_simp

/-- The key identity of the existence half for `ρ`:
`R + (1/2π) Ξ_{2λ} * R = Ξ_λ` for the periodised sech `R` (equation (cBE') of the source). -/
theorem Rsech_add_xiConv {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α + xiConv (2 * lam) (Rsech lam) α = Xi lam α := by
  
  
  
  have hc := summable_secCoeff hlam
  
  
  
  
  
   
  have h2 :=  hasSum_trigTerm (summable_pow_succ_mul hc (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; linarith : Real.exp (-(2 * lam)) < 1).le) (by simp : Summable  fun n  => Real.exp (-(2 * lam)) ^ (n + 1) * 0) α 
  have h3 := (hasSum_trigTerm hc  summable_zero  α).add h2
  
  have e1 : Rsech lam α = 1 / 2 + ∑' n, trigTerm (secCoeff lam) (fun _ => 0) n α := by
    rw [Rsech_eq_trigSeries hlam]; rfl
  have e2 : xiConv (2 * lam) (Rsech lam) α = 1 / 2 +
      ∑' n, trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) n α := by
    rw [(by
           rw [ funext (Rsech_eq_trigSeries hlam) ]; exact xiConv_trigSeries (by linarith) hc  summable_zero  (1 / 2) α : xiConv (2 * lam) (Rsech lam) α =
      trigSeries (1 / 2) (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) α)]; rfl
  
  rw [(by
         grind [trigTerm, one_add_exp_two_mul_div_cosh] : (fun n => trigTerm (secCoeff lam) (fun _ => 0) n α +
      trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) n α) =
      fun n  => 2 * Real.exp (-lam) ^ (n + 1) * Real.cos (((n + 1 : ℕ) ) * α))] at h3
  have h6 := h3.unique (hasSum_Xi_cos hlam α)
  
  linarith

/-! ### The explicit density `ρ_Δ` of (2.1) -/

/-- The explicit solution of (cBE_Δ) given by (2.1): for `x = k(α)`,
`ρ(x) = (1/(4 λ k'(α))) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`, with `λ = λ(Δ)` and `α = k^{-1}(x)`. -/
noncomputable def rho (Δ x : ℝ) : ℝ :=
  1 / (4 * lamOf Δ * deriv (kMap (lamOf Δ)) (kInv (lamOf Δ) x)) *
    ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + kInv (lamOf Δ) x) / (2 * lamOf Δ))

section

variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ

theorem rho_eq  (x : ℝ) :
    rho Δ x = Rsech (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := by
  
  have hpi := Real.pi_pos
  
  unfold rho Rsech
  rw [deriv_kMap (lamOf_pos hΔ)]
  grind

theorem Rtrans_rho  (α : ℝ) :
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
  
  rw [ funext (Rtrans_rho hΔ) ]
  exact Rsech_add_xiConv (lamOf_pos hΔ) α

end

/-! ### Uniqueness: transfer between the variables `x` and `α` -/

section

variable {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc (-π) π) volume)
include hlam hf

theorem integrableOn_Xi_mul_comp  :
    IntegrableOn (fun β => Xi lam β * f (kMap lam β)) (Icc (-π) π) volume := by
  
  
  refine ((integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
            (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
            (strictMono_kMap hlam).injective.injOn f).1 (by rwa [ (bijOn_kMap hlam).image_eq ])).congr_fun (fun β _ => ?_) measurableSet_Icc
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]

theorem integrableOn_comp_kMap_of_Xi  :
    IntegrableOn (fun β => f (kMap lam β)) (Icc (-π) π) volume := by
  
  have hc : ContinuousOn (fun β => (Xi lam β)⁻¹) (Icc (-π) π) :=
    ((continuous_Xi (μ := lam) hlam).inv₀  fun β => (Xi_pos hlam β).ne' ).continuousOn
  have := (integrableOn_Xi_mul_comp hlam hf).mul_continuousOn hc isCompact_Icc
  refine this.congr_fun (fun β _ => ?_) measurableSet_Icc
  have := (Xi_pos hlam β).ne'
  
  field_simp

end

/-- If `f ∘ k = g ∘ k` a.e. on `[-π, π]` for integrable `f, g`, then `f = g` a.e. on `[-π, π]`. -/
theorem ae_eq_of_comp_kMap {lam : ℝ} (hlam : 0 < lam) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) (hg : IntegrableOn g (Icc (-π) π) volume)
    (h : ∀ᵐ β ∂ volume.restrict (Icc (-π) π) , f (kMap lam β) = g (kMap lam β)) :
    f =ᵐ[volume.restrict (Icc (-π) π)] g := by
  
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn  fun x => |f x - g x| 
  rw [ (bijOn_kMap hlam).image_eq ] at hcov
  
  have hi : Integrable (fun x => |f x - g x|) (volume.restrict (Icc (-π) π)) :=
    (hf.sub hg).abs
  have := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hi).1 (by
                                                                           rw [hcov]
                                                                           
                                                                           rw [integral_congr_ae (by
                                                                                                    filter_upwards [h] with β hβ
                                                                                                    all_goals simp_all : ∀ᵐ β ∂ volume.restrict (Icc (-π) π) , |Xi lam β| • |f (kMap lam β) - g (kMap lam β)| = 0)]; simp)
  filter_upwards [this] with x hx
  simp only [Pi.zero_apply, abs_eq_zero] at hx
  linarith

section

variable {μ : ℝ} (hμ : 0 < μ) {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π) (hg : IntervalIntegrable g volume (-π) π) (α : ℝ)
include hμ hf hg α

/-- Linearity of the Poisson convolution. -/
theorem xiConv_sub  :
    xiConv μ (fun β => f β - g β) α = xiConv μ f α - xiConv μ g α := by
  have hc : Continuous  fun β  => Xi μ (α - β)  := (continuous_Xi hμ).comp (by fun_prop)
  unfold xiConv
  
  simp_rw [(fun β => by ring : ∀ β , Xi μ (α - β) * (f β - g β) = Xi μ (α - β) * f β - Xi μ (α - β) * g β)]
  rw [intervalIntegral.integral_sub (hf.continuousOn_mul hc.continuousOn)
    (hg.continuousOn_mul hc.continuousOn)]
  ring

theorem xiConv_add  :
    xiConv μ (fun β => f β + g β) α = xiConv μ f α + xiConv μ g α := by
  have hc : Continuous  fun β  => Xi μ (α - β)  := (continuous_Xi hμ).comp (by fun_prop)
  unfold xiConv
  
  simp_rw [(fun β => by ring : ∀ β , Xi μ (α - β) * (f β + g β) = Xi μ (α - β) * f β + Xi μ (α - β) * g β)]
  rw [intervalIntegral.integral_add (hf.continuousOn_mul hc.continuousOn)
    (hg.continuousOn_mul hc.continuousOn)]
  ring

end

theorem continuous_Rsech {lam : ℝ} (hlam : 0 < lam) : Continuous (Rsech lam) := Eq.mpr (congrArg Continuous (funext (Rsech_eq_trigSeries hlam)))
                                                                                  (continuous_trigSeries (summable_secCoeff hlam) summable_zero (1 / 2))

theorem continuous_rho {Δ : ℝ} (hΔ : Δ < -1) : Continuous (rho Δ) := by
  have hlam := lamOf_pos hΔ
  have : rho Δ = fun x => Rsech (lamOf Δ) (kInv (lamOf Δ) x) /
      (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := funext (rho_eq hΔ)
  rw [this]
  have hk := continuous_kInv hlam
  refine ((continuous_Rsech hlam).comp hk).div
    (continuous_const.mul ((continuous_Xi hlam).comp hk))  fun x => ?_ 
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity

theorem integrableOn_Icc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Icc (-π) π) volume :=
  hf.continuousOn.integrableOn_Icc

theorem intervalIntegrable_of_integrableOn_Icc {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) : IntervalIntegrable f volume (-π) π := by
  have hpi := Real.pi_pos
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  exact hf.mono_set Ioc_subset_Icc_self

end PottsDiscontinuity.Bethe
