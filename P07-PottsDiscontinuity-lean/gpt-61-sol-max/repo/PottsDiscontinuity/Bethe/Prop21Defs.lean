module

public import Mathlib
public import PottsDiscontinuity.Bethe.ThetaK
public import PottsDiscontinuity.Bethe.FourierPoisson

/-!
# Proposition 2.1: the equations (cBE_Δ), (cOE_Δ) and the change of variables `x = k(α)`

Source: arXiv:1611.09877v2, §2.1 (equations (cBE_Δ), (cOE_Δ) and the proof of Proposition 2.1).

* `d1Theta`, `d2Theta`: the partial derivatives `∂₁Θ`, `∂₂Θ` of `theta`;
* `cBEop`, `IsCBESolution`: the equation (cBE_Δ); `cOEop`, `IsCOESolution`: the equation (cOE_Δ);
* `kInv`: explicit inverse of `kMap` (`kMap_kInv`, `kInv_kMap`);
* `Rtrans`, `Ttrans`, `PsiFn`: `R = 2π ρ(k) k'`, `T = 2π τ(k)`, `Ψ = (Θ(k·,-π) + Θ(k·,π))/2`;
* `isCBESolution_iff`, `isCOESolution_iff`: the change of variables turns (cBE), (cOE) into
  (cBE'): `R + (1/2π) Ξ_{2λ} * R = Ξ_λ` and (cOE'): `T + (1/2π) Ξ_{2λ} * T = Ψ` on `[-π, π]`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The inverse `x ↦ α` of `kMap lam` (explicit closed form):
`k_λ^{-1}(x) = x - 2 arctan (sin x / (e^λ + cos x))`. -/
noncomputable def kInv (lam x : ℝ) : ℝ :=
  x - 2 * Real.arctan (Real.sin x / (Real.exp lam + Real.cos x))

section

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

theorem exp_add_cos_pos  (x : ℝ) : 0 < Real.exp lam + Real.cos x := by
  have := Real.add_one_lt_exp hlam.ne'
  have := Real.neg_one_le_cos x
  linarith

theorem continuous_kInv  : Continuous (kInv lam) := by
  
  refine continuous_id.sub (continuous_const.mul (Real.continuous_arctan.comp ?_))
  exact Real.continuous_sin.div (continuous_const.add Real.continuous_cos)
     fun x => (exp_add_cos_pos hlam x).ne' 

theorem analyticAt_kInv  (x : ℝ) : AnalyticAt ℝ (kInv lam) x := analyticAt_id.sub (analyticAt_const.mul ((analyticAt_real_arctan _).comp (Real.analyticAt_sin.div (analyticAt_const.add Real.analyticAt_cos) (exp_add_cos_pos hlam x).ne')))

theorem exp_I_mul_kInv  (x : ℝ) :
    Complex.exp (I * (kInv lam x : ℂ)) =
      (Complex.exp (I * x) * (Real.exp lam : ℂ) + 1) / ((Real.exp lam : ℂ) + Complex.exp (I * x)) := by
  
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sin x / (Real.exp lam + Real.cos x) := ⟨_, rfl⟩
  have hk : kInv lam x = x - 2 * Real.arctan t := by rw [ht]; rfl
  have ha' :   Real.exp lam  + (Real.cos x : ℂ)  ≠ 0 := by exact_mod_cast (exp_add_cos_pos hlam x).ne'
  
  have hts :  t  * ( Real.exp lam  +  Real.cos x ) = (Real.sin x : ℂ) := by
    simp_all
  
  have hub  :=
    exp_neg_I_mul_ofReal x
  have h1 : Complex.exp (I *  kInv lam x ) = Complex.exp (I * x) *
      (Complex.exp ( (2 * Real.arctan t : ℝ)  * I))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add, hk]
    
    push_cast
    ring
  rw [h1, exp_two_arctan_mul_I]
  have hE1 :  Real.exp lam  + Complex.exp (I * x) =
      ( Real.exp lam  +  Real.cos x ) * (1 +  t  * I) := by
    rw [ exp_I_mul_ofReal x ]; linear_combination  -I  * hts
  
  have huu : Complex.exp (I * x) * Complex.exp (-(I * x)) = 1 := by
    rw [← Complex.exp_add]; simp
  grind

theorem kMap_kInv  (x : ℝ) : kMap lam (kInv lam x) = x := by
  have key : (fun x => kMap lam (kInv lam x)) = fun x => x := by
    refine eq_of_exp_eq (X := ℝ) ?_ continuous_id ?_ 0 ?_
    · exact (continuous_kMap hlam).comp (continuous_kInv hlam)
    · intro x
      have hE :  1  < Real.exp lam := by simpa using hlam
      
      
      have hE2 : (Real.exp lam : ℂ) ^ 2 - 1 ≠ 0 := by
        have :  Real.exp lam  ^ 2 - 1 = ( (Real.exp lam ^ 2 - 1 : ℝ)  : ℂ) := by push_cast; ring
        rw [this]
        exact Complex.ofReal_ne_zero.mpr (by nlinarith)
      have hne3 :  Real.exp lam  + Complex.exp (I * x) ≠ 0 := by
        intro h
        have :  Real.exp lam  = -Complex.exp (I * x) := by linear_combination h
        have h2 : ‖(Real.exp lam : ℂ)‖ = ‖Complex.exp (I *  x )‖ := by
          rw [this, norm_neg]
        rw [ norm_exp_I_mul' x , Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
        linarith
      
      rw [mul_comm, exp_I_mul_kMap_unit hlam, exp_I_mul_kInv hlam x]
      grind
    · simp [kInv, kMap]
  exact congrFun key x

theorem kInv_kMap  (α : ℝ) : kInv lam (kMap lam α) = α :=
  by
    solve_by_elim [_root_.StrictMono.injective, _root_.PottsDiscontinuity.Bethe.strictMono_kMap, _root_.PottsDiscontinuity.Bethe.kMap_kInv]

theorem kInv_mem_Icc  {x : ℝ} (hx : x ∈ Icc (-π) π) :
    kInv lam x ∈ Icc (-π) π := by
  have hm := strictMono_kMap hlam
  have h := kMap_kInv hlam x
  constructor
  · by_contra hlt
    have := hm (not_le.mp hlt)
    rw [kMap_neg_pi] at this
    linarith [hx.1]
  · by_contra hlt
    have := hm (not_le.mp hlt)
    rw [kMap_pi] at this
    linarith [hx.2]

theorem kMap_mem_Icc  {α : ℝ} (hα : α ∈ Icc (-π) π) :
    kMap lam α ∈ Icc (-π) π := mapsTo_kMap hlam hα

end

/-! ### The operators of (cBE) and (cOE) -/

/-- `∂₁Θ_Δ(x, y)`, the partial derivative of the Bethe phase in its first variable. -/
noncomputable def d1Theta (Δ x y : ℝ)  := deriv (fun s => theta Δ s y) x

/-- `∂₂Θ_Δ(x, y)`, the partial derivative of the Bethe phase in its second variable. -/
noncomputable def d2Theta (Δ x y : ℝ)  := deriv  (theta Δ x)  y

/-- The right-hand side of (cBE_Δ): `1 + ∫_{-π}^{π} ∂₁Θ(x,y) ρ(y) dy`. -/
noncomputable def cBEop (Δ : ℝ) (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + ∫ y in (-π)..π, d1Theta Δ x y * ρ y

/-- `ρ` solves (cBE_Δ): `2π ρ(x) = 1 + ∫_{-π}^{π} ∂₁Θ(x,y) ρ(y) dy` for all `x ∈ [-π, π]`. -/
def IsCBESolution (Δ : ℝ) (ρ : ℝ → ℝ)  :=
  ∀ x ∈ Icc (-π) π, 2 * π * ρ x = cBEop Δ ρ x

/-- The right-hand side of (cOE_Δ):
`(Θ(x,-π) + Θ(x,π))/2 - ∫_{-π}^{π} ∂₂Θ(x,y) τ(y) dy`. -/
noncomputable def cOEop (Δ : ℝ) (τ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (theta Δ x (-π) + theta Δ x π) / 2 - ∫ y in (-π)..π, d2Theta Δ x y * τ y

/-- `τ` solves (cOE_Δ): `2π τ(x) = (Θ(x,-π)+Θ(x,π))/2 - ∫_{-π}^{π} ∂₂Θ(x,y) τ(y) dy` for all
`x ∈ [-π, π]`. -/
def IsCOESolution (Δ : ℝ) (τ : ℝ → ℝ)  :=
  ∀ x ∈ Icc (-π) π, 2 * π * τ x = cOEop Δ τ x

/-! ### The change of variables `x = k(α)` -/

/-- `R(α) = 2π ρ(k(α)) k'(α)`. -/
noncomputable def Rtrans (Δ : ℝ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * π * ρ (kMap (lamOf Δ) α) * deriv (kMap (lamOf Δ)) α

/-- `T(α) = 2π τ(k(α))`. -/
noncomputable def Ttrans (Δ : ℝ) (τ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * π * τ (kMap (lamOf Δ) α)

/-- `Ψ(α) = (Θ(k(α),-π) + Θ(k(α),π))/2`. -/
noncomputable def PsiFn (Δ α : ℝ) : ℝ :=
  (theta Δ (kMap (lamOf Δ) α) (-π) + theta Δ (kMap (lamOf Δ) α) π) / 2

theorem Rtrans_eq {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    Rtrans Δ ρ α = 2 * π * ρ (kMap (lamOf Δ) α) * Xi (lamOf Δ) α := by
  rw [Rtrans, deriv_kMap (lamOf_pos hΔ)]

theorem integral_Icc_comp_kMap {lam : ℝ} (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ y in (-π)..π, g y = ∫ β in (-π)..π, Xi lam β * g (kMap lam β) := by
  have hpi := Real.pi_pos
  
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn g
  rw [ (bijOn_kMap hlam).image_eq ] at hcov
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, hcov]
  refine setIntegral_congr_fun measurableSet_Icc fun β _ => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]

section

variable {Δ : ℝ}
include Δ

section

variable (hΔ : Δ < -1)
include hΔ

/-- Change of variables `x = k(α)` in (cBE): for every function `ρ` and every `α`,
`cBEop ρ (k α) = 1 - (1/(2π Ξ_λ(α))) ∫_{-π}^{π} Ξ_{2λ}(α-β) (2π ρ(k β) Ξ_λ(β)) dβ`. -/
theorem cBEop_kMap   (ρ : ℝ → ℝ) (α : ℝ) :
    cBEop Δ ρ (kMap (lamOf Δ) α) =
      1 - (2 * π * Xi (lamOf Δ) α)⁻¹ *
        ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β) := by
  have hlam := lamOf_pos hΔ
  
  
  
  unfold cBEop
  rw [integral_Icc_comp_kMap hlam]
  
  simp_rw [(by
              intro β
              rw [d1Theta, deriv_theta_left_kMap hlam (cosh_lamOf hΔ) α β]
              field_simp : ∀ β , Xi (lamOf Δ) β * (d1Theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) * ρ (kMap (lamOf Δ) β)) =
      -((2 * π * Xi (lamOf Δ) α)⁻¹ *
        (Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β))))]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring

/-- Change of variables `x = k(α)` in (cOE): for every function `τ` and every `α`,
`cOEop τ (k α) = Ψ(α) - ∫_{-π}^{π} Ξ_{2λ}(α-β) τ(k β) dβ`. -/
theorem cOEop_kMap   (τ : ℝ → ℝ) (α : ℝ) :
    cOEop Δ τ (kMap (lamOf Δ) α) =
      PsiFn Δ α - ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
  have hlam := lamOf_pos hΔ
  
  
  unfold cOEop PsiFn
  rw [integral_Icc_comp_kMap hlam]
  
  simp_rw [(by
              intro β
              have hXb := Xi_pos hlam β
              rw [d2Theta, deriv_theta_right_kMap hlam (cosh_lamOf hΔ) α β]
              field_simp : ∀ β , Xi (lamOf Δ) β * (d2Theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) * τ (kMap (lamOf Δ) β)) =
      Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β))]

theorem xiConv_Rtrans   (ρ : ℝ → ℝ) (α : ℝ) :
    xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α =
      (2 * π)⁻¹ * ∫ β in (-π)..π,
        Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β) := by
  grind [xiConv, Rtrans_eq]

end

theorem xiConv_Ttrans  (τ : ℝ → ℝ) (α : ℝ) :
    xiConv (2 * lamOf Δ) (Ttrans Δ τ) α =
      ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
  
  unfold xiConv Ttrans
  
  simp_rw [(fun β => by ring : ∀ β , Xi (2 * lamOf Δ) (α - β) * (2 * π * τ (kMap (lamOf Δ) β)) =
       2 * π  * (Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β)))]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

section

variable (hΔ : Δ < -1)
include hΔ

/-- Pointwise form of the change of variables for (cBE): the equation at `x = k(α)` is
equivalent to (cBE') at `α`. -/
theorem cBE_at_iff   (ρ : ℝ → ℝ) (α : ℝ) :
     2 * π * ρ (kMap (lamOf Δ) α) = cBEop Δ ρ (kMap (lamOf Δ) α)  ↔
      Rtrans Δ ρ α + xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α = Xi (lamOf Δ) α := by
  
  
  have hXa := Xi_pos (lamOf_pos hΔ) α
  rw [cBEop_kMap hΔ, Rtrans_eq hΔ, xiConv_Rtrans hΔ]
  grind

/-- Pointwise form of the change of variables for (cOE). -/
theorem cOE_at_iff   (τ : ℝ → ℝ) (α : ℝ) :
     2 * π * τ (kMap (lamOf Δ) α) = cOEop Δ τ (kMap (lamOf Δ) α)  ↔
      Ttrans Δ τ α + xiConv (2 * lamOf Δ) (Ttrans Δ τ) α = PsiFn Δ α := by
  grind [Ttrans, cOEop_kMap, xiConv_Ttrans]

/-- (cBE) is equivalent to (cBE') for `R = 2π ρ(k·) k'`: for `x = k(α)`,
`R + (1/2π) Ξ_{2λ} * R = Ξ_λ`. -/
theorem isCBESolution_iff   (ρ : ℝ → ℝ) :
    IsCBESolution Δ ρ ↔ ∀ α ∈ Icc (-π) π,
      Rtrans Δ ρ α + xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α = Xi (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  constructor
  · intro h α hα
    exact (cBE_at_iff hΔ ρ α).1 (h _ (kMap_mem_Icc hlam hα))
  · intro h x hx
    
    have := (cBE_at_iff hΔ ρ (kInv (lamOf Δ) x)).2 (h _ (kInv_mem_Icc hlam hx))
    rwa [kMap_kInv hlam] at this

/-- (cOE) is equivalent to (cOE') for `T = 2π τ(k·)`: `T + (1/2π) Ξ_{2λ} * T = Ψ`. -/
theorem isCOESolution_iff   (τ : ℝ → ℝ) :
    IsCOESolution Δ τ ↔ ∀ α ∈ Icc (-π) π,
      Ttrans Δ τ α + xiConv (2 * lamOf Δ) (Ttrans Δ τ) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  constructor
  · intro h α hα
    exact (cOE_at_iff hΔ τ α).1 (h _ (kMap_mem_Icc hlam hα))
  · intro h x hx
    
    have := (cOE_at_iff hΔ τ (kInv (lamOf Δ) x)).2 (h _ (kInv_mem_Icc hlam hx))
    rwa [kMap_kInv hlam] at this

end

end

end PottsDiscontinuity.Bethe
