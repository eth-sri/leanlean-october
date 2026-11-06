module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierSawtooth
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1 for `τ`: the explicit solution of (cOE_Δ) and its uniqueness

Source: arXiv:1611.09877v2, Proposition 2.1 and its proof (§2.1), with the Fourier computations of
§4 (`T̂(m) = ((-1)^m/(i m)) tanh(λ|m|)`, `Ψ̂(m) = ((-1)^m/(i m))(1 - Ξ̂_{2λ}(m))`).

**End-point convention.**  The series in (2.1),
`τ(x) = ∑_{m>0} (-1)^m/(π m) tanh(λ m) sin(m α)`, is not absolutely summable and is interpreted as
the limit of its partial sums (`tauPartial`, `tauSeries`, `tau`).  For `|α| < π` the limit exists and
equals `T(α)/(2π)`, where `T = -α + U_λ` (`tendsto_tauPartial`, `tau_eq_tauCont`).  At `α = ±π` all
terms vanish, so the *literal* series is `0` there (`tau_pi`, `tau_neg_pi`), while the continuous
solution has `τ_c(±π) = ∓1/2` (`tauCont_pi`, `tauCont_neg_pi`).  Consequently the literal `τ`
solves (cOE) on `(-π, π)` (`tau_cOE_on_Ioo`) but not at the end points (`tau_not_cOE_pi`); the
continuous representative `tauCont` solves (cOE) on all of `[-π, π]` (`tauCont_isCOESolution`),
and uniqueness holds in `L²` (`eq_tauCont_of_isCOESolution_of_integrableOn`), i.e. up to a null set.

* `TcontFn_add_xiConv`: `T + (1/2π) Ξ_{2λ} * T = Ψ`, i.e. (cOE'), for `T = -α + U_λ`;
* `tauU_add_xiConv`: `U + (1/2π) Ξ_{2λ} * U = -2 sawS(2λ)`, from the Poisson action on the sine
  series and `1 - tanh x = e^{-x}/cosh x`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The partial sums `∑_{m=1}^{N} (-1)^m/(π m) tanh(λ m) sin(m α)` of the series for `τ` in (2.1)
(written with `m = n + 1`). -/
noncomputable def tauPartial (lam α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1) ^ (n + 1) / (π * ((n : ℝ) + 1)) * Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
    Real.sin (((n + 1 : ℕ) : ℝ) * α)

/-- The literal series `τ(x) = ∑_{m>0} (-1)^m/(π m) tanh(λ m) sin(m α)` of (2.1) at `α`,
as the limit of the partial sums (the series is not absolutely summable). -/
noncomputable def tauSeries (lam α : ℝ) : ℝ := limUnder atTop (tauPartial lam α)

/-- The literal `τ` of (2.1): `τ(x) = tauSeries λ (k^{-1}(x))`. -/
noncomputable def tau (Δ x : ℝ)  := tauSeries (lamOf Δ) (kInv (lamOf Δ) x)

/-- Coefficients of the smooth periodic part `U` of `T`: `u_n = 2(-1)^n (1 - tanh(λ(n+1)))/(n+1)`. -/
noncomputable def tauCoeff (lam : ℝ) (n : ℕ) : ℝ :=
  2 * (-1) ^ n * (1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ))) / ((n : ℝ) + 1)

/-- `U_λ(α) = ∑_{n≥0} u_n sin((n+1)α)`, absolutely convergent. -/
noncomputable def tauU (lam α : ℝ)  := trigSeries 0 (fun _ => 0) (tauCoeff lam) α

/-- `T(α) = 2π τ(k(α))` for the continuous representative: `T(α) = -α + U_λ(α)`. -/
noncomputable def TcontFn (lam α : ℝ)  := -α + tauU lam α

/-- The continuous representative of `τ`: `τ_c(x) = T(k^{-1}(x))/(2π)`; it equals the series
(2.1) for `|x| < π` and takes the values `∓1/2` at `x = ±π`. -/
noncomputable def tauCont (Δ x : ℝ) : ℝ :=
  TcontFn (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π)

theorem one_sub_tanh_eq (x : ℝ) : 1 - Real.tanh x = Real.exp (-x) / Real.cosh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  
  field_simp
  rw [Real.cosh_sub_sinh]

section

variable (lam : ℝ) (n : ℕ)


theorem one_sub_tanh_eq_mul_secCoeff  :
    1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) = Real.exp (-lam) ^ (n + 1) * secCoeff lam n := by
  rw [one_sub_tanh_eq]
  unfold secCoeff
  
  rw [(by
         rw [← Real.exp_nat_mul];   ring : Real.exp (-lam) ^ (n + 1) = Real.exp (-(lam * ((n + 1 : ℕ) ))))]; ring

theorem secCoeff_le_one  : secCoeff lam n ≤ 1 := by
  unfold secCoeff
  rw [div_le_one (Real.cosh_pos _)]
  exact Real.one_le_cosh _

theorem abs_tauCoeff_le  :
    |tauCoeff lam n| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  have hq : 0 < Real.exp (-lam) ^ (n + 1) := by positivity
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := secCoeff_pos lam n
  have h3 := secCoeff_le_one lam n
  
  
  unfold tauCoeff
  have hn :  0  < (n : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hn, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos  two_pos , abs_of_nonneg (by
                                                       rw [h1]; positivity)]
  rw [div_le_iff₀ hn]
  nlinarith

end

section

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

theorem summable_tauCoeff  : Summable (tauCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  
  exact Summable.of_norm_bounded (by
                                    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
                                    all_goals grind : Summable  fun n  => 2 * Real.exp (-lam) ^ (n + 1))  fun n => by simp_all [abs_tauCoeff_le] 

theorem continuous_tauU  : Continuous (tauU lam) :=
  continuous_trigSeries summable_zero (summable_tauCoeff hlam) 0

theorem continuous_TcontFn  : Continuous (TcontFn lam) :=
  continuous_neg.add (continuous_tauU hlam)

end

/-- `(1 + e^{-2λ(n+1)}) u_n = -4 (-1)^{n+1} e^{-2λ(n+1)}/(n+1)`. -/
theorem one_add_mul_tauCoeff {lam : ℝ} (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * tauCoeff lam n =
      -(2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / ((n : ℝ) + 1))) := by
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := one_add_exp_two_mul_div_cosh (lam := lam) n
  have h3 : Real.exp (-(2 * lam)) ^ (n + 1) = Real.exp (-lam) ^ (n + 1) * Real.exp (-lam) ^ (n + 1) := by
    
    rw [(by
           rw [← Real.exp_add];  ring : Real.exp (-(2 * lam)) = Real.exp (-lam) * Real.exp (-lam)), mul_pow]
  
  unfold tauCoeff
  grind

/-- `U + (1/2π) Ξ_{2λ} * U = -2 sawS(2λ)`. -/
theorem tauU_add_xiConv {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    tauU lam α + xiConv (2 * lam) (tauU lam) α = -2 * sawS (2 * lam) α := by
  have hlam2 : 0 < 2 * lam := by linarith
  
  
  have hu := summable_tauCoeff hlam
  
  have hX : xiConv (2 * lam) (tauU lam) α =
      trigSeries 0 (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) α :=
    xiConv_trigSeries hlam2  summable_zero  hu 0 α
  
  
  
  have h2 := hasSum_trigTerm (by simp : Summable  fun n  => Real.exp (-(2 * lam)) ^ (n + 1) * 0) (summable_pow_succ_mul hu (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; linarith : Real.exp (-(2 * lam)) < 1).le) α
  have h3 := (hasSum_trigTerm  summable_zero  hu α).add h2
  
  have e1 : tauU lam α = 0 + ∑' n, trigTerm (fun _ => 0) (tauCoeff lam) n α := rfl
  have e2 : xiConv (2 * lam) (tauU lam) α = 0 +
      ∑' n, trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) n α := by
    rw [hX]; rfl
  have h5 : (fun n => trigTerm (fun _ => 0) (tauCoeff lam) n α +
      trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) n α) =
      fun n  => -2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / ( n  + 1) *
        Real.sin ( (n + 1 : ℕ)  * α)) := by
    grind [trigTerm, one_add_mul_tauCoeff]
  rw [h5] at h3
  have h6 := h3.unique ((hasSum_xiConv_neg_id hlam2 α).mul_left (-2))
  rw [xiConv_neg_id hlam2] at h6
  
  linarith

section

variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ

/-- The key identity of the existence half for `τ`: `T + (1/2π) Ξ_{2λ} * T = Ψ`
(equation (cOE') of the source) for `T = -α + U_λ`. -/
theorem TcontFn_add_xiConv  (α : ℝ) :
    TcontFn (lamOf Δ) α + xiConv (2 * lamOf Δ) (TcontFn (lamOf Δ)) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  
  
  
  have hfun : TcontFn (lamOf Δ) = fun β => -β + tauU (lamOf Δ) β := rfl
  rw [hfun, xiConv_add (by linarith) (continuous_neg.intervalIntegrable _ _) ((continuous_tauU hlam).intervalIntegrable _ _), xiConv_neg_id (by linarith), PsiFn_eq_neg_sub_sawS hΔ]
  have := tauU_add_xiConv hlam α
  
  linarith

theorem Ttrans_tauCont  :
    Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := by
  
  
  funext α
  unfold Ttrans tauCont
  rw [kInv_kMap (lamOf_pos hΔ)]
  field_simp

/-- **Proposition 2.1, existence for `τ`**: the continuous representative `τ_c` of `τ` solves
(cOE_Δ) at every `x ∈ [-π, π]`, including the end points (where `τ_c(±π) = ∓1/2`). -/
theorem tauCont_isCOESolution  : IsCOESolution Δ (tauCont Δ) := by
  rw [isCOESolution_iff hΔ, Ttrans_tauCont hΔ]
  intro α _
  exact TcontFn_add_xiConv hΔ α

theorem continuous_tauCont  : Continuous (tauCont Δ) := by
  have hlam := lamOf_pos hΔ
  exact ((continuous_TcontFn hlam).comp (continuous_kInv hlam)).div_const _

/-- **Proposition 2.1, uniqueness for `τ`** (integrable version): every integrable solution of
(cOE_Δ) on `[-π, π]` coincides with `τ_c` at every point of `[-π, π]`. -/
theorem eq_tauCont_of_isCOESolution_of_integrableOn  {τ' : ℝ → ℝ}
    (hτ' : IntegrableOn τ' (Icc (-π) π) volume) (h : IsCOESolution Δ τ') :
    ∀ x ∈ Icc (-π) π, τ' x = tauCont Δ x := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi := Real.pi_pos
  have hT'eq := (isCOESolution_iff hΔ τ').1 h
  have hTeq := (isCOESolution_iff hΔ (tauCont Δ)).1 (tauCont_isCOESolution hΔ)
  have hTrho  := Ttrans_tauCont hΔ
  rw [hTrho] at hTeq
  
  have hT'ii := intervalIntegrable_of_integrableOn_Icc (by
                                                                                                                          solve_by_elim [_root_.MeasureTheory.Integrable.const_mul, _root_.PottsDiscontinuity.Bethe.integrableOn_comp_kMap_of_Xi, _root_.PottsDiscontinuity.Bethe.kInv._proof_1] : IntegrableOn (Ttrans Δ τ') (Icc (-π) π) volume)
  have hTii : IntervalIntegrable (TcontFn (lamOf Δ)) volume (-π) π :=
     (continuous_TcontFn hlam).intervalIntegrable _ _ 
  
  have hD0 := eq_zero_of_eq_neg_xiConv hlam2 (hT'ii.sub hTii) (by
                                                                 intro α hα
                                                                 
                                                                 rw [xiConv_sub hlam2 hT'ii hTii]
                                                                 grind)
  
  
  have hae2 := ae_eq_of_comp_kMap hlam hτ' (integrableOn_Icc_of_continuous (continuous_tauCont hΔ)) (by
                                                  
                                                  filter_upwards [(by
                                                                     rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
                                                                     exact hD0 : ∀ᵐ β ∂ volume.restrict (Icc (-π) π) ,
                                                      Ttrans Δ τ' β - TcontFn (lamOf Δ) β = 0)] with β hβ
                                                  
                                                  
                                                  
                                                  exact mul_left_cancel₀ (by positivity) (by
                                                                                            rw [hTrho]; linarith : Ttrans Δ τ' β = Ttrans Δ (tauCont Δ) β))
  intro x hx
  
  
  
  
  have h7 : 2 * π ≠ 0 := by positivity
  exact mul_left_cancel₀ h7 (by rw [ h x hx ,  tauCont_isCOESolution hΔ x hx , (by
                                                                                  unfold cOEop
                                                                                  congr 1
                                                                                  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
                                                                                  refine integral_congr_ae ?_
                                                                                  
                                                                                  filter_upwards [(by
                                                                                                     rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
                                                                                                     exact hae2)] with y hy
                                                                                  rw [hy] : cOEop Δ τ' x = cOEop Δ (tauCont Δ) x)])

end

/-! ### The literal series (2.1) for `τ` -/

section

variable {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π)
include hlam hα

/-- For `|α| < π` the partial sums of the series (2.1) for `τ` converge to `T(α)/(2π)`
with `T = -α + U_λ`, i.e. to the continuous representative. -/
theorem tendsto_tauPartial  :
    Tendsto (tauPartial lam α) atTop (𝓝 (TcontFn lam α / (2 * π))) := by
  
  
  
  have h2 := ((tendsto_sawtooth hα).add (((hasSum_trigTerm (a := fun _ => 0) (b := tauCoeff lam) summable_zero
                         (summable_tauCoeff hlam) α).tendsto_sum_nat).const_mul (1 / 2))).const_mul (1 / π)
  have hval : 1 / π * (-α / 2 + 1 / 2 * ∑' n, trigTerm (fun _ => 0) (tauCoeff lam) n α) =
      TcontFn lam α / (2 * π) := by
    grind [TcontFn, tauU, trigSeries, trigTerm]
  rw [hval] at h2
  refine h2.congr  fun N => ?_ 
  unfold tauPartial
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
   
  unfold tauCoeff trigTerm
  grind

theorem tauSeries_eq  :
    tauSeries lam α = TcontFn lam α / (2 * π) :=
  (tendsto_tauPartial hlam hα).limUnder_eq

end

section

variable (lam : ℝ)


theorem tauPartial_pi  (N : ℕ) : tauPartial lam π N = 0 := by
  
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Real.sin_nat_mul_pi]; simp 

theorem tauPartial_neg_pi  (N : ℕ) : tauPartial lam (-π) N = 0 := by
  
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_neg, Real.sin_neg, Real.sin_nat_mul_pi]; simp

/-- At the end points the *literal* series of (2.1) vanishes (every `sin(mπ) = 0`). -/
theorem tauSeries_pi  : tauSeries lam π = 0 := Eq.mpr (congrArg (fun _a => atTop.limUnder _a = 0) (funext (tauPartial_pi lam)))
                                                 (Tendsto.limUnder_eq tendsto_const_nhds)

theorem tauSeries_neg_pi  : tauSeries lam (-π) = 0 := Eq.mpr (congrArg (fun _a => atTop.limUnder _a = 0) (funext (tauPartial_neg_pi lam)))
                                                        (Tendsto.limUnder_eq tendsto_const_nhds)

end

section

variable {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π)
include hΔ hx

theorem abs_kInv_lt  :
    |kInv (lamOf Δ) x| < π := by
  have hlam := lamOf_pos hΔ
  
  have hm := kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  rw [abs_lt]
  have hk := kMap_kInv hlam x
  refine ⟨lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_⟩
  · intro h
    have : x = -π := by rw [← hk, ← h, kMap_neg_pi]
    exact hx.1.ne this.symm
  · intro h
    
    exact hx.2.ne (by rw [← hk, h, kMap_pi])

/-- In the open interval the literal series (2.1) is the continuous representative. -/
theorem tau_eq_tauCont  :
    tau Δ x = tauCont Δ x := tauSeries_eq (lamOf_pos hΔ) (abs_kInv_lt hΔ hx)

end

end PottsDiscontinuity.Bethe
