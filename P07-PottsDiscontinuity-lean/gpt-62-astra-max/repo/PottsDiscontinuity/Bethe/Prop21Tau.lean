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
  ∑ n ∈ Finset.range N, (-1) ^ (n + 1) / (π * (n + 1)) * Real.tanh (lam * ↑(n + 1)) *
    Real.sin (↑(n + 1) * α)

/-- The literal series `τ(x) = ∑_{m>0} (-1)^m/(π m) tanh(λ m) sin(m α)` of (2.1) at `α`,
as the limit of the partial sums (the series is not absolutely summable). -/
noncomputable def tauSeries (lam α : ℝ) : ℝ := limUnder atTop (tauPartial lam α)

/-- The literal `τ` of (2.1): `τ(x) = tauSeries λ (k^{-1}(x))`. -/
noncomputable def tau (Δ x : ℝ) : ℝ := tauSeries (lamOf Δ) (kInv (lamOf Δ) x)

section
variable (lam : ℝ) (n : ℕ)

include lam n in
/-- Coefficients of the smooth periodic part `U` of `T`: `u_n = 2(-1)^n (1 - tanh(λ(n+1)))/(n+1)`. -/
noncomputable def tauCoeff : ℝ :=
  2 * (-1) ^ n * (1 - Real.tanh (lam * ↑(n + 1))) / (n + 1)

/-- `U_λ(α) = ∑_{n≥0} u_n sin((n+1)α)`, absolutely convergent. -/
noncomputable def tauU (lam α : ℝ) : ℝ := trigSeries 0 (fun _ => 0) (tauCoeff lam) α

/-- `T(α) = 2π τ(k(α))` for the continuous representative: `T(α) = -α + U_λ(α)`. -/
noncomputable def TcontFn (lam α : ℝ) : ℝ := -α + tauU lam α

/-- The continuous representative of `τ`: `τ_c(x) = T(k^{-1}(x))/(2π)`; it equals the series
(2.1) for `|x| < π` and takes the values `∓1/2` at `x = ±π`. -/
noncomputable def tauCont (Δ x : ℝ) : ℝ :=
  TcontFn (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π)

theorem one_sub_tanh_eq (x : ℝ) : 1 - Real.tanh x = Real.exp (-x) / Real.cosh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  simp

theorem one_sub_tanh_eq_mul_secCoeff :
    1 - Real.tanh (lam * ↑(n + 1)) = Real.exp (-lam) ^ (n + 1) * secCoeff lam n := by
  rw [one_sub_tanh_eq]
  unfold secCoeff
  have h2 : Real.exp (-lam) ^ (n + 1) = Real.exp (-(lam * ↑(n + 1))) := by
    rw [← Real.exp_nat_mul]; ring
  grind

theorem secCoeff_le_one : secCoeff lam n ≤ 1 := by
  unfold secCoeff
  rw [div_le_one (Real.cosh_pos _)]
  exact Real.one_le_cosh _

theorem abs_tauCoeff_le :
    |tauCoeff lam n| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := secCoeff_pos lam n
  have h3 := secCoeff_le_one lam n
  have h4 : 0 ≤ 1 - Real.tanh (lam * ↑(n + 1)) := by
    rw [h1]; positivity
  unfold tauCoeff
  have hn : 0 < (n : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hn, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos two_pos, abs_of_nonneg h4, div_le_iff₀ hn]
  nlinarith

end

section
variable {lam : ℝ} (hlam : 0 < lam)

include hlam in
theorem summable_tauCoeff : Summable (tauCoeff lam) := by
  have hr1 : Real.exp (-lam) < 1 := by grind [Real.exp_lt_one_iff]
  exact Summable.of_norm_bounded (by
    have := (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left (2 * Real.exp (-lam))
    grind) (fun n => abs_tauCoeff_le lam n)

include hlam in
theorem continuous_tauU : Continuous (tauU lam) :=
  continuous_trigSeries summable_zero (summable_tauCoeff hlam) 0

include hlam in
theorem continuous_TcontFn : Continuous (TcontFn lam) :=
  continuous_neg.add (continuous_tauU hlam)

/-- `(1 + e^{-2λ(n+1)}) u_n = -4 (-1)^{n+1} e^{-2λ(n+1)}/(n+1)`. -/
theorem one_add_mul_tauCoeff (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * tauCoeff lam n =
      -(2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / (n + 1))) := by
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := one_add_exp_two_mul_div_cosh (lam := lam) n
  have h3 : Real.exp (-(2 * lam)) ^ (n + 1) = Real.exp (-lam) ^ (n + 1) * Real.exp (-lam) ^ (n + 1) := by
    have e : Real.exp (-(2 * lam)) = Real.exp (-lam) * Real.exp (-lam) := by
      rw [← Real.exp_add]; ring
    rw [e, mul_pow]
  unfold tauCoeff
  grind

include hlam in
/-- `U + (1/2π) Ξ_{2λ} * U = -2 sawS(2λ)`. -/
theorem tauU_add_xiConv (α : ℝ) :
    tauU lam α + xiConv (2 * lam) (tauU lam) α = -2 * sawS (2 * lam) α := by
  have hlam2 : 0 < 2 * lam := by linarith
  have hr1 : Real.exp (-(2 * lam)) < 1 := by grind [Real.exp_lt_one_iff]
  have hu := summable_tauCoeff hlam
  have hz : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hX :=
    xiConv_trigSeries hlam2 hz hu 0 α
  have hz2 : Summable (fun n : ℕ => Real.exp (-(2 * lam)) ^ (n + 1) * 0) := by simp
  have h3 := (hasSum_trigTerm hz hu α).add (hasSum_trigTerm hz2 (summable_pow_succ_mul hu (Real.exp_pos _).le hr1.le) α)
  have e1 : tauU lam α = 0 + ∑' n, trigTerm (fun _ => 0) (tauCoeff lam) n α := rfl
  have e2 : xiConv (2 * lam) (tauU lam) α = 0 +
      ∑' n, trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) n α := by
    assumption
  have h5 : (fun n => trigTerm (fun _ => 0) (tauCoeff lam) n α +
      trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) n α) =
      fun n : ℕ => -2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / (n + 1) *
        Real.sin (↑(n + 1) * α)) := by
    grind [trigTerm, one_add_mul_tauCoeff]
  rw [h5] at h3
  have h6 := h3.unique ((hasSum_xiConv_neg_id hlam2 α).mul_left (-2))
  simp_all [xiConv_neg_id hlam2, e1, e2]

end

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ

/-- The key identity of the existence half for `τ`: `T + (1/2π) Ξ_{2λ} * T = Ψ`
(equation (cOE') of the source) for `T = -α + U_λ`. -/
theorem TcontFn_add_xiConv (α : ℝ) :
    TcontFn (lamOf Δ) α + xiConv (2 * lamOf Δ) (TcontFn (lamOf Δ)) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hfun : TcontFn (lamOf Δ) = fun β => -β + tauU (lamOf Δ) β := rfl
  rw [hfun, xiConv_add hlam2 (continuous_neg.intervalIntegrable _ _) ((continuous_tauU hlam).intervalIntegrable _ _), xiConv_neg_id hlam2, PsiFn_eq_neg_sub_sawS hΔ]
  have := tauU_add_xiConv hlam α
  linarith

theorem Ttrans_tauCont :
    Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := by
  funext α
  unfold Ttrans tauCont
  rw [kInv_kMap (lamOf_pos hΔ)]
  field_simp

/-- **Proposition 2.1, existence for `τ`**: the continuous representative `τ_c` of `τ` solves
(cOE_Δ) at every `x ∈ [-π, π]`, including the end points (where `τ_c(±π) = ∓1/2`). -/
theorem tauCont_isCOESolution : IsCOESolution Δ (tauCont Δ) := by
  rw [isCOESolution_iff hΔ, Ttrans_tauCont hΔ]
  intro α _
  exact TcontFn_add_xiConv hΔ α

theorem continuous_tauCont : Continuous (tauCont Δ) := by
  have hlam := lamOf_pos hΔ
  exact ((continuous_TcontFn hlam).comp (continuous_kInv hlam)).div_const _

/-- **Proposition 2.1, uniqueness for `τ`** (integrable version): every integrable solution of
(cOE_Δ) on `[-π, π]` coincides with `τ_c` at every point of `[-π, π]`. -/
theorem eq_tauCont_of_isCOESolution_of_integrableOn {τ' : ℝ → ℝ}
    (hτ' : IntegrableOn τ' (Icc (-π) π) volume) (h : IsCOESolution Δ τ') :
    ∀ x ∈ Icc (-π) π, τ' x = tauCont Δ x := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi := Real.pi_pos
  have hT'eq := (isCOESolution_iff hΔ τ').1 h
  have hTeq := (isCOESolution_iff hΔ _).1 (tauCont_isCOESolution hΔ)
  have hTrho := Ttrans_tauCont hΔ
  rw [hTrho] at hTeq
  have hT'int : IntegrableOn (Ttrans Δ τ') (Icc (-π) π) volume := Integrable.const_mul (integrableOn_comp_kMap_of_Xi hlam hτ') _
  have hT'ii := intervalIntegrable_of_integrableOn_Icc hT'int
  have hTii : IntervalIntegrable (TcontFn (lamOf Δ)) volume (-π) π :=
    (continuous_TcontFn hlam).intervalIntegrable _ _
  have hae2 := ae_eq_of_comp_kMap hlam hτ' (integrableOn_Icc_of_continuous (continuous_tauCont hΔ)) (by
    have h1 : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)),
        Ttrans Δ τ' β - TcontFn (lamOf Δ) β = 0 := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      exact (eq_zero_of_eq_neg_xiConv hlam2 (hT'ii.sub hTii) (by grind [xiConv_sub hlam2 hT'ii hTii]))
    filter_upwards [h1] with β hβ
    have : Ttrans Δ τ' β = Ttrans Δ (tauCont Δ) β := by
      rw [hTrho]; linarith
    grind [Ttrans])
  intro x hx
  have h3 := h x hx
  have h4 := tauCont_isCOESolution hΔ x hx
  have h5 : cOEop Δ τ' x = cOEop Δ (tauCont Δ) x := by
    unfold cOEop
    congr 1
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂(volume.restrict (Ioc (-π) π)), τ' y = tauCont Δ y := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact hae2
    filter_upwards [this] with y hy
    grind
  grind

end

/-! ### The literal series (2.1) for `τ` -/

section
variable {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π)
include hlam hα

/-- For `|α| < π` the partial sums of the series (2.1) for `τ` converge to `T(α)/(2π)`
with `T = -α + U_λ`, i.e. to the continuous representative. -/
theorem tendsto_tauPartial :
    Tendsto (tauPartial lam α) atTop (𝓝 (TcontFn lam α / (2 * π))) := by
  have hU := (hasSum_trigTerm summable_zero
    (summable_tauCoeff hlam) α).tendsto_sum_nat
  have h2 := ((tendsto_sawtooth hα).add (hU.const_mul (1 / 2))).const_mul (1 / π)
  have hval : 1 / π * (-α / 2 + 1 / 2 * ∑' n, trigTerm (fun _ => 0) (tauCoeff lam) n α) =
      TcontFn lam α / (2 * π) := by
    unfold TcontFn tauU trigSeries
    grind [zero_add, trigTerm]
  rw [hval] at h2
  refine h2.congr (fun N => ?_)
  unfold tauPartial
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  grind [tauCoeff, trigTerm]

theorem tauSeries_eq :
    tauSeries lam α = TcontFn lam α / (2 * π) :=
  (tendsto_tauPartial hlam hα).limUnder_eq

end

variable {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π)
include hΔ hx

theorem abs_kInv_lt :
    |kInv (lamOf Δ) x| < π := by
  have hlam := lamOf_pos hΔ
  have hm := kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  rw [abs_lt]
  have hk := kMap_kInv hlam x
  refine ⟨lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_⟩
  · grind [kMap_neg_pi]
  · intro h
    simp_all [h, kMap_pi]

/-- In the open interval the literal series (2.1) is the continuous representative. -/
theorem tau_eq_tauCont :
    tau Δ x = tauCont Δ x := tauSeries_eq (lamOf_pos hΔ) (abs_kInv_lt hΔ hx)

end PottsDiscontinuity.Bethe
