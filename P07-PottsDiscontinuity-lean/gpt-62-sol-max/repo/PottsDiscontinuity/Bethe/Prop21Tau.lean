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
and is the unique integrable solution there (`eq_tauCont_of_isCOESolution_of_integrableOn`).

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
noncomputable def tau (Δ x : ℝ) : ℝ := tauSeries (lamOf Δ) (kInv (lamOf Δ) x)

/-- Coefficients of the smooth periodic part `U` of `T`: `u_n = 2(-1)^n (1 - tanh(λ(n+1)))/(n+1)`. -/
noncomputable def tauCoeff (lam : ℝ) (n : ℕ) : ℝ :=
  2 * (-1) ^ n * (1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ))) / ((n : ℝ) + 1)

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
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp
  simp

section

variable (lam : ℝ) (n : ℕ)

theorem one_sub_tanh_eq_mul_secCoeff :
    1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) = Real.exp (-lam) ^ (n + 1) * secCoeff lam n := by
  rw [one_sub_tanh_eq]
  unfold secCoeff
  have h2 : Real.exp (-lam) ^ (n + 1) = Real.exp (-(lam * ((n + 1 : ℕ) : ℝ))) := by
    rw [← Real.exp_nat_mul]; ring
  rw [h2]; ring

theorem secCoeff_le_one : secCoeff lam n ≤ 1 := by
  unfold secCoeff
  rw [div_le_one (Real.cosh_pos _)]
  exact Real.one_le_cosh _

theorem abs_tauCoeff_le :
    |tauCoeff lam n| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  have hq : 0 < Real.exp (-lam) ^ (n + 1) := by positivity
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := secCoeff_pos lam n
  have h3 := secCoeff_le_one lam n
  have h4 : 0 ≤ 1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) := by
    rw [h1]; positivity
  have h5 : 1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-lam) ^ (n + 1) := by
    rw [h1]; nlinarith
  unfold tauCoeff
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hn, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (two_pos : (0:ℝ) < 2), abs_of_nonneg h4]
  rw [div_le_iff₀ hn]
  nlinarith

end

theorem summable_tauCoeff {lam : ℝ} (hlam : 0 < lam) : Summable (tauCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by simp_all
  have hs : Summable (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
    grind
  exact Summable.of_norm_bounded hs (fun n => by rw [Real.norm_eq_abs]; exact abs_tauCoeff_le lam n)

theorem continuous_tauU {lam : ℝ} (hlam : 0 < lam) : Continuous (tauU lam) :=
  continuous_trigSeries summable_zero (summable_tauCoeff hlam) 0

theorem continuous_TcontFn {lam : ℝ} (hlam : 0 < lam) : Continuous (TcontFn lam) :=
  continuous_neg.add (continuous_tauU hlam)

/-- `(1 + e^{-2λ(n+1)}) u_n = -4 (-1)^{n+1} e^{-2λ(n+1)}/(n+1)`. -/
theorem one_add_mul_tauCoeff {lam : ℝ} (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * tauCoeff lam n =
      -(2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / ((n : ℝ) + 1))) := by
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := one_add_exp_two_mul_div_cosh (lam := lam) n
  have h3 : Real.exp (-(2 * lam)) ^ (n + 1) = Real.exp (-lam) ^ (n + 1) * Real.exp (-lam) ^ (n + 1) := by
    have e : Real.exp (-(2 * lam)) = Real.exp (-lam) * Real.exp (-lam) := by
      rw [← Real.exp_add]; ring
    rw [e, mul_pow]
  unfold tauCoeff
  rw [h1]
  grind

/-- `U + (1/2π) Ξ_{2λ} * U = -2 sawS(2λ)`. -/
theorem tauU_add_xiConv {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    tauU lam α + xiConv (2 * lam) (tauU lam) α = -2 * sawS (2 * lam) α := by
  unfold tauU
  rw [trigSeries_add_xiConv (by positivity) summable_zero (summable_tauCoeff hlam), trigSeries, sawS, ← tsum_mul_left]
  simp only [mul_zero, zero_add, one_add_mul_tauCoeff]
  congr 1
  funext n
  ring

/-- The key identity of the existence half for `τ`: `T + (1/2π) Ξ_{2λ} * T = Ψ`
(equation (cOE') of the source) for `T = -α + U_λ`. -/
theorem TcontFn_add_xiConv {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ) :
    TcontFn (lamOf Δ) α + xiConv (2 * lamOf Δ) (TcontFn (lamOf Δ)) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hneg : IntervalIntegrable (fun β : ℝ => -β) volume (-π) π :=
    continuous_neg.intervalIntegrable _ _
  have hU : IntervalIntegrable (tauU (lamOf Δ)) volume (-π) π :=
    (continuous_tauU hlam).intervalIntegrable _ _
  have hfun : TcontFn (lamOf Δ) = fun β => -β + tauU (lamOf Δ) β := rfl
  rw [hfun, xiConv_add hlam2 hneg hU, xiConv_neg_id hlam2, PsiFn_eq_neg_sub_sawS hΔ]
  have := tauU_add_xiConv hlam α
  simp only
  linarith

theorem Ttrans_tauCont {Δ : ℝ} (hΔ : Δ < -1) :
    Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := by
  grind [kInv_kMap, Ttrans, tauCont, Real.pi_pos, lamOf_pos]

/-- **Proposition 2.1, existence for `τ`**: the continuous representative `τ_c` of `τ` solves
(cOE_Δ) at every `x ∈ [-π, π]`, including the end points (where `τ_c(±π) = ∓1/2`). -/
theorem tauCont_isCOESolution {Δ : ℝ} (hΔ : Δ < -1) : IsCOESolution Δ (tauCont Δ) := by
  rw [isCOESolution_iff hΔ, Ttrans_tauCont hΔ]
  intro α _
  exact TcontFn_add_xiConv hΔ α

theorem continuous_tauCont {Δ : ℝ} (hΔ : Δ < -1) : Continuous (tauCont Δ) := by
  have hlam := lamOf_pos hΔ
  exact ((continuous_TcontFn hlam).comp (continuous_kInv hlam)).div_const _

/-! ### The literal series (2.1) for `τ` -/

/-- For `|α| < π` the partial sums of the series (2.1) for `τ` converge to `T(α)/(2π)`
with `T = -α + U_λ`, i.e. to the continuous representative. -/
theorem tendsto_tauPartial {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π) :
    Tendsto (tauPartial lam α) atTop (𝓝 (TcontFn lam α / (2 * π))) := by
  have h1 := tendsto_sawtooth hα
  have hU := (hasSum_trigTerm (a := fun _ => (0 : ℝ)) (b := tauCoeff lam) summable_zero
    (summable_tauCoeff hlam) α).tendsto_sum_nat
  have h2 := (h1.add (hU.const_mul (1 / 2))).const_mul (1 / π)
  have hval : 1 / π * (-α / 2 + 1 / 2 * ∑' n, trigTerm (fun _ => (0 : ℝ)) (tauCoeff lam) n α) =
      TcontFn lam α / (2 * π) := by
    unfold TcontFn tauU trigSeries
    simp only [zero_add]
    unfold trigTerm
    field_simp
  rw [hval] at h2
  refine h2.congr (fun N => ?_)
  unfold tauPartial
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold tauCoeff trigTerm
  field_simp
  rw [pow_succ (-1 : ℝ) i]
  ring

theorem tauSeries_eq {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π) :
    tauSeries lam α = TcontFn lam α / (2 * π) :=
  (tendsto_tauPartial hlam hα).limUnder_eq

section

variable (lam : ℝ)

end

theorem abs_kInv_lt {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π) :
    |kInv (lamOf Δ) x| < π := by
  have hlam := lamOf_pos hΔ
  grind [kMap_pi, kMap_neg_pi, lt_of_le_of_ne, kMap_kInv, kInv_mem_Icc]

/-- In the open interval the literal series (2.1) is the continuous representative. -/
theorem tau_eq_tauCont {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π) :
    tau Δ x = tauCont Δ x := by
  exact tauSeries_eq (lamOf_pos hΔ) (abs_kInv_lt hΔ hx)

end PottsDiscontinuity.Bethe
