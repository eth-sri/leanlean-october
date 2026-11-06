module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1: positivity of `ρ` and the uniform lower bound `m_ρ`

* `rho_pos`: `ρ_Δ(x) > 0` for every `Δ < -1` and every `x` (all terms of the sum in (2.1) are
  positive and `k' = Ξ_λ > 0`);
* `rho_uniform_lower_bound` (the constant `m_ρ > 0` used in Section 2.2, the infimum of `ρ`
  over `x ∈ [-π, π]` and `Δ ≤ Δ₀`): for `Δ₀ < -1` there is `m_ρ > 0`
  with `ρ_Δ(x) ≥ m_ρ` for all `Δ ≤ Δ₀` and `x ∈ [-π, π]`.  The proof splits at `λ = 3`: for
  `λ ≥ 3` the cosine series `R = 1/2 + ∑ cos(mα)/cosh(λ m)` gives `R ≥ 1/4`; for `λ₀ ≤ λ ≤ 3`
  only the term `j = 0` of the periodised sech is kept; and `k' = Ξ_λ ≤ (e^λ+1)/(e^λ-1) ≤
  (e^{λ₀}+1)/(e^{λ₀}-1)`;
* `rho_uniform_upper_bound`: for `Δ₀ < -1`, `ρ_Δ(x) ≤ M_ρ` for all `Δ ≤ Δ₀` (from `R ≤ 1/2 + 2/(e^λ-1)`
  and `k' = Ξ_λ ≥ (e^λ-1)/(e^λ+1)`).
-/

public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-! ### Positivity of `ρ` -/

theorem Rsech_pos {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : 0 < Rsech lam α := by
  unfold Rsech
  have hs := summable_sech_periodic hlam α
  have  :=
    hs.tsum_pos (fun j => by positivity) 0 (by positivity)
  positivity

/-- **Strict positivity of `ρ`** (Proposition 2.1): `ρ_Δ(x) > 0`. -/
theorem rho_pos {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : 0 < rho Δ x := by
  have hlam := lamOf_pos hΔ
  rw [rho_eq hΔ]
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  have := Rsech_pos hlam (kInv (lamOf Δ) x)
  positivity

/-! ### The uniform lower bound for `Δ ≤ Δ₀ < -1` -/

theorem abs_Rsech_sub_half_le {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    |Rsech lam α - 1 / 2| ≤ 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := by
  have hgeo := (hasSum_geometric_of_lt_one (Real.exp_pos (-lam)).le (by simp_all)).mul_left (2 * Real.exp (-lam))
  have hsum := (hasSum_trigTerm (summable_secCoeff hlam) summable_zero α).summable
  rw [Rsech_eq_trigSeries hlam, trigSeries, add_sub_cancel_left]
  calc _ ≤ ∑' n, |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, 2 * Real.exp (-lam) * Real.exp (-lam) ^ n := hsum.abs.tsum_le_tsum (fun n => by grind [abs_trigTerm_le (secCoeff lam) (fun _ => (0 : ℝ)) n α, secCoeff_le hlam n, secCoeff_pos lam n, pow_succ]) hgeo.summable
    _ = _ := by rw [hgeo.tsum_eq, div_eq_mul_inv]

/-- For `λ ≥ 3`, `R ≥ 1/4` (the cosine series has `∑ 1/cosh(λ m) ≤ 1/4`). -/
theorem Rsech_ge_quarter {lam : ℝ} (hlam : 3 ≤ lam) (α : ℝ) : 1 / 4 ≤ Rsech lam α := by
  have h := (abs_le.1 (abs_Rsech_sub_half_le (by linarith) α)).1
  have hq : Real.exp (-lam) ≤ 1 / 9 := by
    refine (Real.exp_le_exp.2 (by linarith : -lam ≤ -3)).trans ?_
    rw [Real.exp_neg, inv_le_comm₀ (by positivity) (by norm_num), show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  have h1 : 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- For `λ₀ ≤ λ ≤ 3`, `|α| ≤ π`: `R(α) ≥ (π/6) / cosh(π²/(2λ₀))` (keep only the term `j = 0`). -/
theorem Rsech_ge_of_le_three {lam lam0 : ℝ} (h0 : 0 < lam0) (h1 : lam0 ≤ lam) (h2 : lam ≤ 3)
    {α : ℝ} (hα : |α| ≤ π) :
    (π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0))) ≤ Rsech lam α := by
  have hpi := Real.pi_pos
  have hl : 0 < lam := by linarith
  have hs := summable_sech_periodic hl α
  have hterm :=
    hs.le_tsum 0 (fun j _ => by positivity)
  have hc : Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) ≤ Real.cosh (π ^ 2 / (2 * lam0)) := by
    simp
    have e : |π * α / (2 * lam)| = π * |α| / (2 * lam) := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by positivity : (0:ℝ) < 2 * lam)]
    have e1 : π * |α| / (2 * lam) ≤ π * π / (2 * lam) := by gcongr
    have e2 : π * π / (2 * lam) ≤ π ^ 2 / (2 * lam0) := by
      rw [sq]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    grind
  have h3 :=
    one_div_le_one_div_of_le (Real.cosh_pos _) hc
  have h4 : π / 6 ≤ π / (2 * lam) := by
    apply div_le_div_of_nonneg_left hpi.le (by positivity); linarith
  calc π / 6 * (1 / Real.cosh (π ^ 2 / (2 * lam0)))
      ≤ π / (2 * lam) * (1 / Real.cosh (π ^ 2 / (2 * lam0))) := by gcongr
    _ ≤ π / (2 * lam) * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) := by
        gcongr; linarith

/-- The uniform lower bound for `R`: for `λ ≥ λ₀ > 0` and `|α| ≤ π`. -/
theorem Rsech_lower_bound {lam0 : ℝ} (h0 : 0 < lam0) {lam : ℝ} (h1 : lam0 ≤ lam) {α : ℝ}
    (hα : |α| ≤ π) :
    min (1 / 4) ((π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0)))) ≤ Rsech lam α := by
  rcases le_total 3 lam with h | h
  · grind [Rsech_ge_quarter]
  · exact (min_le_right _ _).trans (Rsech_ge_of_le_three h0 h1 h hα)

theorem Xi_le_exp_ratio {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Xi lam α ≤ (Real.exp lam + 1) / (Real.exp lam - 1) := by
  have h := (Xi_bounds hlam α).2
  refine h.trans (le_of_eq ?_)
  have hE : 1 < Real.exp lam := by simp_all
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  grind

theorem exp_ratio_mono {lam0 lam : ℝ} (h0 : 0 < lam0) (h : lam0 ≤ lam) :
    (Real.exp lam + 1) / (Real.exp lam - 1) ≤ (Real.exp lam0 + 1) / (Real.exp lam0 - 1) := by
  have hE0 : 1 < Real.exp lam0 := by simp_all
  have hE := Real.exp_le_exp.2 h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem lamOf_mono {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (h : Δ ≤ Δ₀) : lamOf Δ₀ ≤ lamOf Δ := by
  have hΔ : Δ < -1 := by linarith
  have h3 := cosh_lamOf hΔ
  have h4 := cosh_lamOf hΔ₀
  have : Real.cosh (lamOf Δ₀) ≤ Real.cosh (lamOf Δ) := by linarith
  rw [Real.cosh_le_cosh, abs_of_pos (lamOf_pos hΔ), abs_of_pos (lamOf_pos hΔ₀)] at this
  omega

/-- **Uniform lower bound** (the constant `m_ρ` of Section 2.2): for every `Δ₀ < -1` there is
`m_ρ > 0` with `ρ_Δ(x) ≥ m_ρ` for all `Δ ≤ Δ₀` and all `x ∈ [-π, π]`; an explicit constant is
given. -/
theorem rho_uniform_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x ∈ Icc (-π) π, m ≤ rho Δ x := by
  set lam0 := lamOf Δ₀ with hlam0
  have h0 := lamOf_pos hΔ₀
  have hE0 : 1 < Real.exp lam0 := by simp_all
  set X0 := (Real.exp lam0 + 1) / (Real.exp lam0 - 1) with hX0
  set mR := min (1 / 4) ((π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0)))) with hmR
  refine ⟨mR / (2 * π * X0), by positivity, fun Δ hΔ x hx => ?_⟩
  have hΔ1 : Δ < -1 := by linarith
  have hlam := lamOf_pos hΔ1
  have hle := lamOf_mono hΔ₀ hΔ
  have hα := kInv_mem_Icc hlam hx
  have habs : |kInv (lamOf Δ) x| ≤ π := by grind
  rw [rho_eq hΔ1]
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc mR * (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) ≤ Rsech (lamOf Δ) (kInv (lamOf Δ) x) * (2 * π * X0) := by
        have := Rsech_pos hlam (kInv (lamOf Δ) x)
        nlinarith [mul_le_mul (Rsech_lower_bound h0 hle habs) (mul_le_mul_of_nonneg_left ((Xi_le_exp_ratio hlam _).trans (exp_ratio_mono h0 hle)) (by positivity : (0:ℝ) ≤ 2 * π))
          (by positivity) this.le]
    _ = _ := by ring


/-! ### A uniform upper bound -/

section
variable {lam : ℝ} (hlam : 0 < lam) (α : ℝ)
include hlam
theorem Xi_ge_exp_ratio  :
    (Real.exp lam - 1) / (Real.exp lam + 1) ≤ Xi lam α := by
  refine le_trans (le_of_eq ?_) ((Xi_bounds hlam α).1)
  have hE : 1 < Real.exp lam := by simp_all
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  grind
end

theorem exp_ratio_mono' {lam0 lam : ℝ} (h0 : 0 < lam0) (h : lam0 ≤ lam) :
    (Real.exp lam0 - 1) / (Real.exp lam0 + 1) ≤ (Real.exp lam - 1) / (Real.exp lam + 1) := by
  have hE0 : 1 < Real.exp lam0 := by simp_all
  have hE := Real.exp_le_exp.2 h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Uniform upper bound**: for every `Δ₀ < -1` there is `M_ρ` with `ρ_Δ(x) ≤ M_ρ` for all
`Δ ≤ Δ₀` and all `x ∈ [-π, π]` (used for `ρ` bounded above uniformly in `Δ ≤ Δ₀`). -/
theorem rho_uniform_upper_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ M : ℝ, ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x : ℝ, rho Δ x ≤ M := by
  set lam0 := lamOf Δ₀ with hlam0
  have h0 := lamOf_pos hΔ₀
  have hE0 : 1 < Real.exp lam0 := by simp_all
  have hq1 : Real.exp (-lam0) < 1 := by simp_all
  set Y0 := (Real.exp lam0 - 1) / (Real.exp lam0 + 1) with hY0
  set B := 1 / 2 + 2 * Real.exp (-lam0) / (1 - Real.exp (-lam0)) with hB
  have hBpos : 0 < B := by
    positivity
  refine ⟨B / (2 * π * Y0), fun Δ hΔ x => ?_⟩
  have hΔ1 : Δ < -1 := by linarith
  have hlam := lamOf_pos hΔ1
  have hle := lamOf_mono hΔ₀ hΔ
  rw [rho_eq hΔ1]
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  have hR := (abs_le.1 (abs_Rsech_sub_half_le hlam (kInv (lamOf Δ) x))).2
  have hRq : 1 / 2 + 2 * Real.exp (-(lamOf Δ)) / (1 - Real.exp (-(lamOf Δ))) ≤ B := by
    have hq : Real.exp (-(lamOf Δ)) ≤ Real.exp (-lam0) := by simp_all
    have : 2 * Real.exp (-(lamOf Δ)) / (1 - Real.exp (-(lamOf Δ))) ≤
        2 * Real.exp (-lam0) / (1 - Real.exp (-lam0)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have hY : Y0 ≤ Xi (lamOf Δ) (kInv (lamOf Δ) x) :=
    (exp_ratio_mono' h0 hle).trans (Xi_ge_exp_ratio hlam _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul ((sub_le_iff_le_add'.1 hR).trans hRq) (mul_le_mul_of_nonneg_left hY (by positivity : (0:ℝ) ≤ 2 * π))
    (by positivity) hBpos.le]

end PottsDiscontinuity.Bethe
