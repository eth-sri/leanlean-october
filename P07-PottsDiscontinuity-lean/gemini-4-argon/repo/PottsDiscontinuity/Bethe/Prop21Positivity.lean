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

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-! ### Positivity of `ρ` -/

theorem Rsech_pos {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : 0 < Rsech lam α := by
  unfold Rsech
  have : 0 < ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) :=
    (summable_sech_periodic hlam α).tsum_pos (fun j => by positivity) 0 (by positivity)
  positivity

/-- **Strict positivity of `ρ`** (Proposition 2.1): `ρ_Δ(x) > 0`. -/
theorem rho_pos {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : 0 < rho Δ x := by
  have hlam := lamOf_pos hΔ
  rw [rho_eq hΔ]
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  have := Rsech_pos hlam (kInv (lamOf Δ) x)
  positivity

/-! ### The uniform lower bound for `Δ ≤ Δ₀ < -1` -/

private theorem abs_Rsech_sub_half_le {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    |Rsech lam α - 1 / 2| ≤ 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  rw [Rsech_eq_trigSeries hlam, trigSeries, add_sub_cancel_left]
  have hb (n : ℕ) : |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
    have h1 := abs_trigTerm_le (secCoeff lam) (fun _ => (0 : ℝ)) n α
    simp only [abs_zero, add_zero, abs_of_pos (secCoeff_pos lam n)] at h1
    linarith [secCoeff_le hlam n]
  have hgeo : HasSum (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1))
      (2 * Real.exp (-lam) / (1 - Real.exp (-lam))) := by
    convert ((hasSum_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))) using 1
    · funext n; ring
    · field_simp
  have hsum := (hasSum_trigTerm (summable_secCoeff hlam) summable_zero α).summable
  have hnorm : |∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| ≤
      ∑' n, |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
  exact (hnorm.trans (hsum.abs.tsum_le_tsum hb hgeo.summable)).trans_eq hgeo.tsum_eq

theorem exp_neg_three_le : Real.exp (-3) ≤ 1 / 9 := by
  have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [show Real.exp (-3) = (Real.exp 1)⁻¹ ^ 3 by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring]
  have h4 : (Real.exp 1)⁻¹ ≤ 10 / 27 := by
    rw [inv_eq_one_div]
    exact (one_div_le_one_div_of_le (by norm_num) h1).trans_eq (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) h4 3).trans (by norm_num)

/-- For `λ ≥ 3`, `R ≥ 1/4` (the cosine series has `∑ 1/cosh(λ m) ≤ 1/4`). -/
theorem Rsech_ge_quarter {lam : ℝ} (hlam : 3 ≤ lam) (α : ℝ) : 1 / 4 ≤ Rsech lam α := by
  have hl : 0 < lam := by linarith
  have h := (abs_le.mp (abs_Rsech_sub_half_le hl α)).1
  have hq : Real.exp (-lam) ≤ 1 / 9 := (Real.exp_le_exp.2 (by linarith)).trans exp_neg_three_le
  have h1 : 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-- For `λ₀ ≤ λ ≤ 3`, `|α| ≤ π`: `R(α) ≥ (π/6) / cosh(π²/(2λ₀))` (keep only the term `j = 0`). -/
theorem Rsech_ge_of_le_three {lam lam0 : ℝ} (h0 : 0 < lam0) (h1 : lam0 ≤ lam) (h2 : lam ≤ 3)
    {α : ℝ} (hα : |α| ≤ π) :
    (π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0))) ≤ Rsech lam α := by
  have hpi := Real.pi_pos
  have hl : 0 < lam := by linarith
  unfold Rsech
  have hterm : 1 / Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) ≤
      ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) :=
    (summable_sech_periodic hl α).le_tsum 0 (fun j _ => by positivity)
  have hc : Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) ≤ Real.cosh (π ^ 2 / (2 * lam0)) := by
    rw [Real.cosh_le_cosh]
    simp only [Int.cast_zero, mul_zero, zero_add]
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by positivity : (0 : ℝ) < 2 * lam),
      abs_of_pos (by positivity : (0 : ℝ) < π ^ 2 / (2 * lam0)), sq]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hα hpi.le) (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
  have h3 := (one_div_le_one_div_of_le (Real.cosh_pos _) hc).trans hterm
  have h4 : π / 6 ≤ π / (2 * lam) := div_le_div_of_nonneg_left hpi.le (by positivity) (by linarith)
  exact mul_le_mul h4 h3 (by positivity) (by positivity)

/-- The uniform lower bound for `R`: for `λ ≥ λ₀ > 0` and `|α| ≤ π`. -/
theorem Rsech_lower_bound {lam0 : ℝ} (h0 : 0 < lam0) {lam : ℝ} (h1 : lam0 ≤ lam) {α : ℝ}
    (hα : |α| ≤ π) :
    min (1 / 4) ((π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0)))) ≤ Rsech lam α := by
  rcases le_total 3 lam with h | h
  · exact (min_le_left _ _).trans (Rsech_ge_quarter h α)
  · exact (min_le_right _ _).trans (Rsech_ge_of_le_three h0 h1 h hα)

theorem Xi_le_exp_ratio {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Xi lam α ≤ (Real.exp lam + 1) / (Real.exp lam - 1) := by
  refine (Xi_bounds hlam α).2.trans_eq ?_
  have hE : 1 < Real.exp lam := by simpa using hlam
  have hE0 : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg,
    div_eq_div_iff (by rw [show (Real.exp lam + (Real.exp lam)⁻¹) / 2 - 1 =
      (Real.exp lam - 1) ^ 2 / (2 * Real.exp lam) by field_simp; ring]; positivity) (by linarith)]
  field_simp; ring

theorem exp_ratio_mono {lam0 lam : ℝ} (h0 : 0 < lam0) (h : lam0 ≤ lam) :
    (Real.exp lam + 1) / (Real.exp lam - 1) ≤ (Real.exp lam0 + 1) / (Real.exp lam0 - 1) := by
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  have hE : Real.exp lam0 ≤ Real.exp lam := Real.exp_le_exp.2 h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem lamOf_mono {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (h : Δ ≤ Δ₀) : lamOf Δ₀ ≤ lamOf Δ := by
  have hΔ : Δ < -1 := lt_of_le_of_lt h hΔ₀
  have : Real.cosh (lamOf Δ₀) ≤ Real.cosh (lamOf Δ) := by
    rw [cosh_lamOf hΔ, cosh_lamOf hΔ₀]; linarith
  rwa [Real.cosh_le_cosh, abs_of_pos (lamOf_pos hΔ), abs_of_pos (lamOf_pos hΔ₀)] at this

/-- **Uniform lower bound** (the constant `m_ρ` of Section 2.2): for every `Δ₀ < -1` there is
`m_ρ > 0` with `ρ_Δ(x) ≥ m_ρ` for all `Δ ≤ Δ₀` and all `x ∈ [-π, π]`; an explicit constant is
given. -/
theorem rho_uniform_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x ∈ Icc (-π) π, m ≤ rho Δ x := by
  have hpi := Real.pi_pos
  set lam0 := lamOf Δ₀
  have h0 : 0 < lam0 := lamOf_pos hΔ₀
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  set X0 := (Real.exp lam0 + 1) / (Real.exp lam0 - 1) with hX0
  have hX0pos : 0 < X0 := div_pos (by linarith) (by linarith)
  set mR := min (1 / 4) ((π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0)))) with hmR
  have hmR : 0 < mR := lt_min (by norm_num) (by positivity)
  refine ⟨mR / (2 * π * X0), by positivity, fun Δ hΔ x hx => ?_⟩
  have hΔ1 : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  have hlam := lamOf_pos hΔ1
  have hle := lamOf_mono hΔ₀ hΔ
  have hα := kInv_mem_Icc hlam hx
  rw [rho_eq hΔ1]
  have hR := Rsech_lower_bound h0 hle (abs_le.2 ⟨hα.1, hα.2⟩)
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  have hXle : Xi (lamOf Δ) (kInv (lamOf Δ) x) ≤ X0 :=
    (Xi_le_exp_ratio hlam _).trans (exp_ratio_mono h0 hle)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hR (mul_le_mul_of_nonneg_left hXle (by positivity : (0 : ℝ) ≤ 2 * π))
    (by positivity) (Rsech_pos hlam (kInv (lamOf Δ) x)).le]

/-! ### A uniform upper bound -/

theorem Xi_ge_exp_ratio {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    (Real.exp lam - 1) / (Real.exp lam + 1) ≤ Xi lam α := by
  refine le_trans (le_of_eq ?_) (Xi_bounds hlam α).1
  have hE : 1 < Real.exp lam := by simpa using hlam
  have hE0 : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg,
    div_eq_div_iff (by linarith) (by rw [show (Real.exp lam + (Real.exp lam)⁻¹) / 2 + 1 =
      (Real.exp lam + 1) ^ 2 / (2 * Real.exp lam) by field_simp; ring]; positivity)]
  field_simp; ring

theorem exp_ratio_mono' {lam0 lam : ℝ} (h0 : 0 < lam0) (h : lam0 ≤ lam) :
    (Real.exp lam0 - 1) / (Real.exp lam0 + 1) ≤ (Real.exp lam - 1) / (Real.exp lam + 1) := by
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  have hE : Real.exp lam0 ≤ Real.exp lam := Real.exp_le_exp.2 h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- **Uniform upper bound**: for every `Δ₀ < -1` there is `M_ρ` with `ρ_Δ(x) ≤ M_ρ` for all
`Δ ≤ Δ₀` and all `x ∈ [-π, π]` (used for `ρ` bounded above uniformly in `Δ ≤ Δ₀`). -/
theorem rho_uniform_upper_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ M : ℝ, ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x : ℝ, rho Δ x ≤ M := by
  have hpi := Real.pi_pos
  set lam0 := lamOf Δ₀
  have h0 : 0 < lam0 := lamOf_pos hΔ₀
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  have hq0 : 0 < Real.exp (-lam0) := Real.exp_pos _
  have hq1 : Real.exp (-lam0) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set Y0 := (Real.exp lam0 - 1) / (Real.exp lam0 + 1)
  have hY0pos : 0 < Y0 := div_pos (by linarith) (by linarith)
  set B := 1 / 2 + 2 * Real.exp (-lam0) / (1 - Real.exp (-lam0)) with hB
  have hBpos : 0 < B := add_pos (by norm_num) (div_pos (by positivity) (by linarith))
  refine ⟨B / (2 * π * Y0), fun Δ hΔ x => ?_⟩
  have hΔ1 : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  have hlam := lamOf_pos hΔ1
  have hle := lamOf_mono hΔ₀ hΔ
  rw [rho_eq hΔ1]
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  have hR := (abs_le.mp (abs_Rsech_sub_half_le hlam (kInv (lamOf Δ) x))).2
  have hRq : 1 / 2 + 2 * Real.exp (-(lamOf Δ)) / (1 - Real.exp (-(lamOf Δ))) ≤ B := by
    rw [hB]
    have hq : Real.exp (-(lamOf Δ)) ≤ Real.exp (-lam0) := Real.exp_le_exp.2 (by linarith)
    have hqlt : Real.exp (-(lamOf Δ)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have : 2 * Real.exp (-(lamOf Δ)) / (1 - Real.exp (-(lamOf Δ))) ≤
        2 * Real.exp (-lam0) / (1 - Real.exp (-lam0)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    linarith
  have hY : Y0 ≤ Xi (lamOf Δ) (kInv (lamOf Δ) x) :=
    (exp_ratio_mono' h0 hle).trans (Xi_ge_exp_ratio hlam _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul (by linarith : Rsech (lamOf Δ) (kInv (lamOf Δ) x) ≤ B)
    (mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 2 * π))
    (by positivity) hBpos.le]

end PottsDiscontinuity.Bethe
