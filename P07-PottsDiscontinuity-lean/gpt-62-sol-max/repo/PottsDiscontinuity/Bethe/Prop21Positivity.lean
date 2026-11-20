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
  have hs := summable_sech_periodic hlam α
  have : 0 < ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) :=
    hs.tsum_pos (fun j => by positivity) 0 (by positivity)
  positivity

/-- **Strict positivity of `ρ`** (Proposition 2.1): `ρ_Δ(x) > 0`. -/
theorem rho_pos {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : 0 < rho Δ x := by
  have hlam := lamOf_pos hΔ
  rw [rho_eq hΔ]
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  have := Rsech_pos hlam (kInv (lamOf Δ) x)
  positivity

/-- The cosine-series deviation is bounded by a geometric series at any smaller parameter. -/
private theorem Rsech_deviation {lam₀ lam : ℝ} (h₀ : 0 < lam₀) (hle : lam₀ ≤ lam) (α : ℝ) :
    |Rsech lam α - 1 / 2| ≤ 2 * Real.exp (-lam₀) / (1 - Real.exp (-lam₀)) := by
  let r := Real.exp (-lam₀)
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlam := h₀.trans_le hle
  let f n := trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α
  have hf : Summable f := (hasSum_trigTerm (summable_secCoeff hlam) summable_zero α).summable
  have hgeo : HasSum (fun n : ℕ => 2 * r ^ (n + 1)) (2 * r / (1 - r)) := by
    simpa [pow_succ', mul_assoc, div_eq_mul_inv] using
          (hasSum_geometric_of_lt_one hr.le hr₁).mul_left (2 * r)
  rw [Rsech_eq_trigSeries hlam, trigSeries, add_sub_cancel_left]
  calc |∑' n, f n| ≤ ∑' n, |f n| := by
        simpa using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ, 2 * r ^ (n + 1) := hf.abs.tsum_le_tsum (fun n => by
      have hn : |f n| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
        grind only [abs_of_pos, abs_zero, secCoeff_pos, secCoeff_le, abs_trigTerm_le]
      exact hn.trans (by dsimp [r]; gcongr)) hgeo.summable
    _ = _ := hgeo.tsum_eq

private theorem exp_neg_three_le : Real.exp (-3) ≤ 1 / 9 := by
  have h : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [show (-3 : ℝ) = (3 : ℕ) * (-1) by norm_num, Real.exp_nat_mul, Real.exp_neg]
  exact (pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) h) _).trans (by norm_num)

private theorem Rsech_ge_quarter {lam : ℝ} (hlam : 3 ≤ lam) (α : ℝ) : 1 / 4 ≤ Rsech lam α := by
  have h := (abs_le.mp (Rsech_deviation (by norm_num : (0 : ℝ) < 3) hlam α)).1
  have hq : 2 * Real.exp (-3) / (1 - Real.exp (-3)) ≤ 1 / 4 :=
    (div_le_iff₀ (by linarith [exp_neg_three_le])).2 (by linarith [exp_neg_three_le])
  linarith

private theorem Rsech_ge_of_le_three {lam lam₀ : ℝ} (h₀ : 0 < lam₀) (h₁ : lam₀ ≤ lam)
    (h₂ : lam ≤ 3) {α : ℝ} (hα : |α| ≤ π) :
    π / 6 / Real.cosh (π ^ 2 / (2 * lam₀)) ≤ Rsech lam α := by
  have hlam := h₀.trans_le h₁
  have hc : Real.cosh (π * α / (2 * lam)) ≤ Real.cosh (π ^ 2 / (2 * lam₀)) := by
    rw [Real.cosh_le_cosh, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by positivity : 0 < 2 * lam), abs_of_pos (by positivity : 0 < π ^ 2 / (2 * lam₀)), sq]
    gcongr
  have ht := (summable_sech_periodic hlam α).le_tsum (0 : ℤ) (fun _ _ => by positivity)
  simp only [Int.cast_zero, mul_zero, zero_add] at ht
  rw [Rsech, div_eq_mul_inv]
  calc π / 6 * (Real.cosh (π ^ 2 / (2 * lam₀)))⁻¹ ≤
        π / (2 * lam) * (1 / Real.cosh (π * α / (2 * lam))) := by
        rw [← one_div]
        gcongr <;> linarith
    _ ≤ _ := by gcongr

private theorem Rsech_lower_bound {lam₀ lam α : ℝ} (h₀ : 0 < lam₀) (h₁ : lam₀ ≤ lam)
    (hα : |α| ≤ π) :
    min (1 / 4) (π / 6 / Real.cosh (π ^ 2 / (2 * lam₀))) ≤ Rsech lam α := by
  rcases le_total 3 lam with h | h
  · exact (min_le_left ..).trans (Rsech_ge_quarter h α)
  · exact (min_le_right ..).trans (Rsech_ge_of_le_three h₀ h₁ h hα)

/-- A common upper bound and its reciprocal bound the Poisson kernel above a cutoff. -/
theorem exists_Xi_uniform_bounds {l : ℝ} (hl : 0 < l) :
    ∃ X : ℝ, 1 < X ∧ ∀ μ ≥ l, ∀ α, X⁻¹ ≤ Xi μ α ∧ Xi μ α ≤ X := by
  let R (x : ℝ) := (Real.exp x + 1) / (Real.exp x - 1)
  have hR (x : ℝ) (hx : 0 < x) : 1 < R x := by
    exact (lt_div_iff₀ (sub_pos.2 (Real.one_lt_exp_iff.2 hx))).2 (by linarith)
  refine ⟨R l, hR l hl, fun μ hμ α => ?_⟩
  have hμ' := hl.trans_le hμ
  have h0 := Real.one_lt_exp_iff.2 hl
  have h1 := Real.one_lt_exp_iff.2 hμ'
  have h : R μ ≤ R l := by
    dsimp only [R]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [Real.exp_le_exp.2 hμ]
  have hhi : Real.sinh μ / (Real.cosh μ - 1) = R μ := by
    grind only [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have hlo : Real.sinh μ / (Real.cosh μ + 1) = (R μ)⁻¹ := by
    rw [show (R μ)⁻¹ = (Real.exp μ - 1) / (Real.exp μ + 1) by simp [R]]
    grind only [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  obtain ⟨hL, hU⟩ := Xi_bounds hμ' α
  rw [hhi] at hU
  rw [hlo] at hL
  exact ⟨(inv_anti₀ (zero_lt_one.trans (hR μ hμ')) h).trans hL, hU.trans h⟩

theorem lamOf_mono {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (h : Δ ≤ Δ₀) : lamOf Δ₀ ≤ lamOf Δ := by
  have hΔ : Δ < -1 := lt_of_le_of_lt h hΔ₀
  have h1 := lamOf_pos hΔ
  have h2 := lamOf_pos hΔ₀
  have h3 := cosh_lamOf hΔ
  have h4 := cosh_lamOf hΔ₀
  have : Real.cosh (lamOf Δ₀) ≤ Real.cosh (lamOf Δ) := by simp_all
  simpa [abs_of_pos h1, abs_of_pos h2] using this

/-- Uniform positive lower bound on `ρ` in the physical interval. -/
theorem rho_uniform_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x ∈ Icc (-π) π, m ≤ rho Δ x := by
  let l := lamOf Δ₀
  let A := min (1 / 4) (π / 6 / Real.cosh (π ^ 2 / (2 * l)))
  have h₀ : 0 < l := lamOf_pos hΔ₀
  obtain ⟨X, hX, hXi⟩ := exists_Xi_uniform_bounds h₀
  have hXpos := zero_lt_one.trans hX
  have hA : 0 < A := lt_min (by norm_num) (by positivity)
  refine ⟨A / (2 * π * X), by positivity, fun Δ hΔ x hx => ?_⟩
  have hd := hΔ.trans_lt hΔ₀
  have hl := lamOf_pos hd
  have hle := lamOf_mono hΔ₀ hΔ
  have ha := kInv_mem_Icc hl hx
  have hxpos := Xi_pos hl (kInv (lamOf Δ) x)
  rw [rho_eq hd]
  exact div_le_div₀ (hA.le.trans (Rsech_lower_bound h₀ hle (abs_le.mpr ha)))
    (Rsech_lower_bound h₀ hle (abs_le.mpr ha)) (by positivity)
    (mul_le_mul_of_nonneg_left (hXi _ hle _).2 (by positivity))

/-- Uniform upper bound on `ρ`. -/
theorem rho_uniform_upper_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ M : ℝ, ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x : ℝ, rho Δ x ≤ M := by
  let l := lamOf Δ₀
  let B := 1 / 2 + 2 * Real.exp (-l) / (1 - Real.exp (-l))
  have h₀ : 0 < l := lamOf_pos hΔ₀
  obtain ⟨X, hX, hXi⟩ := exists_Xi_uniform_bounds h₀
  have hXpos := zero_lt_one.trans hX
  have hE := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos h₀))
  refine ⟨B / (2 * π * X⁻¹), fun Δ hΔ x => ?_⟩
  have hd := hΔ.trans_lt hΔ₀
  have hle := lamOf_mono hΔ₀ hΔ
  have h := (abs_le.mp (Rsech_deviation h₀ hle (kInv (lamOf Δ) x))).2
  rw [rho_eq hd]
  refine div_le_div₀ (by positivity) (by dsimp [B]; linarith) (by positivity) ?_
  gcongr
  exact (hXi _ hle _).1

end PottsDiscontinuity.Bethe
