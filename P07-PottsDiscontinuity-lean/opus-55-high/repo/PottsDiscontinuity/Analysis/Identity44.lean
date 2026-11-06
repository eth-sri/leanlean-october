module

public import Mathlib
public import PottsDiscontinuity.Analysis.HyperbolicSeries

/-!
# The identity (4.4): convergence, positivity and the value of the alternating tanh series

For every `lam > 0`, the partial sums `∑_{k=1}^N (-1)^k / k * tanh (k lam)` converge to a limit
`S`, the series `∑_{k ≥ 0} 4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))` has a sum `T`, and
`lam + 2 S = T > 0` (`identity44`).

The proof expands `tanh (m lam) / m = ∑_j c_j(m)` into partial fractions
(`hasSum_cTerm_tanh`), interchanges the (conditionally convergent) double series with Tannery's
theorem, using the alternating-series bound `|∑_{m ≤ N} (-1)^m c_j(m)| ≤ c_j(1)`
(`alt_partial_sum_bounds`), and evaluates the inner alternating series in closed form
(`hasSum_alt_cTerm`).
-/

public noncomputable section

open Filter Topology Real

namespace PottsDiscontinuity

/-! ### Alternating partial sums of an antitone nonnegative sequence -/

theorem alt_partial_sum_bounds : ∀ (N : ℕ) (u : ℕ → ℝ), Antitone u → (∀ i, 0 ≤ u i) →
    0 ≤ ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u i ∧
      ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u i ≤ u 0
  | 0, u, _, h0 => by simp_all
  | N + 1, u, hu, h0 => by
    have ih := alt_partial_sum_bounds N (fun i => u (i + 1))
      (fun a b hab => hu (by omega)) (fun i => h0 _)
    have h01 : u 1 ≤ u 0 := by tauto
    rw [Finset.sum_range_succ']
    have e : ∑ i ∈ Finset.range N, (-1 : ℝ) ^ (i + 1) * u (i + 1) =
        -∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u (i + 1) := by
      rw [← Finset.sum_neg_distrib]
      ring
    grind

theorem sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k = ∑ n ∈ Finset.range N, g (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-! ### The sum of the odd reciprocal squares -/

theorem hasSum_odd_inv_sq : HasSum (fun j : ℕ => 1 / (2 * (j : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have hz := hasSum_zeta_two
  have hev : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 / 4) := by
    have h := hz.div_const 4
    grind
  have hodd : Summable (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (fun x y h => by linarith)
  have h3 := hz.unique (HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hev hodd.hasSum)
  have e : ∑' j : ℕ, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by linarith
  rw [← e]
  convert hodd.hasSum using 1
  simp

theorem hasSum_odd_inv_sq_mul (c : ℝ) :
    HasSum (fun j : ℕ => c / (2 * (j : ℝ) + 1) ^ 2) (c * (π ^ 2 / 8)) := by
  convert hasSum_odd_inv_sq.mul_left c using 1
  ring

/-! ### The partial-fraction terms -/

section
variable (lam : ℝ) (j : ℕ)
/-- `c_j(m) = 8 lam / ((2j+1)² π² + 4 m² lam²)`, so that `tanh (m lam) / m = ∑_j c_j(m)`. -/
def cTerm (m : ℝ) : ℝ :=
  8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2 + 4 * m ^ 2 * lam ^ 2)

/-- The closed form of the inner alternating series. -/
def dTerm  : ℝ :=
  2 / ((2 * (j : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam))) -
    4 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2)
end

section
variable {lam : ℝ} (hlam : 0 < lam)
include hlam
theorem cTerm_pos (j : ℕ) (m : ℝ) : 0 < cTerm lam j m := by
  unfold cTerm
  positivity

theorem hasSum_cTerm_tanh {m : ℝ} (hm : 0 < m) :
    HasSum (fun j : ℕ => cTerm lam j m) (Real.tanh (m * lam) / m) := by
  have ha : 0 < 2 * m * lam / π := by positivity
  have h := (hasSum_inv_sq_add_odd_sq ha).mul_left (8 * lam / π ^ 2)
  grind [cTerm]

theorem hasSum_alt_cTerm (j : ℕ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1)) (dTerm lam j) := by
  set b : ℝ := (2 * (j : ℝ) + 1) * π / (2 * lam) with hb
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (-1 : ℝ) ^ n / (b ^ 2 + (n : ℝ) ^ 2)) 1
    (g := π / (2 * b * Real.sinh (π * b)) + 1 / (2 * b ^ 2))).2 (hasSum_alt_inv_sq_add_sq (by positivity))
  convert (h.mul_left (2 / lam)) using 1
  · unfold cTerm
    simp only [hb]
    push_cast
    field_simp
    ring
  · unfold dTerm
    simp
    simp only [hb]
    field_simp
    ring
end

/-! ### Bounds -/

section
variable {lam : ℝ} (hlam : 0 < lam)
include hlam
theorem cTerm_antitone (j : ℕ) :
    Antitone (fun n : ℕ => cTerm lam j ((n : ℝ) + 1)) := by
  intro a b hab
  have hab' : ((a : ℝ) + 1) ≤ (b : ℝ) + 1 := by simp_all
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg lam, mul_le_mul hab' hab' (by positivity) (by positivity)]

theorem cTerm_one_le (j : ℕ) :
    cTerm lam j (((0 : ℕ) : ℝ) + 1) ≤ 8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2) := by
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-- The partial sums of the inner alternating series are dominated by `c_j(1)`. -/
theorem norm_partial_cTerm_le (j N : ℕ) :
    ‖∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1)‖ ≤
      8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2) := by
  have hb := alt_partial_sum_bounds N (fun n : ℕ => cTerm lam j ((n : ℝ) + 1))
    (cTerm_antitone hlam j) (fun i => (cTerm_pos hlam j _).le)
  have e : ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1) =
      -∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * cTerm lam j ((n : ℝ) + 1) := by
    rw [← Finset.sum_neg_distrib]
    ring
  simp
  grind [cTerm_one_le]

theorem summable_bound  :
    HasSum (fun j : ℕ => 8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2)) (lam) := by
  have h := hasSum_odd_inv_sq_mul (8 * lam / π ^ 2)
  have hpi := Real.pi_ne_zero
  grind
end

/-! ### The terms `4 / ((2k+1) sinh (π² (2k+1) / (2 lam)))` -/

section
variable {lam : ℝ} (hlam : 0 < lam)
include hlam
theorem tTerm_pos (k : ℕ) :
    0 < 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) := by
  positivity

theorem tTerm_le (k : ℕ) :
    4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) ≤
      8 * lam / ((2 * (k : ℝ) + 1) ^ 2 * π ^ 2) := by
  have hy : 0 < π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam) := by positivity
  have hs := Real.self_le_sinh_iff.2 hy.le
  have hk : 0 < 2 * (k : ℝ) + 1 := by positivity
  calc 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))
      ≤ 4 / ((2 * (k : ℝ) + 1) * (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        simp_all
    _ = 8 * lam / ((2 * (k : ℝ) + 1) ^ 2 * π ^ 2) := by
        grind

theorem summable_tTerm  :
    Summable (fun k : ℕ =>
      4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))) :=
  Summable.of_nonneg_of_le (fun k => (tTerm_pos hlam k).le) (fun k => tTerm_le hlam k)
    (summable_bound hlam).summable

theorem dTerm_eq (j : ℕ) :
    dTerm lam j =
      (4 / ((2 * (j : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)))) / 2 -
        4 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2) := by
  grind [dTerm, Real.sinh]
end

/-! ### The main identity -/

/-- **Identity (4.4)** together with the convergence and positivity statements: for every
`lam > 0`, the partial sums of `∑ (-1)^k / k * tanh (k lam)` converge to `S`, the hyperbolic series
sums to `T`, and `lam + 2 S = T > 0`. -/
theorem identity44 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S T : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
      HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
      0 < lam + 2 * S ∧ lam + 2 * S = T := by
  have hT := (summable_tTerm hlam).hasSum
  set T := ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))
    with hTdef
  have hTpos := (summable_tTerm hlam).tsum_pos (fun k => (tTerm_pos hlam k).le) 0
    (tTerm_pos hlam 0)
  have hd : HasSum (fun j : ℕ => dTerm lam j) (T / 2 - lam / 2) := by
    have h := (hT.div_const 2).sub ((hasSum_odd_inv_sq_mul (4 * lam / π ^ 2)))
    have hpi := Real.pi_ne_zero
    grind [dTerm_eq]
  set S := ∑' j : ℕ, dTerm lam j with hSdef
  have hS := hd.tsum_eq
  refine ⟨S, T, ?_, hT, by linarith, by linarith⟩
  -- Tannery
  have hf : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / k * Real.tanh (k * lam) =
      ∑' j : ℕ, ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1) := by
    intro N
    rw [Summable.tsum_finsetSum, sum_Icc_one_eq_sum_range]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [(hasSum_cTerm_tanh hlam (by positivity)).mul_left ((-1 : ℝ) ^ (n + 1)) |>.tsum_eq]
      grind
    · intro n _
      exact ((hasSum_cTerm_tanh hlam (by positivity)).mul_left ((-1 : ℝ) ^ (n + 1))).summable
  simp_rw [hf]
  exact tendsto_tsum_of_dominated_convergence (summable_bound hlam).summable
    (fun j => (hasSum_alt_cTerm hlam j).tendsto_sum_nat)
    (Eventually.of_forall fun N j => norm_partial_cTerm_le hlam j N)

end PottsDiscontinuity
