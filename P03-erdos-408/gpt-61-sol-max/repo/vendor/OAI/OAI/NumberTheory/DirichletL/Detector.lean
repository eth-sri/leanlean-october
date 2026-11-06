module
public import Mathlib.Tactic

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace OAI

namespace SevenEighths.Detector

section
variable (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n) {lo hi base x e : ℝ} (he : 0 < e)

include hn in
theorem exists_small_increment      
      (hlo : lo ≤ M 0) (hhi : M n ≤ hi)
    (hwidth : hi - lo ≤ n * e) :
    ∃ i < n, M (i + 1) - M i ≤ e := by
  by_contra h
  have hinc : ∀ i ∈ Finset.range n, e < M (i + 1) - M i := by
    grind
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) hinc
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_sub] at hs
  linarith

include he in
theorem exists_grid_rounding     (hx : base ≤ x) :
    ∃ k : ℕ, base + e * k ≤ x ∧ x < base + e * k + e := by
  let k := ⌊(x - base) / e⌋₊
  have hnonneg : 0 ≤ (x - base) / e := div_nonneg (sub_nonneg.mpr hx) he.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((x - base) / e)
  have hlo' := (le_div_iff₀ he).mp hlo
  have hhi' := (div_lt_iff₀ he).mp hhi
  refine ⟨k, ?_, ?_⟩ <;> dsimp [k] <;> nlinarith

include hn he in
theorem exists_buffered_bin      
       
    (hbound : ∀ j ≤ n, (51 / 100 : ℝ) ≤ M j ∧ M j ≤ 1)
    (hwidth : (49 / 100 : ℝ) ≤ n * e) :
    ∃ i < n, ∃ k : ℕ,
      let a : ℝ := 51 / 100 + e * k
      a ≤ 1 ∧ a ≤ M i ∧ M i < a + e ∧ M (i + 1) < a + 2 * e := by
  obtain ⟨i, hi, hstep⟩ := exists_small_increment M hn (e := e)
    (hbound 0 (Nat.zero_le _)).1 (hbound n le_rfl).2 (by linarith)
  obtain ⟨k, hklo, hkhi⟩ := exists_grid_rounding he (hbound i hi.le).1
  grind

end

theorem simultaneous_saturation {U δ r m ε A B : ℝ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprod : U ^ (δ * (r + m) - ε) ≤ A * B)
    (hupperA : A ≤ U ^ (δ * r + ε))
    (hupperB : B ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ A ∧ U ^ (δ * m - 2 * ε) ≤ B := by
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hBcoarse : B ≤ U ^ (δ * m + ε) := by
    apply hupperB.trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le
      (by bound)
  have hpupper : A * B ≤ U ^ (δ * r + ε + (δ * min m (1 - m) + ε)) := by
    rw [Real.rpow_add hU0]
    exact mul_le_mul hupperA hupperB hB (Real.rpow_nonneg hU0.le _)
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp (hprod.trans hpupper)
  have hlength : m ≤ 1 / 2 + 75 * ε := by
    by_cases hm : m ≤ 1 / 2
    · linarith
    · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
      rw [hmin] at hexp
      have hm0 : 0 ≤ m - 1 / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hδ hm0
      nlinarith
  have hlowerA : U ^ (δ * r - 2 * ε) ≤ A := by
    have hp : U ^ (δ * r - 2 * ε) * U ^ (δ * m + ε) ≤
        A * U ^ (δ * m + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := mul_le_mul_of_nonneg_left hBcoarse hA
    have hpos := Real.rpow_pos_of_pos hU0 (δ * m + ε)
    nlinarith
  have hlowerB : U ^ (δ * m - 2 * ε) ≤ B := by
    have hp : U ^ (δ * m - 2 * ε) * U ^ (δ * r + ε) ≤
        B * U ^ (δ * r + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hupperA hB
    have hpos := Real.rpow_pos_of_pos hU0 (δ * r + ε)
    nlinarith
  exact ⟨hlength, hlowerA, hlowerB⟩

end SevenEighths.Detector

end OAI
