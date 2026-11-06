module

public import Chazelle.Core.SpecPhases
public import Chazelle.RewriteTactics
public import Chazelle.ChainTactics

/-!
# WP-J up phase: the arithmetic of the grades

Chain `i` of grade `g` starts at `i 2^g` and has `min (2^g, n - 1 - i 2^g)` edges; there are
`(n - 2)/2^g + 1` of them.  Chain `i` of grade `g + 1` is the union of chains `2i` and `2i + 1`
of grade `g`, or chain `2i` itself when `2i + 1` does not exist (`gradeLen_succ_two`,
`gradeLen_succ_one`); the top grade has one chain, of `n - 1` edges (`gradeCount_top`,
`gradeLen_top`).
-/

namespace Chazelle.Core.Up

@[expose] public section

variable {n g i : ℕ}

theorem gradeStart_succ (g i : ℕ) : gradeStart (g + 1) i = gradeStart g (2 * i) := by
  urring gradeStart [pow_succ]

theorem gradeCount_succ (n g : ℕ) : gradeCount n (g + 1) = (n - 2) / 2 ^ g / 2 + 1 := by
  unfold gradeCount; rw [pow_succ, Nat.div_div_eq_div_mul]

/-- A chain of a grade has at least one edge and fits in the curve. -/
theorem gradeLen_pos (hn : 2 ≤ n) (hi : i < gradeCount n g) : 1 ≤ gradeLen n g i := by
  unfold gradeLen gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have : i * 2 ^ g ≤ n - 2 := by
    by_contra hc
    have : (n - 2) / 2 ^ g < i := by
      rwo [Nat.div_lt_iff_lt_mul hpos]
    omega
  have := Nat.one_le_two_pow (n := g)
  apply le_min this; omega

theorem gradeLen_le (n g i : ℕ) : gradeLen n g i ≤ 2 ^ g := min_le_left _ _

theorem gradeLen_fit (hn : 2 ≤ n) (hi : i < gradeCount n g) :
    gradeStart g i + gradeLen n g i + 1 ≤ n := by
  unfold gradeLen gradeStart gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have : i * 2 ^ g ≤ n - 2 := by
    by_contra hc
    have : (n - 2) / 2 ^ g < i := by
      rwo [Nat.div_lt_iff_lt_mul hpos]
    omega
  have := min_le_right (2 ^ g) (n - 1 - i * 2 ^ g)
  omega

/-- **The union of two children.** -/
theorem gradeLen_succ_two (hn : 2 ≤ n) (h : 2 * i + 1 < gradeCount n g) :
    gradeLen n g (2 * i) = 2 ^ g ∧
      gradeLen n (g + 1) i = gradeLen n g (2 * i) + gradeLen n g (2 * i + 1) ∧
      gradeStart g (2 * i + 1) = gradeStart g (2 * i) + gradeLen n g (2 * i) := by
  unfold gradeLen gradeStart gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have h1 : (2 * i + 1) * 2 ^ g ≤ n - 2 := by
    by_contra hc
    have : (n - 2) / 2 ^ g < 2 * i + 1 := by rwo [Nat.div_lt_iff_lt_mul hpos]
    omega
  have e : (2 * i + 1) * 2 ^ g = 2 * i * 2 ^ g + 2 ^ g := by ring
  have e2 : i * 2 ^ (g + 1) = 2 * i * 2 ^ g := by rwring [pow_succ]
  rw [e2]
  refine ⟨min_eq_left (by omega), ?_, ?_⟩
  · rw [min_eq_left (show 2 ^ g ≤ n - 1 - 2 * i * 2 ^ g by omega), pow_succ]
    rcases le_total (2 ^ g) (n - 1 - (2 * i + 1) * 2 ^ g) with h2 | h2
    · rwring [min_eq_left h2, min_eq_left (by omega)]
    · rwo [min_eq_right h2, min_eq_right (by omega)]
  · rwring [min_eq_left (by omega)]

/-- **A single child.** -/
theorem gradeLen_succ_one (hn : 2 ≤ n) (_hi : i < gradeCount n (g + 1))
    (h : gradeCount n g ≤ 2 * i + 1) : gradeLen n (g + 1) i = gradeLen n g (2 * i) := by
  unfold gradeLen gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have e2 : i * 2 ^ (g + 1) = 2 * i * 2 ^ g := by rwring [pow_succ]
  rw [e2]
  have h1 : n - 2 < (2 * i + 1) * 2 ^ g := by
    have : (n - 2) / 2 ^ g < 2 * i + 1 := by omega
    rwa [Nat.div_lt_iff_lt_mul hpos] at this
  have e : (2 * i + 1) * 2 ^ g = 2 * i * 2 ^ g + 2 ^ g := by ring
  rw [min_eq_right (show n - 1 - 2 * i * 2 ^ g ≤ 2 ^ (g + 1) by rwo [pow_succ]),
    min_eq_right (show n - 1 - 2 * i * 2 ^ g ≤ 2 ^ g by omega)]

/-- The top grade has a single chain. -/
theorem gradeCount_top (hn : 2 ≤ n) : gradeCount n (topGrade n) = 1 := by
  unfold gradeCount topGrade
  have := Nat.le_pow_clog (b := 2) (by norm_num) (n - 1)
  rw [Nat.div_eq_of_lt (by omega)]

theorem gradeLen_top (_hn : 2 ≤ n) : gradeLen n (topGrade n) 0 = n - 1 := by
  unfold gradeLen topGrade
  have := Nat.le_pow_clog (b := 2) (by norm_num) (n - 1)
  simp only [Nat.zero_mul, Nat.sub_zero]
  exact min_eq_right this

end

end Chazelle.Core.Up
