module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecPhases

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
  core_grind

theorem gradeCount_succ (n g : ℕ) : gradeCount n (g + 1) = (n - 2) / 2 ^ g / 2 + 1 := by
  core_grind [pow_succ, Nat.div_div_eq_div_mul]

/-- A chain of a grade has at least one edge and fits in the curve. -/
theorem gradeLen_pos (hn : 2 ≤ n) (hi : i < gradeCount n g) : 1 ≤ gradeLen n g i := by
  unfold gradeLen gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have : i * 2 ^ g ≤ n - 2 := by
    by_contra hc
    have : (n - 2) / 2 ^ g < i := by
      rw [Nat.div_lt_iff_lt_mul hpos]; omega
    omega
  omega

theorem gradeLen_le (n g i : ℕ) : gradeLen n g i ≤ 2 ^ g := min_le_left _ _

section
variable (hn : 2 ≤ n)
include hn
theorem gradeLen_fit (hi : i < gradeCount n g) :
    gradeStart g i + gradeLen n g i + 1 ≤ n := by
  unfold gradeLen gradeStart gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have : i * 2 ^ g ≤ n - 2 := by
    by_contra hc
    have : (n - 2) / 2 ^ g < i := by
      rw [Nat.div_lt_iff_lt_mul hpos]; omega
    omega
  omega

/-- **The union of two children.** -/
theorem gradeLen_succ_two (h : 2 * i + 1 < gradeCount n g) :
    gradeLen n g (2 * i) = 2 ^ g ∧
      gradeLen n (g + 1) i = gradeLen n g (2 * i) + gradeLen n g (2 * i + 1) ∧
      gradeStart g (2 * i + 1) = gradeStart g (2 * i) + gradeLen n g (2 * i) := by
  unfold gradeLen gradeStart gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have h1 : (2 * i + 1) * 2 ^ g ≤ n - 2 := by
    by_contra hc
    have : (n - 2) / 2 ^ g < 2 * i + 1 := by rw [Nat.div_lt_iff_lt_mul hpos]; omega
    omega
  ram_grind

/-- **A single child.** -/
theorem gradeLen_succ_one (_hi : i < gradeCount n (g + 1))
    (h : gradeCount n g ≤ 2 * i + 1) : gradeLen n (g + 1) i = gradeLen n g (2 * i) := by
  unfold gradeLen gradeCount at *
  have hpos : 0 < 2 ^ g := by positivity
  have e2 : i * 2 ^ (g + 1) = 2 * i * 2 ^ g := by ring_nf <;> omega
  rw [e2]
  have h1 : n - 2 < (2 * i + 1) * 2 ^ g := by
    have : (n - 2) / 2 ^ g < 2 * i + 1 := by omega
    rwa [Nat.div_lt_iff_lt_mul hpos] at this
  grind

/-- The top grade has a single chain. -/
theorem gradeCount_top : gradeCount n (topGrade n) = 1 := by
  unfold gradeCount topGrade
  have := Nat.le_pow_clog (b := 2) (by norm_num) (n - 1)
  simp_all +zetaDelta <;> omega


end

theorem gradeLen_top (_hn : 2 ≤ n) : gradeLen n (topGrade n) 0 = n - 1 := by
  unfold gradeLen topGrade
  have := Nat.le_pow_clog (b := 2) (by norm_num) (n - 1)
  omega

end

end Chazelle.Core.Up
