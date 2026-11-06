module

public import PottsDiscontinuity.TorusCrossing.Lattice

/-!
# Closed one-cochains are exact (planar Poincare lemma on the rotated lattice)

A `ZMod 2`-valued function `f` on medial vertices is a *cochain*; its *degree* at a cell is
the sum over the four corners.  If the degree vanishes at every primal cell strictly between
two vertical lines, the left-ray potential `g(z) = sum_{a <= z.1} f(a, z.2) + c(z.2)` is a
primitive: `g` of the two dual endpoints of `m` sums to `f m`, for every medial vertex `m`
whose abscissa is between the two lines.  The correction `c` absorbs the (arbitrary) defects
on the left line; defects on the right line never enter.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

/-- Degree of a cochain at a cell: the sum over its four corners. -/
def cdeg (f : Cell → ZMod 2) (c : Cell) : ZMod 2 :=
  f c + f (c.1 + 1, c.2) + f (c.1, c.2 + 1) + f (c.1 + 1, c.2 + 1)

section
variable (x0 : ℤ) (f : Cell → ZMod 2)
/-- Partial row sum of `f` over columns `x0 + 1, ..., i` of row `j`. -/
def rowSum (j i : ℤ) : ZMod 2 :=
  ∑ a ∈ Finset.Icc (x0 + 1) i, f (a, j)

/-- Defect of the cochain at the primal cell `(x0, k)` of the left line (zero for odd cells). -/
def leftDefect (k : ℤ) : ZMod 2 :=
  if IsPrimal (x0, k) then cdeg f (x0, k) else 0
end

section
variable (x0 y0 : ℤ) (f : Cell → ZMod 2)
/-- Accumulated left defects below row `j`, counted from row `y0`. -/
def leftCorr (j : ℤ) : ZMod 2 :=
  ∑ k ∈ Finset.Ico y0 j, leftDefect x0 f k

/-- The left-ray potential. -/
def leftPotential (z : Cell) : ZMod 2 :=
  rowSum x0 f z.2 z.1 + leftCorr x0 y0 f z.2
end

section
variable (x0 : ℤ) (f : Cell → ZMod 2)
theorem rowSum_succ (j i : ℤ) (h : x0 ≤ i) :
    rowSum x0 f j (i + 1) = rowSum x0 f j i + f (i + 1, j) := by
  unfold rowSum
  rw [show Finset.Icc (x0 + 1) (i + 1) = insert (i + 1) (Finset.Icc (x0 + 1) i) by
    grind]
  grind

theorem rowSum_of_le (j i : ℤ) (h : i ≤ x0) :
    rowSum x0 f j i = 0 := by
  simp_all [rowSum]

/-- The two-step recursion for the sum of two consecutive row sums. -/
theorem rowSum_pair_step (b X : ℤ) (hX : x0 ≤ X - 2) :
    rowSum x0 f b X + rowSum x0 f (b - 1) X =
      rowSum x0 f b (X - 2) + rowSum x0 f (b - 1) (X - 2) + cdeg f (X - 1, b - 1) := by
  have h1 : rowSum x0 f b X = rowSum x0 f b (X - 2) + f (X - 1, b) + f (X, b) := by
    have := rowSum_succ x0 f b (X - 2) hX
    have h2 := rowSum_succ x0 f b (X - 1) (by omega)
    grind
  have h2 : rowSum x0 f (b - 1) X =
      rowSum x0 f (b - 1) (X - 2) + f (X - 1, b - 1) + f (X, b - 1) := by
    have := rowSum_succ x0 f (b - 1) (X - 2) hX
    have h2 := rowSum_succ x0 f (b - 1) (X - 1) (by omega)
    grind
  grind [cdeg]
end

/-- Core identity: with left defects absorbed, consecutive row sums add up to the defect of the
left line. -/
theorem rowSum_pair (x0 : ℤ) (w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (b : ℤ) : ∀ n : ℕ, (n : ℤ) ≤ w → ((x0 + n + b) % 2 = 0) →
      rowSum x0 f b (x0 + n) + rowSum x0 f (b - 1) (x0 + n) = leftDefect x0 f (b - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpar
    have hnotprim : n % 2 = 0 → ¬ IsPrimal (x0, b - 1) := by
      grind [IsPrimal]
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · -- n = 0
        have : leftDefect x0 f (b - 1) = 0 := by
          unfold leftDefect; simp_all
        simp_all [rowSum_of_le]
      grind [IsPrimal, leftDefect, cdeg, rowSum, rowSum_succ, rowSum_of_le]
    · -- n ≥ 2
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
      have hprim : IsPrimal (x0 + ((k + 2 : ℕ) : ℤ) - 1, b - 1) := by
        grind [IsPrimal]
      have hstep := rowSum_pair_step x0 f b (x0 + ((k + 2 : ℕ) : ℤ)) (by omega)
      grind


/-- Integer-indexed version of `rowSum_pair`. -/
theorem rowSum_pair' (x0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (b X : ℤ) (h1 : x0 ≤ X) (h2 : X ≤ x0 + w) (hp : (X + b) % 2 = 0) :
    rowSum x0 f b X + rowSum x0 f (b - 1) X = leftDefect x0 f (b - 1) := by
  have := rowSum_pair x0 w f hx0 hdeg b (X - x0).toNat (by omega) (by omega)
  simp_all

theorem leftCorr_succ (x0 y0 : ℤ) (f : Cell → ZMod 2)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0) (b : ℤ) :
    leftCorr x0 y0 f b + leftCorr x0 y0 f (b - 1) = leftDefect x0 f (b - 1) := by
  by_cases h : y0 ≤ b - 1
  · unfold leftCorr
    rw [show Finset.Ico y0 b = insert (b - 1) (Finset.Ico y0 (b - 1)) by
      grind,
      Finset.sum_insert (by simp)]
    grind
  · unfold leftCorr
    rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
    have hd : leftDefect x0 f (b - 1) = 0 := by
      unfold leftDefect cdeg
      grind
    simp_all



theorem leftPotential_primitive (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (m : Cell) (hm1 : x0 < m.1) (hm2 : m.1 ≤ x0 + w) :
    leftPotential x0 y0 f (dualEnds m).1 + leftPotential x0 y0 f (dualEnds m).2 = f m := by
  obtain ⟨a, b⟩ := m
  have hcc := leftCorr_succ x0 y0 f hy0 b
  unfold dualEnds leftPotential
  split_ifs with hpar
  · have h1 := rowSum_pair' x0 w f hx0 hdeg b a (by omega) (by omega) (by omega)
    have h2 := rowSum_succ x0 f b (a - 1) (by omega)
    grind
  · have h1 := rowSum_pair' x0 w f hx0 hdeg b (a - 1) (by omega) (by omega) (by omega)
    have h2 := rowSum_succ x0 f b (a - 1) (by omega)
    grind


section
variable (x0 y0 w : ℤ) (f : Cell → ZMod 2) (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0) (hxw : ∀ m : Cell, x0 + w < m.1 → f m = 0) (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0) (hclosed : ∀ c : Cell, IsPrimal c → x0 ≤ c.1 → c.1 ≤ x0 + w → cdeg f c = 0) (hw : 0 ≤ w)
include y0 hx0 hxw hy0 hclosed hw
/-- Full row sums vanish for a cochain that is closed at every primal cell of the strip
`x0 ≤ x ≤ x0 + w` and supported in `x0 < a ≤ x0 + w`, `b > y0`. -/
theorem rowSum_full_zero (j : ℤ) : rowSum x0 f j (x0 + w) = 0 := by
  have hld : ∀ k, leftDefect x0 f k = 0 := by
    unfold leftDefect; grind
  -- consecutive full row sums agree
  have hpair : ∀ b : ℤ, rowSum x0 f b (x0 + w) + rowSum x0 f (b - 1) (x0 + w) = 0 := by
    intro b
    by_cases hpar : (x0 + w + b) % 2 = 0
    · have := rowSum_pair' x0 w f hx0 (fun c hc h1 h2 => hclosed c hc h1.le h2.le) b (x0 + w)
        (by omega) le_rfl hpar
      grind
    · have := rowSum_pair' x0 (w + 1) f hx0 (by grind) b (x0 + w + 1) (by omega) (by omega) (by omega)
      grind [rowSum_succ]
  have hup : ∀ n : ℕ, rowSum x0 f (y0 + n) (x0 + w) = 0 := by
    intro n
    induction n with
    | zero =>
      apply Finset.sum_eq_zero
      grind
    | succ n ih =>
      grind
  by_cases hj : y0 ≤ j
  · have := hup (j - y0).toNat
    grind
  · apply Finset.sum_eq_zero
    grind

/-- **Boundary behaviour of the primitive of a globally closed cochain.** -/
theorem leftPotential_zero_of_closed (z : Cell) (hz : z.1 ≤ x0 ∨ x0 + w ≤ z.1) :
    leftPotential x0 y0 f z = 0 := by
  have hld : ∀ k, leftDefect x0 f k = 0 := by
    unfold leftDefect; grind
  have hcorr : leftCorr x0 y0 f z.2 = 0 :=
    Finset.sum_eq_zero (fun k _ => hld k)
  unfold leftPotential
  rw [hcorr, add_zero]
  rcases hz with hz | hz
  · grind [rowSum_of_le]
  · have h0 := rowSum_full_zero x0 y0 w f hx0 hxw hy0 hclosed hw z.2
    by_cases hzw : z.1 = x0 + w
    · grind
    · rw [← h0]
      symm
      apply Finset.sum_subset <;> grind
end
end PottsDiscontinuity.TorusCrossing
