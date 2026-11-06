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

/-- Partial row sum of `f` over columns `x0 + 1, ..., i` of row `j`. -/
def rowSum (x0 : ℤ) (f : Cell → ZMod 2) (j i : ℤ) : ZMod 2 :=
  ∑ a ∈ Finset.Icc (x0 + 1) i, f (a, j)

/-- Defect of the cochain at the primal cell `(x0, k)` of the left line (zero for odd cells). -/
def leftDefect (x0 : ℤ) (f : Cell → ZMod 2) (k : ℤ) : ZMod 2 :=
  if IsPrimal (x0, k) then cdeg f (x0, k) else 0

/-- Accumulated left defects below row `j`, counted from row `y0`. -/
def leftCorr (x0 y0 : ℤ) (f : Cell → ZMod 2) (j : ℤ) : ZMod 2 :=
  ∑ k ∈ Finset.Ico y0 j, leftDefect x0 f k

/-- The left-ray potential. -/
def leftPotential (x0 y0 : ℤ) (f : Cell → ZMod 2) (z : Cell) : ZMod 2 :=
  rowSum x0 f z.2 z.1 + leftCorr x0 y0 f z.2

theorem rowSum_succ (x0 : ℤ) (f : Cell → ZMod 2) (j i : ℤ) (h : x0 ≤ i) :
    rowSum x0 f j (i + 1) = rowSum x0 f j i + f (i + 1, j) := by
  unfold rowSum
  rw [show Finset.Icc (x0 + 1) (i + 1) = insert (i + 1) (Finset.Icc (x0 + 1) i) by
    ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp), add_comm]

theorem rowSum_of_le (x0 : ℤ) (f : Cell → ZMod 2) (j i : ℤ) (h : i ≤ x0) :
    rowSum x0 f j i = 0 := by
  unfold rowSum; rw [Finset.Icc_eq_empty (by omega)]; simp

theorem rowSum_pair_step (x0 : ℤ) (f : Cell → ZMod 2) (b X : ℤ) (hX : x0 ≤ X - 2) :
    rowSum x0 f b X + rowSum x0 f (b - 1) X =
      rowSum x0 f b (X - 2) + rowSum x0 f (b - 1) (X - 2) + cdeg f (X - 1, b - 1) := by
  have hstep (r : ℤ) : rowSum x0 f r X = rowSum x0 f r (X - 2) + f (X - 1, r) + f (X, r) := by
    have h1 := rowSum_succ x0 f r (X - 2) hX
    have h2 := rowSum_succ x0 f r (X - 1) (by omega)
    rw [show X - 2 + 1 = X - 1 by ring] at h1
    rw [show X - 1 + 1 = X by ring] at h2
    rw [h2, h1]
  rw [hstep b, hstep (b - 1)]
  unfold cdeg
  rw [show X - 1 + 1 = X by ring, show b - 1 + 1 = b by ring]
  ring

theorem rowSum_pair (x0 : ℤ) (w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (b : ℤ) : ∀ n : ℕ, (n : ℤ) ≤ w → ((x0 + n + b) % 2 = 0) →
      rowSum x0 f b (x0 + n) + rowSum x0 f (b - 1) (x0 + n) = leftDefect x0 f (b - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpar
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · rw [show leftDefect x0 f (b - 1) = 0 from ite_eq_right (by unfold IsPrimal; dsimp; omega),
          rowSum_of_le x0 f b _ (by simp), rowSum_of_le x0 f (b - 1) _ (by simp), add_zero]
      · have hprim : IsPrimal (x0, b - 1) := by unfold IsPrimal; dsimp; push_cast at hpar; omega
        have e (r : ℤ) : rowSum x0 f r (x0 + ((1 : ℕ) : ℤ)) = f (x0 + 1, r) := by
          push_cast; rw [rowSum_succ x0 f r x0 le_rfl, rowSum_of_le x0 f r x0 le_rfl, zero_add]
        unfold leftDefect cdeg
        rw [ite_eq_left hprim, e b, e (b - 1), hx0 (x0, b - 1) (by dsimp; omega),
          hx0 (x0, b - 1 + 1) (by dsimp; omega)]
        ring_nf
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
      have hprim : IsPrimal (x0 + ((k + 2 : ℕ) : ℤ) - 1, b - 1) := by
        unfold IsPrimal; dsimp; push_cast at hpar ⊢; omega
      rw [rowSum_pair_step x0 f b (x0 + ((k + 2 : ℕ) : ℤ)) (by push_cast; omega),
        hdeg _ hprim (by push_cast; omega) (by push_cast at hn ⊢; omega), add_zero,
        show x0 + ((k + 2 : ℕ) : ℤ) - 2 = x0 + (k : ℤ) by push_cast; ring]
      exact ih k (by omega) (by push_cast at hn ⊢; omega) (by push_cast at hpar ⊢; omega)

theorem rowSum_pair' (x0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (b X : ℤ) (h1 : x0 ≤ X) (h2 : X ≤ x0 + w) (hp : (X + b) % 2 = 0) :
    rowSum x0 f b X + rowSum x0 f (b - 1) X = leftDefect x0 f (b - 1) := by
  have := rowSum_pair x0 w f hx0 hdeg b (X - x0).toNat (by omega) (by omega)
  rwa [show x0 + ((X - x0).toNat : ℤ) = X by omega] at this

theorem leftCorr_succ (x0 y0 : ℤ) (f : Cell → ZMod 2)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0) (b : ℤ) :
    leftCorr x0 y0 f b + leftCorr x0 y0 f (b - 1) = leftDefect x0 f (b - 1) := by
  unfold leftCorr
  by_cases h : y0 ≤ b - 1
  · rw [show Finset.Ico y0 b = insert (b - 1) (Finset.Ico y0 (b - 1)) by
      ext a; simp only [Finset.mem_Ico, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    generalize ∑ k ∈ Finset.Ico y0 (b - 1), leftDefect x0 f k = S
    generalize leftDefect x0 f (b - 1) = d
    revert S d; decide
  · rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
    unfold leftDefect cdeg
    split_ifs
    · simp [hy0 (x0, b - 1) (by dsimp; omega), hy0 (x0 + 1, b - 1) (by dsimp; omega),
        hy0 (x0, b) (by dsimp; omega), hy0 (x0 + 1, b) (by dsimp; omega)]
    · rfl

theorem zmod2_aux1 (R1' R1 R2 C1 C2 D F : ZMod 2) (h1 : R1 + R2 = D) (hcc : C1 + C2 = D)
    (h2 : R1 = R1' + F) : (R1' + C1) + (R2 + C2) = F := by
  subst h2; revert R1' R2 C1 C2 D F; decide

theorem zmod2_aux2 (R1' R2' C1 C2 D F : ZMod 2) (h1 : R1' + R2' = D) (hcc : C1 + C2 = D) :
    (R1' + F + C1) + (R2' + C2) = F := by
  revert R1' R2' C1 C2 D F; decide

theorem leftPotential_primitive (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hdeg : ∀ c : Cell, IsPrimal c → x0 < c.1 → c.1 < x0 + w → cdeg f c = 0)
    (m : Cell) (hm1 : x0 < m.1) (hm2 : m.1 ≤ x0 + w) :
    leftPotential x0 y0 f (dualEnds m).1 + leftPotential x0 y0 f (dualEnds m).2 = f m := by
  obtain ⟨a, b⟩ := m
  dsimp only at hm1 hm2
  have hcc := leftCorr_succ x0 y0 f hy0 b
  have h2 := rowSum_succ x0 f b (a - 1) (by omega)
  rw [show a - 1 + 1 = a by ring] at h2
  unfold dualEnds leftPotential
  split_ifs with hpar <;> dsimp only
  · exact zmod2_aux1 _ _ _ _ _ _ _
      (rowSum_pair' x0 w f hx0 hdeg b a (by omega) (by omega) (by omega)) hcc h2
  · rw [h2]
    exact zmod2_aux2 _ _ _ _ _ _
      (rowSum_pair' x0 w f hx0 hdeg b (a - 1) (by omega) (by omega) (by omega)) hcc

theorem rowSum_full_zero (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hxw : ∀ m : Cell, x0 + w < m.1 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hclosed : ∀ c : Cell, IsPrimal c → x0 ≤ c.1 → c.1 ≤ x0 + w → cdeg f c = 0)
    (hw : 0 ≤ w) (j : ℤ) : rowSum x0 f j (x0 + w) = 0 := by
  have hld (k : ℤ) : leftDefect x0 f k = 0 := by
    unfold leftDefect; split_ifs with hk <;> [exact hclosed _ hk le_rfl (by simpa using hw); rfl]
  have hpair (b : ℤ) : rowSum x0 f b (x0 + w) + rowSum x0 f (b - 1) (x0 + w) = 0 := by
    by_cases hpar : (x0 + w + b) % 2 = 0
    · have := rowSum_pair' x0 w f hx0 (fun c hc h1 h2 => hclosed c hc h1.le h2.le) b (x0 + w)
        (by omega) le_rfl hpar
      rwa [hld] at this
    · have := rowSum_pair' x0 (w + 1) f hx0
        (fun c hc h1 h2 => hclosed c hc h1.le (by omega)) b (x0 + w + 1)
        (by omega) (by omega) (by omega)
      rw [hld, rowSum_succ x0 f b (x0 + w) (by omega), rowSum_succ x0 f (b - 1) (x0 + w) (by omega),
        hxw (x0 + w + 1, b) (by dsimp; omega), hxw (x0 + w + 1, b - 1) (by dsimp; omega)] at this
      simpa using this
  have hup (n : ℕ) : rowSum x0 f (y0 + n) (x0 + w) = 0 := by
    induction n with
    | zero => exact Finset.sum_eq_zero fun a _ => hy0 _ (by dsimp; omega)
    | succ n ih =>
      have := hpair (y0 + ((n + 1 : ℕ) : ℤ))
      rwa [show y0 + ((n + 1 : ℕ) : ℤ) - 1 = y0 + (n : ℤ) by push_cast; ring, ih, add_zero] at this
  by_cases hj : y0 ≤ j
  · have := hup (j - y0).toNat
    rwa [show y0 + ((j - y0).toNat : ℤ) = j by omega] at this
  · exact Finset.sum_eq_zero fun a _ => hy0 _ (by dsimp; omega)

theorem leftPotential_zero_of_closed (x0 y0 w : ℤ) (f : Cell → ZMod 2)
    (hx0 : ∀ m : Cell, m.1 ≤ x0 → f m = 0)
    (hxw : ∀ m : Cell, x0 + w < m.1 → f m = 0)
    (hy0 : ∀ m : Cell, m.2 ≤ y0 → f m = 0)
    (hclosed : ∀ c : Cell, IsPrimal c → x0 ≤ c.1 → c.1 ≤ x0 + w → cdeg f c = 0)
    (hw : 0 ≤ w) (z : Cell) (hz : z.1 ≤ x0 ∨ x0 + w ≤ z.1) :
    leftPotential x0 y0 f z = 0 := by
  have hcorr : leftCorr x0 y0 f z.2 = 0 := Finset.sum_eq_zero fun k _ => by
    unfold leftDefect; split_ifs with hk <;> [exact hclosed _ hk le_rfl (by simpa using hw); rfl]
  unfold leftPotential
  rw [hcorr, add_zero]
  rcases hz with hz | hz
  · exact rowSum_of_le x0 f _ _ hz
  · rw [← rowSum_full_zero x0 y0 w f hx0 hxw hy0 hclosed hw z.2]
    exact (Finset.sum_subset (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)
      fun a ha hna => by simp only [Finset.mem_Icc] at ha hna; exact hxw _ (by dsimp; omega)).symm

end PottsDiscontinuity.TorusCrossing
