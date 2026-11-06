/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Plane.FiniteFieldConstants
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linarith

/-! Integer parameters for the Stepanov construction above the cutoff
`stepanovThreshold d = 27 * d ^ 4`. -/

public section
namespace CCDN

/-- The numerical dimension inequality of the Stepanov method: for `p > 27 d⁴`, `x ^ 2 ≤ p`,
`p ≤ y + d` and `N = x - 4 d² > 0`, one has `N (x + y + d + d² N) < (x - d²) (y - d²)`. -/
lemma stepanov_numeric_dimension (d p x y N : ℕ) (hd : 0 < d)
    (hp : stepanovThreshold d < p) (hx : x ^ 2 ≤ p) (hy : p ≤ y + d)
    (hN : N + 4 * d ^ 2 = x) (hNpos : 0 < N) :
    N * (x + y + d + d ^ 2 * N) < (x - d ^ 2) * (y - d ^ 2) := by
  unfold stepanovThreshold at hp
  let b := d ^ 2
  have hb : d ≤ b := by simpa only [b, pow_two] using Nat.le_mul_self d
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hp' : 27 * b ^ 2 < p := by dsimp [b]; nlinarith [hp]
  have hxb : b ≤ x := by omega
  have hyb : b ≤ y := by nlinarith
  have hxp : 5 * x ≤ p := by
    have hh : 5 ≤ x := by omega
    nlinarith [Nat.mul_le_mul_left x hh]
  have hNN : N ^ 2 ≤ p := by
    have hh : N ≤ x := by omega
    nlinarith [Nat.mul_self_le_mul_self hh]
  have hNx' : N * x ≤ p := by
    have hh : N ≤ x := by omega
    nlinarith [Nat.mul_le_mul_right x hh]
  have hNb : b * N ≤ b * x := Nat.mul_le_mul_left b (by omega)
  have hNd : d * N ≤ b * x := Nat.mul_le_mul hb (by omega)
  have h3y := Nat.mul_le_mul_left (3 * b) hy
  have h5bx := Nat.mul_le_mul_left (2 * b) hxp
  have hNp := Nat.mul_le_mul_left b hNN
  have hbd := Nat.mul_le_mul_left b hb
  have hbp : p ≤ b * p := by nlinarith [Nat.mul_le_mul_right p hbpos]
  have hsubx := Nat.sub_add_cancel hxb
  have hsuby := Nat.sub_add_cancel hyb
  have hv : N * (b + d + x + b * N) + 3 * b ^ 2 < 3 * b * y := by
    linarith
  have hi : (x - b) * (y - b) + N * (b + d + x + b * N) + 3 * b ^ 2 =
      N * (x + y + d + b * N) + 3 * b * y := by
    grind
  change N * (x + y + d + b * N) < (x - b) * (y - b)
  omega


/-- Concrete integer degrees: A=floor(sqrt(p)/d), D=floor((p-1)/d),
and N=d*A-4*d^2. The cutoff ensures a positive multiplicity. -/
theorem exists_stepanov_integer_parameters (d p : ℕ) (hd : 0 < d)
    (hp : stepanovThreshold d < p) :
    ∃ A D N : ℕ, d ≤ A ∧ d ≤ D ∧ d * D < p ∧ N ≤ p ∧
      N + 4 * d ^ 2 = d * A ∧ 0 < N ∧ (d * A) ^ 2 ≤ p ∧
      p ≤ d * D + d ∧ p < (d * A + d) ^ 2 := by
  unfold stepanovThreshold at hp
  let A := Nat.sqrt p / d
  let D := (p - 1) / d
  let x := d * A
  let y := d * D
  have hb : d ≤ d ^ 2 := by nlinarith
  have hbb : d ^ 2 ≤ (d ^ 2) ^ 2 := by nlinarith
  have hp' : 27 * (d ^ 2) ^ 2 < p := by nlinarith only [hp]
  have hs := Nat.mod_add_div (Nat.sqrt p) d
  have hsm := Nat.mod_lt (Nat.sqrt p) hd
  have hxs : x ≤ Nat.sqrt p := by dsimp only [x, A]; omega
  have hsx : Nat.sqrt p + 1 ≤ x + d := by dsimp only [x, A]; omega
  have hx := (Nat.pow_le_pow_left hxs 2).trans (Nat.sqrt_le' p)
  have hpx :=
    (Nat.lt_succ_sqrt' p).trans_le (Nat.pow_le_pow_left hsx 2)
  have hydiv := Nat.mod_add_div (p - 1) d
  have hymod := Nat.mod_lt (p - 1) hd
  have hyp : y < p := by dsimp only [y, D]; omega
  have hpy : p ≤ y + d := by dsimp only [y, D]; omega
  have hx4 : 4 * d ^ 2 < x := by
    nlinarith
  have hA : d ≤ A := by dsimp only [x] at hx4; nlinarith only [hx4, hd]
  have hD : d ≤ D := by
    have hdy : d ^ 2 ≤ y := by omega
    dsimp only [y] at hdy
    nlinarith only [hdy, hd]
  let N := x - 4 * d ^ 2
  have hNx := Nat.sub_add_cancel (Nat.le_of_lt hx4)
  have hNpos := Nat.sub_pos_of_lt hx4
  have hxx : x ≤ x ^ 2 := by simp_all [pow_two, Nat.le_mul_self]
  exact ⟨A, D, N, hA, hD, hyp, (by omega), hNx, hNpos, hx, hpy, hpx⟩

end CCDN
