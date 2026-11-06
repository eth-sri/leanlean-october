/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import Mathlib

/-!
# Generator data, vectors in `ℕ⁴`, and normalized arithmetic

Write-up `PROOF_B_lean_writeup.md`, §1: Definitions 1–2 and Lemma 1.
-/

@[expose] public section

namespace SemigroupBetti

open Finset

/-- The generator vector `(m, m+a, m+b, m+w)`. -/
def gens (m a b w : ℕ) : Fin 4 → ℕ := ![m, m + a, m + b, m + w]

/-- **Definition 1.** Generator data with the standing hypotheses `(H)`. -/
structure GenData where
  m : ℕ
  a : ℕ
  b : ℕ
  w : ℕ
  m_pos : 0 < m
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_w : b < w
  gcd_eq_one : Nat.gcd m (Nat.gcd a (Nat.gcd b w)) = 1

/-- **Definition 2.** Support `{i : zᵢ > 0}`. -/
def supp (z : Fin 4 → ℕ) : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < z i)

/-- **Definition 2.** Two vectors share a variable. -/
def SharesVar (z z' : Fin 4 → ℕ) : Prop := ∃ i, 0 < z i ∧ 0 < z' i

instance : DecidableRel SharesVar := fun z z' =>
  inferInstanceAs (Decidable (∃ i, 0 < z i ∧ 0 < z' i))

@[simp] lemma mem_supp {z : Fin 4 → ℕ} {i : Fin 4} : i ∈ supp z ↔ 0 < z i := by
  simp [supp]

lemma SharesVar.symm {z z' : Fin 4 → ℕ} (h : SharesVar z z') : SharesVar z' z :=
  h.imp fun _ => And.symm

namespace GenData

variable (G : GenData)

/-- The generator vector `n = (m, m+a, m+b, m+w)`. -/
def n : Fin 4 → ℕ := gens G.m G.a G.b G.w

/-- `g = gcd(a, gcd(b, w))`. -/
def g : ℕ := Nat.gcd G.a (Nat.gcd G.b G.w)

/-- `A = a / g`. -/
def A : ℕ := G.a / G.g
/-- `B = b / g`. -/
def B : ℕ := G.b / G.g
/-- `W = w / g` (normalized width). -/
def W : ℕ := G.w / G.g

/-- **Definition 2.** Degree `ν(z) = ∑ zᵢ nᵢ`. -/
def nu (z : Fin 4 → ℕ) : ℕ := ∑ i, z i * G.n i

@[simp] lemma n_two : G.n 2 = G.m + G.b := rfl
@[simp] lemma n_three : G.n 3 = G.m + G.w := rfl

lemma nu_eq_sum (z : Fin 4 → ℕ) : G.nu z = z 0 * G.m + z 1 * (G.m + G.a) +
    z 2 * (G.m + G.b) + z 3 * (G.m + G.w) := by
  simp [nu, n, gens, Fin.sum_univ_four]

lemma m_le_n (i : Fin 4) : G.m ≤ G.n i := by fin_cases i <;> simp [n, gens]

lemma n_pos (i : Fin 4) : 0 < G.n i := lt_of_lt_of_le G.m_pos (G.m_le_n i)

lemma n_le_n_three (i : Fin 4) : G.n i ≤ G.n 3 := by
  have := G.a_lt_b; have := G.b_lt_w
  fin_cases i <;> simp [n, gens] <;> omega

/-! ### Additivity of `ν` -/

@[simp] lemma nu_zero : G.nu 0 = 0 := by simp [nu]

lemma nu_add (x y : Fin 4 → ℕ) : G.nu (x + y) = G.nu x + G.nu y := by
  simp [nu, add_mul, Finset.sum_add_distrib]

lemma nu_single (i : Fin 4) (k : ℕ) : G.nu (Pi.single i k) = k * G.n i := by
  simp [nu, Pi.single_apply]

/-- If `x ≤ y` coordinatewise then `ν(y) = ν(x) + ν(y - x)`. -/
lemma nu_sub {x y : Fin 4 → ℕ} (h : x ≤ y) : G.nu y = G.nu x + G.nu (y - x) := by
  rw [← nu_add]; congr 1; ext i; simp only [Pi.add_apply, Pi.sub_apply]
  exact (Nat.add_sub_of_le (h i)).symm

lemma single_le_nu (z : Fin 4 → ℕ) (i : Fin 4) : z i * G.n i ≤ G.nu z :=
  Finset.single_le_sum (f := fun j => z j * G.n j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

lemma nu_pos_of_pos {z : Fin 4 → ℕ} {i : Fin 4} (h : 0 < z i) : 0 < G.nu z :=
  lt_of_lt_of_le (Nat.mul_pos h (G.n_pos i)) (G.single_le_nu z i)

lemma nu_eq_zero_iff {z : Fin 4 → ℕ} : G.nu z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  ext i; simp only [Pi.zero_apply]
  by_contra hi
  have := G.nu_pos_of_pos (z := z) (i := i) (Nat.pos_of_ne_zero hi)
  omega

/-! ### Lemma 1: normalized arithmetic -/

lemma g_dvd_a : G.g ∣ G.a := Nat.gcd_dvd_left _ _
lemma g_dvd_b : G.g ∣ G.b := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
lemma g_dvd_w : G.g ∣ G.w := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

lemma a_eq : G.a = G.g * G.A := (Nat.mul_div_cancel' G.g_dvd_a).symm
lemma b_eq : G.b = G.g * G.B := (Nat.mul_div_cancel' G.g_dvd_b).symm
lemma w_eq : G.w = G.g * G.W := (Nat.mul_div_cancel' G.g_dvd_w).symm

lemma A_pos : 0 < G.A := Nat.pos_of_mul_pos_left (G.a_eq.symm ▸ G.a_pos)

lemma A_lt_B : G.A < G.B := Nat.lt_of_mul_lt_mul_left (by
  rw [← G.a_eq, ← G.b_eq]; exact G.a_lt_b)

lemma B_lt_W : G.B < G.W := Nat.lt_of_mul_lt_mul_left (by
  rw [← G.b_eq, ← G.w_eq]; exact G.b_lt_w)

lemma two_le_B : 2 ≤ G.B := by have := G.A_pos; have := G.A_lt_B; omega
lemma three_le_W : 3 ≤ G.W := by have := G.two_le_B; have := G.B_lt_W; omega
lemma two_le_W_sub_A : 2 ≤ G.W - G.A := by
  have := G.A_lt_B; have := G.B_lt_W; omega

lemma W_le_w : G.W ≤ G.w := Nat.div_le_self _ _

end GenData

end SemigroupBetti
