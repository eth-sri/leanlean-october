/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics

/-! Instead of multiplying matrices over a polynomial ring, evaluate Strassen's
rank-seven identity in trilinear form.  Each recursive call returns one integer. -/
@[expose] public section
namespace Light.Sec3.Trace
open Finset
abbrev Mat := ℕ → ℕ → ℤ

def tri (n : ℕ) (A B C : Mat) := ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, A i k * B j k * C i j

structure Mix where
  (a b : Fin 4)
  (s : ℤ)
  deriving DecidableEq

structure Row where
  (a b c : Mix)
  deriving DecidableEq

/-- Quadrants are numbered row-major from zero.  In the second operand the
columns are the inner dimension, so its two off-diagonal quadrants are swapped. -/
def rows : List Row := [
  ⟨⟨0,3,1⟩, ⟨0,3,1⟩, ⟨0,3,1⟩⟩,
  ⟨⟨2,3,1⟩, ⟨0,0,0⟩, ⟨2,3,-1⟩⟩,
  ⟨⟨0,0,0⟩, ⟨2,3,-1⟩, ⟨1,3,1⟩⟩,
  ⟨⟨3,3,0⟩, ⟨1,0,-1⟩, ⟨0,2,1⟩⟩,
  ⟨⟨0,1,1⟩, ⟨3,3,0⟩, ⟨1,0,-1⟩⟩,
  ⟨⟨2,0,-1⟩, ⟨0,2,1⟩, ⟨3,3,0⟩⟩,
  ⟨⟨1,3,-1⟩, ⟨1,3,1⟩, ⟨0,0,0⟩⟩]

def quad (n : ℕ) (q : Fin 4) (A : Mat) : Mat := fun i j => A (i+q.val/2*n) (j+q.val%2*n)

def Mix.mat (m : Mix) (n : ℕ) (A : Mat) : Mat := fun i j => quad n m.a A i j + m.s * quad n m.b A i j

def Row.val (q : Row) (n : ℕ) (A B C : Mat) := tri n (q.a.mat n A) (q.b.mat n B) (q.c.mat n C)

theorem tri_split (n : ℕ) (A B C : Mat) : tri (n+n) A B C = (rows.map (·.val n A B C)).sum := by
  simp only [tri, sum_range_add, sum_add_distrib]
  simp only [rows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Row.val,tri,
    ← sum_add_distrib]
  iterate 3 apply sum_congr rfl; intros
  simp [Mix.mat, quad, Nat.add_comm n]; ring

theorem offs {i n : ℕ} (hi : i<n) (q : Fin 4) : i+q.val/2*n<n+n ∧ i+q.val%2*n<n+n := by
  have := q.isLt; have := Nat.mul_le_mul_right n (show q.val/2≤1 by omega)
  have := Nat.mul_le_mul_right n (show q.val%2≤1 by omega); omega

abbrev Bdd (n : ℕ) (A : Mat) (h : ℕ) := ∀ i < n, ∀ j < n, |A i j| ≤ (h:ℤ)

theorem bdd_mix {A : Mat} {n h : ℕ} (m : Mix) (hs : |m.s| ≤ 1) (hA : Bdd (n+n) A h) :
    Bdd n (m.mat n A) (2*h) := by
  intro i hi j hj
  have q (a : Fin 4) : |quad n a A i j| ≤ h := by
    exact hA _ (offs hi a).1 _ (offs hj a).2
  have := abs_add_le (quad n m.a A i j) (m.s * quad n m.b A i j)
  have := mul_le_mul hs (q m.b) (abs_nonneg _) (by norm_num)
  rw [one_mul, ← abs_mul] at this
  dsimp [Mix.mat]; have := q m.a; omega

theorem abs_tri {A B C : Mat} {n h : ℕ} (hA : Bdd n A h) (hB : Bdd n B h) (hC : Bdd n C h) :
    |tri n A B C| ≤ ((n*h : ℕ):ℤ)^3 := by
  have bound (f : ℕ → ℤ) (v : ℤ) (hf : ∀ i < n, |f i| ≤ v) : |∑ i ∈ range n, f i| ≤ n*v := by
    exact (Finset.abs_sum_le_sum_abs ..).trans (le_trans (sum_le_sum fun i hi => hf _ (mem_range.1 hi)) (by simp))
  unfold tri
  refine (bound _ _ fun i hi => bound _ _ fun j hj => bound _ ((h:ℤ)*h*h) fun k hk => ?_).trans ?_
  · rw [abs_mul, abs_mul]; exact mul_le_mul (mul_le_mul (hA _ hi _ hk) (hB _ hj _ hk) (by positivity) (by positivity)) (hC _ hi _ hj) (by positivity) (by positivity)
  · push_cast; exact le_of_eq (by ring)
end Light.Sec3.Trace
