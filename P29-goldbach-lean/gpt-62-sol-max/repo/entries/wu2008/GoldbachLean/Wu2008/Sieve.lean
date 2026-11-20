module

public import Mathlib

/-!
# Sieve counts S(A_e; P(D), y)

Definitions shared by the Wu 2008 Lemma 2.2 development: `Sifted`, `S`, `PS`, as in
LeanLab/ChenDoubleSieve/Lemma41.lean of the Lean Lab, unit U-5400. AI wrote the Lean code.
-/

open Finset

@[expose] public noncomputable section
open scoped Classical

namespace GoldbachLean.Wu2008.WuSieve

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`. -/
def Sifted (D : ℕ) (y : ℝ) (a : ℕ) :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < y → ¬ q ∣ D → ¬ q ∣ a

/-- `S(A_e; P(D), y)`. -/
def S (A : Finset ℕ) (e D : ℕ) (y : ℝ) :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
def PS (N : ℕ) (w z : ℝ) : Finset ℕ :=
  {p ∈ range ⌈z⌉₊ | p.Prime ∧ w ≤ p ∧ (p : ℝ) < z ∧ p.Coprime N}

/-- For coprime members the sifted condition is a lower bound on every prime factor. -/
lemma sifted_coprime {N a : ℕ} {z : ℝ} (ha : a ≠ 0) (hc : a.Coprime N) :
    Sifted N z a ↔ ∀ ⦃p⦄, p ∈ a.primeFactors → z ≤ (p : ℝ) := by
  grind [Sifted, Nat.Prime.coprime_iff_not_dvd, → Nat.Coprime.coprime_dvd_left]

end GoldbachLean.Wu2008.WuSieve
