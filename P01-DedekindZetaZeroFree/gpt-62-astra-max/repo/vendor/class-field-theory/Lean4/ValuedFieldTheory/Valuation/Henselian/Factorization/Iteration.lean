module

public import ValuedFieldTheory.Valuation.Henselian.Factorization.Step

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# recursive Hensel iterates

This file records the recursive polynomial iterates used in the proof
of Hensel's lemma and the coefficientwise adic estimates needed for the later
completion argument.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the recursive polynomial sequence
`F_{n+1}=F_n+π^(n+1)c_{n+1}` used for either factor in Hensel's iteration. -/
def henselFactorization_henselIterate {R : Type*} [CommRing R]
    (π : R) (F0 : R[X]) (corr : ℕ → R[X]) : ℕ → R[X]
  | 0 => F0
  | n + 1 =>
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * corr (n + 1)

section

variable {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X])

@[simp]
theorem henselFactorization_henselIterate_zero :
    henselFactorization_henselIterate π F0 corr 0 = F0 :=
  rfl

@[simp]
theorem henselFactorization_henselIterate_succ
    (n : ℕ) :
    henselFactorization_henselIterate π F0 corr (n + 1) =
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * corr (n + 1) :=
  rfl

end

section

variable {R : Type*} [CommRing R] {π : R}

/-- every recursive iterate is congruent to its initial lift
modulo `(π)`.  This is built into the update formula and does not require
`(π)` to be the maximal ideal. -/
theorem henselFactorization_henselIterate_span_singleton
    (F0 : R[X]) (corr : ℕ → R[X]) :
    ∀ n i : ℕ,
      (henselFactorization_henselIterate π F0 corr n - F0).coeff i ∈
        Ideal.span ({π} : Set R) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      intro i
      simpa using
        (henselFactorization_update_preserves_span_singleton

          (Nat.succ_pos n) ih i)

/-- if the initial polynomial and all correction polynomials
have degree at most `M`, then every recursive iterate has degree at most
`M`. -/
theorem henselFactorization_henselIterate_natDegree_le {F0 : R[X]} {corr : ℕ → R[X]} {M : ℕ}
    (hF0 : F0.natDegree ≤ M)
    (hcorr : ∀ n : ℕ, (corr n).natDegree ≤ M) :
    ∀ n : ℕ, (henselFactorization_henselIterate π F0 corr n).natDegree ≤ M := by
  intro n
  induction n with
  | zero =>
      exact hF0
  | succ n ih =>
      exact Polynomial.natDegree_add_le_of_degree_le ih ((Polynomial.natDegree_C_mul_le (π ^ (n + 1)) (corr (n + 1))).trans
        (hcorr (n + 1)))

/-- an iterate only depends on the correction coefficients up
to its own index. -/
theorem henselFactorization_henselIterate_eq_of_corr_eq_le {F0 : R[X]}
    {corr corr' : ℕ → R[X]} :
    ∀ n : ℕ,
      (∀ k : ℕ, k ≤ n → corr k = corr' k) →
        henselFactorization_henselIterate π F0 corr n =
          henselFactorization_henselIterate π F0 corr' n := by
  intro n hcorr
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [henselFactorization_henselIterate_succ,
        henselFactorization_henselIterate_succ]
      grind

end

section

variable {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X])

/-- changing a correction coefficient at a later index does
not change an earlier Hensel iterate. -/
theorem henselFactorization_henselIterate_update_of_lt {n k : ℕ} (c : R[X]) (h : n < k) :
    henselFactorization_henselIterate π F0 (Function.update corr k c) n =
      henselFactorization_henselIterate π F0 corr n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [henselFactorization_henselIterate_succ,
        henselFactorization_henselIterate_succ]
      grind

/-- extending the correction sequence at the next index gives
the expected next Hensel iterate. -/
theorem henselFactorization_henselIterate_update_next (n : ℕ) (c : R[X]) :
    henselFactorization_henselIterate π F0
        (Function.update corr (n + 1) c) (n + 1) =
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * c := by
  simp [henselFactorization_henselIterate_succ, henselFactorization_henselIterate_update_of_lt, Function.update_self]

end

/-- updating the correction functions at `n+1` preserves all
factorization invariants already established up to stage `n`. -/
theorem henselFactorization_henselIterate_update_preserves_factor_of_le
    {R : Type*} [CommRing R] {π : R}
    {f g0 h0 : R[X]} (pCorr qCorr : ℕ → R[X])
    {n r : ℕ} (hr : r ≤ n) (p q fn : R[X])
    (hfactor :
      f - henselFactorization_henselIterate π g0 pCorr r *
          henselFactorization_henselIterate π h0 qCorr r =
        Polynomial.C (π ^ (r + 1)) * fn) :
    f - henselFactorization_henselIterate π g0
          (Function.update pCorr (n + 1) p) r *
        henselFactorization_henselIterate π h0
          (Function.update qCorr (n + 1) q) r =
      Polynomial.C (π ^ (r + 1)) * fn := by
  simp_all [henselFactorization_henselIterate_update_of_lt]

/-- the one-step factorization statement rewritten in terms
of the updated Hensel iterates. -/
theorem henselFactorization_henselIterate_update_next_factor
    {R : Type*} [CommRing R] {π : R}
    {f g0 h0 : R[X]} (pCorr qCorr : ℕ → R[X])
    (n : ℕ) (p q fnNext : R[X])
    (hfactorNext :
      f - (henselFactorization_henselIterate π g0 pCorr n +
            Polynomial.C (π ^ (n + 1)) * p) *
          (henselFactorization_henselIterate π h0 qCorr n +
            Polynomial.C (π ^ (n + 1)) * q) =
        Polynomial.C (π ^ (n + 2)) * fnNext) :
    f - henselFactorization_henselIterate π g0
          (Function.update pCorr (n + 1) p) (n + 1) *
        henselFactorization_henselIterate π h0
          (Function.update qCorr (n + 1) q) (n + 1) =
      Polynomial.C (π ^ (n + 2)) * fnNext := by
  rw [henselFactorization_henselIterate_update_next
         ,
    henselFactorization_henselIterate_update_next
         ]
  exact hfactorNext

/-- a global correction-degree bound is preserved when one
correction coefficient is replaced by another coefficient satisfying the same
bound. -/
theorem henselFactorization_update_corr_natDegree_le
    {R : Type*} [CommRing R] {corr : ℕ → R[X]} {k M : ℕ} {c : R[X]}
    (hcorr : ∀ r : ℕ, (corr r).natDegree ≤ M)
    (hc : c.natDegree ≤ M) :
    ∀ r : ℕ, ((Function.update corr k c) r).natDegree ≤ M := by
  grind

/-- the increment from step `n` to step `n+1` is exactly the
chosen `π^(n+1)`-multiple. -/
theorem henselFactorization_henselIterate_succ_sub_eq
    {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X])
    (n : ℕ) :
    henselFactorization_henselIterate π F0 corr (n + 1) -
        henselFactorization_henselIterate π F0 corr n =
      Polynomial.C (π ^ (n + 1)) * corr (n + 1) := by
  simp

/-- coefficient form of the increment estimate in the
principal ideal `(π^(n+1))`. -/
theorem henselFactorization_henselIterate_succ_sub_coeff_mem_span_singleton_pow
    {R : Type*} [CommRing R] {π : R} (F0 : R[X]) (corr : ℕ → R[X])
    (n i : ℕ) :
    (henselFactorization_henselIterate π F0 corr (n + 1) -
        henselFactorization_henselIterate π F0 corr n).coeff i ∈
      Ideal.span ({π ^ (n + 1)} : Set R) := by
  rw [henselFactorization_henselIterate_succ_sub_eq, Polynomial.coeff_C_mul]
  refine Ideal.mem_span_singleton'.mpr ⟨(corr (n + 1)).coeff i, ?_⟩
  ring

/-- coefficient form of the increment estimate in the
`(n+1)`-st power of the principal ideal `(π)`. -/
theorem henselFactorization_henselIterate_succ_sub_coeff_mem_span_pow
    {R : Type*} [CommRing R] {π : R} (F0 : R[X]) (corr : ℕ → R[X])
    (n i : ℕ) :
    (henselFactorization_henselIterate π F0 corr (n + 1) -
        henselFactorization_henselIterate π F0 corr n).coeff i ∈
      Ideal.span ({π} : Set R) ^ (n + 1) := by
  rw [Ideal.span_singleton_pow]
  grind [henselFactorization_henselIterate_succ_sub_coeff_mem_span_singleton_pow]

/-- Cauchy-control estimate for two iterates in the
principal-ideal filtration generated by `π`. -/
theorem henselFactorization_henselIterate_sub_coeff_mem_span_pow_of_le
    {R : Type*} [CommRing R] {π : R}
    (F0 : R[X]) (corr : ℕ → R[X]) :
    ∀ {m n : ℕ}, m ≤ n → ∀ i : ℕ,
      (henselFactorization_henselIterate π F0 corr n -
          henselFactorization_henselIterate π F0 corr m).coeff i ∈
        Ideal.span ({π} : Set R) ^ (m + 1) := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
      simp [(Nat.eq_zero_of_le_zero hmn)]
  | succ n ih =>
      intro i
      by_cases hm : m = n + 1
      · simp [hm]
      · have hmle := Nat.lt_succ_iff.mp (lt_of_le_of_ne hmn hm)
        have hsplit :
            henselFactorization_henselIterate π F0 corr (n + 1) -
                henselFactorization_henselIterate π F0 corr m =
              (henselFactorization_henselIterate π F0 corr n -
                  henselFactorization_henselIterate π F0 corr m) +
                (henselFactorization_henselIterate π F0 corr (n + 1) -
                  henselFactorization_henselIterate π F0 corr n) := by
          ring
        rw [hsplit, Polynomial.coeff_add]
        exact Ideal.add_mem (Ideal.span {π} ^ (m + 1)) (ih hmle i) (Ideal.pow_le_pow_right (Nat.succ_le_succ hmle) (henselFactorization_henselIterate_succ_sub_coeff_mem_span_pow F0 corr n i))

end Valuations
end AlgebraicNumberTheory

end
