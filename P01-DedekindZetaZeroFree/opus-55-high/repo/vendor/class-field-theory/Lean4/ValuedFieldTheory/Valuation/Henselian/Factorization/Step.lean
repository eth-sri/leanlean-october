module

public import ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
public import ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# one Hensel iteration step

This file packages the algebraic correction, degree truncation, and `π`-power
update into the single step used recursively in the proof of Hensel's
lemma.
-/


open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- Algebraic splitting of an update by a `π^n`-multiple around the initial
lift. -/
theorem henselFactorization_update_sub_eq_initial_error_add
    {R : Type*} [CommRing R] {π : R} {n : ℕ} {g g0 p : R[X]} :
    g + Polynomial.C (π ^ n) * p - g0 =
      (g - g0) + Polynomial.C (π ^ n) * p := by
  ring

/-- adding a `π^n`-multiple preserves congruence modulo
`(π)` once `n ≥ 1`.  This is the inductive congruence needed for the
displayed-factor one-step update. -/
theorem henselFactorization_update_preserves_span_singleton
    {R : Type*} [CommRing R] {π : R} {n : ℕ} (hn : 1 ≤ n)
    {g g0 p : R[X]}
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R)) :
    ∀ i : ℕ,
      (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
        Ideal.span ({π} : Set R) := by
  intro i
  rw [henselFactorization_update_sub_eq_initial_error_add, Polynomial.coeff_add]
  refine (Ideal.span ({π} : Set R)).add_mem (hg i) ?_
  rw [Polynomial.coeff_C_mul]
  exact henselFactorization_pow_mul_mem_span_singleton_of_pos
    (π := π) (x := p.coeff i) hn

/-- displayed-factor one recursive Hensel step from the division
data.  The congruence modulo `(π)` is produced from the displayed Bezout-error
factor, and the update needs only `π ∈ m`, not `m ≤ (π)`. -/
theorem henselFactorization_one_step_update_from_division_data_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] {π : R} {n : ℕ} (hn : 1 ≤ n)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 g h fn a b qdiv p e : R[X]} {m d : ℕ}
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R))
    (hh : ∀ i : ℕ, (h - h0).coeff i ∈ Ideal.span ({π} : Set R))
    (hgunit : IsUnit g0.leadingCoeff)
    (hg0nat : g0.natDegree = m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hdiv : b * fn = g0 * qdiv + p)
    (hfn : fn.natDegree ≤ d)
    (hh0 : h0.natDegree ≤ d - m)
    (hp : p.natDegree ≤ m)
    (hmd : m ≤ d) :
    (henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv)).natDegree ≤ d - m ∧
      (∀ i : ℕ,
        (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
          Ideal.span ({π} : Set R)) ∧
        (∀ i : ℕ,
          (h + Polynomial.C (π ^ n) *
              henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) - h0).coeff i ∈
            Ideal.span ({π} : Set R)) ∧
          (∀ i : ℕ,
            (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
              IsLocalRing.maximalIdeal R) ∧
            (∀ i : ℕ,
              (h + Polynomial.C (π ^ n) *
                  henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) - h0).coeff i ∈
                IsLocalRing.maximalIdeal R) ∧
              ∃ fnNext : R[X],
                f - (g + Polynomial.C (π ^ n) * p) *
                    (h + Polynomial.C (π ^ n) *
                      henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv)) =
                  Polynomial.C (π ^ (n + 1)) * fnNext := by
  rcases henselFactorization_correction_after_division_degree_truncation_span_singleton
      (π := π) hπmem hgunit hg0nat hbezFactor hdiv hfn hh0 hp hmd with
    ⟨hqdeg, hcorrInitial⟩
  have hcorrCurrent :
      ∀ i : ℕ,
        (g * henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) +
            h * p - fn).coeff i ∈ Ideal.span ({π} : Set R) :=
    henselFactorization_correction_congruence_replace_initial_factors_span_singleton
      (π := π) (g0 := g0) (h0 := h0) (g := g) (h := h)
      (fn := fn) (p := p)
      (q := henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv))
      hg hh hcorrInitial
  have hgNext :
      ∀ i : ℕ,
        (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_update_preserves_span_singleton (π := π) hn hg
  have hhNext :
      ∀ i : ℕ,
        (h + Polynomial.C (π ^ n) *
            henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv) - h0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_update_preserves_span_singleton (π := π) hn hh
  have hspan_le :
      Ideal.span ({π} : Set R) ≤ IsLocalRing.maximalIdeal R :=
    henselFactorization_span_singleton_le_ideal_of_mem
      (IsLocalRing.maximalIdeal R) hπmem
  refine ⟨hqdeg, hgNext, hhNext, ?_, ?_, ?_⟩
  · intro i
    exact hspan_le (hgNext i)
  · intro i
    exact hspan_le (hhNext i)
  · exact henselFactorization_power_update_error_factor_exists
      (π := π) hn hfactor hcorrCurrent

/-- existence of one recursive Hensel step from the current
error factor in the displayed-factor principal-element form.  The chosen `π`
only has to lie in the maximal ideal; the needed congruence modulo `(π)` is
carried as an invariant and is produced from the displayed finite-minimum
Bezout-error factor. -/
theorem henselFactorization_exists_one_step_update_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} {n : ℕ} (hn : 1 ≤ n) (hπn : π ^ n ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 g h fn a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R))
    (hh : ∀ i : ℕ, (h - h0).coeff i ∈ Ideal.span ({π} : Set R))
    (hgdeg : g.natDegree ≤ m)
    (hhdeg : h.natDegree ≤ d - m)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0 : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hmd : m ≤ d) :
    ∃ p q fnNext : R[X],
      p.natDegree ≤ m ∧ q.natDegree ≤ d - m ∧
        (∀ i : ℕ,
          (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
            Ideal.span ({π} : Set R)) ∧
          (∀ i : ℕ,
            (h + Polynomial.C (π ^ n) * q - h0).coeff i ∈
              Ideal.span ({π} : Set R)) ∧
            (∀ i : ℕ,
              (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
                IsLocalRing.maximalIdeal R) ∧
              (∀ i : ℕ,
                (h + Polynomial.C (π ^ n) * q - h0).coeff i ∈
                  IsLocalRing.maximalIdeal R) ∧
                f - (g + Polynomial.C (π ^ n) * p) *
                    (h + Polynomial.C (π ^ n) * q) =
                  Polynomial.C (π ^ (n + 1)) * fnNext := by
  have hdegree : g0.natDegree = gbar.natDegree := by
    omega
  rcases henselFactorization_division_by_lifted_factor_degree_lt
      (g0 := g0) (gbar := gbar) hg0map hdegree hglead (b * fn) with
    ⟨qdiv, p, hdiv, hpdeg⟩
  have hpNat : p.natDegree ≤ m :=
    henselFactorization_remainder_natDegree_le_of_degree_lt
      (R := R) (g0 := g0) (p := p) hg0nat hpdeg
  have hgunit : IsUnit g0.leadingCoeff :=
    henselFactorization_lift_leadingCoeff_isUnit_of_natDegree_eq
      hg0map hdegree hglead
  have hfn : fn.natDegree ≤ d :=
    henselFactorization_error_factor_natDegree_le
      (π := π) hπn hf hgdeg hhdeg hmd hfactor
  rcases henselFactorization_one_step_update_from_division_data_of_mem_span
      (π := π) hn hπmem hfactor hg hh hgunit hg0nat
      hbezFactor hdiv hfn hh0 hpNat hmd with
    ⟨hqdeg, hgNext, hhNext, hgNextMax, hhNextMax, hnext⟩
  rcases hnext with ⟨fnNext, hfactorNext⟩
  exact ⟨p, henselFactorization_lowPart (d - m) (a * fn + h0 * qdiv), fnNext,
    hpNat, hqdeg, hgNext, hhNext, hgNextMax, hhNextMax, hfactorNext⟩

/-- displayed-factor one-step existence with the degree
invariants for the next approximants included. -/
theorem henselFactorization_exists_one_step_update_with_degree_bounds_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} {n : ℕ} (hn : 1 ≤ n) (hπn : π ^ n ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 g h fn a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg : ∀ i : ℕ, (g - g0).coeff i ∈ Ideal.span ({π} : Set R))
    (hh : ∀ i : ℕ, (h - h0).coeff i ∈ Ideal.span ({π} : Set R))
    (hgdeg : g.natDegree ≤ m)
    (hhdeg : h.natDegree ≤ d - m)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0 : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn)
    (hmd : m ≤ d) :
    ∃ p q fnNext : R[X],
      p.natDegree ≤ m ∧ q.natDegree ≤ d - m ∧
        (g + Polynomial.C (π ^ n) * p).natDegree ≤ m ∧
          (h + Polynomial.C (π ^ n) * q).natDegree ≤ d - m ∧
            (∀ i : ℕ,
              (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
                Ideal.span ({π} : Set R)) ∧
              (∀ i : ℕ,
                (h + Polynomial.C (π ^ n) * q - h0).coeff i ∈
                  Ideal.span ({π} : Set R)) ∧
                (∀ i : ℕ,
                  (g + Polynomial.C (π ^ n) * p - g0).coeff i ∈
                    IsLocalRing.maximalIdeal R) ∧
                  (∀ i : ℕ,
                    (h + Polynomial.C (π ^ n) * q - h0).coeff i ∈
                      IsLocalRing.maximalIdeal R) ∧
                    f - (g + Polynomial.C (π ^ n) * p) *
                        (h + Polynomial.C (π ^ n) * q) =
                      Polynomial.C (π ^ (n + 1)) * fnNext := by
  rcases henselFactorization_exists_one_step_update_of_mem_span
      (π := π) hn hπn hπmem hf hg hh hgdeg hhdeg
      hg0map hg0nat hgbar_nat hglead hh0 hbezFactor hfactor hmd with
    ⟨p, q, fnNext, hpdeg, hqdeg, hgNext, hhNext,
      hgNextMax, hhNextMax, hfactorNext⟩
  have hgNextDeg :
      (g + Polynomial.C (π ^ n) * p).natDegree ≤ m := by
    have hterm : (Polynomial.C (π ^ n) * p).natDegree ≤ m :=
      (Polynomial.natDegree_C_mul_le (π ^ n) p).trans hpdeg
    exact Polynomial.natDegree_add_le_of_degree_le hgdeg hterm
  have hhNextDeg :
      (h + Polynomial.C (π ^ n) * q).natDegree ≤ d - m := by
    have hterm : (Polynomial.C (π ^ n) * q).natDegree ≤ d - m :=
      (Polynomial.natDegree_C_mul_le (π ^ n) q).trans hqdeg
    exact Polynomial.natDegree_add_le_of_degree_le hhdeg hterm
  exact ⟨p, q, fnNext, hpdeg, hqdeg, hgNextDeg, hhNextDeg,
    hgNext, hhNext, hgNextMax, hhNextMax, hfactorNext⟩
