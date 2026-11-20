module

public import ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# finite Hensel prefixes

This file isolates the reusable one-step extension in the finite
Hensel construction.  Compatible prefixes themselves are assembled once, as
HenselFactorizationFinitePrefixState, in the next layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- extend a finite Hensel prefix by one step in the
displayed-factor principal-element form.  The current iterates are automatically
congruent to the initial lifts modulo `(π)`, so the extension uses only
`π ∈ m` and the displayed Bezout-error factor. -/
theorem henselFactorization_extend_finite_prefix_one_step_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d n : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0 : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (pCorr qCorr : ℕ → R[X])
    (hprefix :
      ∀ r : ℕ, r ≤ n →
        ∃ fr : R[X],
          f - henselFactorization_henselIterate π g0 pCorr r *
              henselFactorization_henselIterate π h0 qCorr r =
            Polynomial.C (π ^ (r + 1)) * fr)
    {fn : R[X]}
    (hfactor :
      f - henselFactorization_henselIterate π g0 pCorr n *
          henselFactorization_henselIterate π h0 qCorr n =
        Polynomial.C (π ^ (n + 1)) * fn)
    (hgDeg : (henselFactorization_henselIterate π g0 pCorr n).natDegree ≤ m)
    (hhDeg : (henselFactorization_henselIterate π h0 qCorr n).natDegree ≤ d - m) :
    ∃ p q fnNext : R[X],
      p.natDegree ≤ m ∧ q.natDegree ≤ d - m ∧
        (∀ r : ℕ, r ≤ n →
          ∃ fr : R[X],
            f - henselFactorization_henselIterate π g0
                  (Function.update pCorr (n + 1) p) r *
                henselFactorization_henselIterate π h0
                  (Function.update qCorr (n + 1) q) r =
              Polynomial.C (π ^ (r + 1)) * fr) ∧
          f - henselFactorization_henselIterate π g0
                (Function.update pCorr (n + 1) p) (n + 1) *
              henselFactorization_henselIterate π h0
                (Function.update qCorr (n + 1) q) (n + 1) =
            Polynomial.C (π ^ (n + 2)) * fnNext ∧
            (henselFactorization_henselIterate π g0
                (Function.update pCorr (n + 1) p) (n + 1)).natDegree ≤ m ∧
              (henselFactorization_henselIterate π h0
                  (Function.update qCorr (n + 1) q) (n + 1)).natDegree ≤
                d - m ∧
                (∀ i : ℕ,
                  (henselFactorization_henselIterate π g0
                      (Function.update pCorr (n + 1) p) (n + 1) -
                    g0).coeff i ∈ IsLocalRing.maximalIdeal R) ∧
                  (∀ i : ℕ,
                    (henselFactorization_henselIterate π h0
                        (Function.update qCorr (n + 1) q) (n + 1) -
                      h0).coeff i ∈ IsLocalRing.maximalIdeal R) := by
  rcases henselFactorization_exists_one_step_update_with_degree_bounds_of_mem_span
        (Nat.succ_pos n) (pow_ne_zero (n + 1) hπne) hπmem

      hf (henselFactorization_henselIterate_span_singleton g0 pCorr n) (henselFactorization_henselIterate_span_singleton h0 qCorr n) hgDeg hhDeg hg0map hg0nat hgbar_nat hglead
      hh0 hbezFactor hfactor hmd with
    ⟨p, q, fnNext, hpDeg, hqDeg, hgNextDeg, hhNextDeg,
      _hgNextSpan, _hhNextSpan, hgNextRed, hhNextRed, hfactorNextRaw⟩
  refine ⟨p, q, fnNext, hpDeg, hqDeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r hr ↦ Exists.casesOn (hprefix r hr) fun fr hfr ↦ Exists.intro fr (henselFactorization_henselIterate_update_preserves_factor_of_le pCorr qCorr hr p q fr hfr)
  · apply henselFactorization_henselIterate_update_next_factor <;> assumption
  · rw [henselFactorization_henselIterate_update_next
          ]
    exact hgNextDeg
  · rw [henselFactorization_henselIterate_update_next
          ]
    exact hhNextDeg
  · intro i
    rw [henselFactorization_henselIterate_update_next
          ]
    exact hgNextRed i
  · intro i
    rw [henselFactorization_henselIterate_update_next
          ]
    exact hhNextRed i

end Valuations
end AlgebraicNumberTheory

end
