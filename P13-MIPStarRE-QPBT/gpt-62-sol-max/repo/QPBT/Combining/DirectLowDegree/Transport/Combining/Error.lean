module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Parameters
public import QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# The scalar error of the simultaneity reduction

`prop:ld-simultaneous-general-k` produces the three consistency relations of
`lem:ld-soundness` with the error of `thm:main-formal` at the combined
parameters of `def:ld-combining-parameters`, at the pass bound `30 ε`, together
with the recovery loss `(m + k) d / q` of `lem:ld-combining-recovery`.  This
module absorbs that error into the error function `deltaLd` of
`lem:ld-soundness` at the original parameters `(q, m, d, k)`.

The absorption is the estimate

  `mainFormalError (q, m + k, d) (2560000 (m + k)³ d) (30 ε) + (m + k) d / q`
  `  ≤ deltaLd a b ε q m d k`

for `0 < ε ≤ 1`, with the universal constants `a = 10^23` and `b = 1/80000`.
The exponent is the transport exponent of `exists_directLdTransportConstants`,
half the exponent `1/40000` carried by `mainFormalError`; the constant is
obtained from the prefactor `655360000000000000 (m + k)^{10} d²` of the error
of `thm:main-formal` at the combined parameters, the factor `30 d` by which the three envelope
terms of that error exceed the corresponding terms of `deltaLd`, and the bound
`m + k ≤ 2 d m k`.

## Main results

* `exists_directCombinedTransportConstants` — the absorption, with the explicit
  universal constants `a = 10^23` and `b = 1/80000`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:693-722`
* `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-! ## The error of `thm:main-formal` at the combined parameters -/

section

variable (D : DirectLdParams) {ε : ℝ}
    (hε0 : 0 < ε)
include D ε hε0

/-- The combined main-test error uses the same prefactor and noise terms,
with linear dimension `m + k` and test error `30 ε`. -/
private theorem mainFormalError_combined_le (hε1 : ε ≤ 1) :
    Test.mainFormalError D.combined.toLDTParameters
        (directLdAuxParameter D.combined) (3 * (10 * ε)) ≤
      19660800000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ (10 : ℕ)) * ((D.d : ℝ) ^ (3 : ℕ)) *
        transportEnvelope D ε := by
  have hd : (1 : ℝ) ≤ D.d := by exact_mod_cast D.hd
  have hq : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  have h1 : (3 * (10 * ε)) ^ (1 / 40000 : ℝ) ≤ 30 * ε ^ (1 / 80000 : ℝ) := by
    rw [show 3 * (10 * ε) = 30 * ε by ring]
    exact (transport_rpow_mul_le (by norm_num) hε0.le (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)) (by norm_num))
  have h2 := transport_rpow_ratio_le hd hq (by norm_num : (1 / 80000 : ℝ) ≤ 1 / 40000) (by norm_num)
  have h3 : Real.exp (-((D.combined.m : ℝ) * D.combined.d)) ≤
      (2 : ℝ) ^ (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
    push_cast
    apply transport_exp_le (by positivity) _ (by norm_num) (by norm_num)
    gcongr
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hNoise : directLdNoise D.combined (3 * (10 * ε)) ≤ 30 * (D.d : ℝ) * transportEnvelope D ε := by
    simp only [directLdNoise, transportEnvelope, Real.rpow_eq_pow]
    have hx := Real.rpow_nonneg hε0.le (1 / 80000 : ℝ)
    have hy := Real.rpow_nonneg (Nat.cast_nonneg D.q : 0 ≤ (D.q : ℝ)) (-(1 / 80000))
    have hz := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))
    change (3 * (10 * ε)) ^ (1 / 40000 : ℝ) + ((D.d : ℝ) / D.q) ^ (1 / 40000 : ℝ) +
      Real.exp (-((D.combined.m : ℝ) * D.combined.d)) ≤ _
    nlinarith
  rw [mainFormalError_direct_eq]
  refine (mul_le_mul_of_nonneg_left hNoise (by positivity)).trans_eq ?_
  unfold directLdPrefactor
  change 655360000000000000 * (((D.m + D.k : ℕ) : ℝ) ^ 10) * ((D.d : ℝ) ^ 2) * _ = _
  ring

private theorem directCombinedRecoveryLoss_le :
    ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) ≤
      ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ) * transportEnvelope D ε := by
  let M := ((D.m + D.k : ℕ) : ℝ) * (D.d : ℝ)
  have hM : 1 ≤ M := by
    have h : 1 ≤ (D.m + D.k) * D.d := Nat.mul_pos (by have := D.hm; omega) D.hd
    dsimp only [M]
    exact_mod_cast h
  have hq : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  rw [Nat.cast_mul]
  change M / D.q ≤ M * transportEnvelope D ε
  calc _ ≤ M * (D.q : ℝ) ^ (-(1 / 80000 : ℝ)) := by
        simpa only [Real.rpow_one] using
          transport_rpow_ratio_le hM hq (by norm_num : (1 / 80000 : ℝ) ≤ 1) le_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (transportEnvelope_rpow_q_le D hε0.le)
      (zero_le_one.trans hM)

end

/-! ## Absorption into the error function of `lem:ld-soundness` -/

/-- Absorption of the error of `prop:ld-simultaneous-general-k` into the error
function of `lem:ld-soundness`.

The explicit universal constants `a = 10^23` and `b = 1/80000` satisfy the side
conditions of `lem:ld-soundness` and absorb the error of `thm:main-formal` at
the combined parameters of `def:ld-combining-parameters`, at the pass bound
`30 ε`, together with the recovery loss `(m + k) d / q` of
`lem:ld-combining-recovery`, into `deltaLd a b ε q m d k` in the nontrivial
regime `0 < ε ≤ 1`.  Blueprint `ch13_qpbt_test.tex:693-722`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem exists_directCombinedTransportConstants :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) ≤
          deltaLd a b ε D.q D.m D.d D.k := by
  refine ⟨100000000000000000000000, 1 / 80000, by norm_num, by norm_num, by norm_num, ?_⟩
  intro D ε hε0 hε1
  let a : ℝ := 100000000000000000000000
  let M := ((D.m + D.k : ℕ) : ℝ)
  let N := ((D.d * D.m * D.k : ℕ) : ℝ)
  let E := transportEnvelope D ε
  have hm : (1 : ℝ) ≤ D.m := by exact_mod_cast D.hm
  have hd : (1 : ℝ) ≤ D.d := by exact_mod_cast D.hd
  have hk : (1 : ℝ) ≤ D.k := by exact_mod_cast D.hk
  have hM : 1 ≤ M := by dsimp only [M]; exact_mod_cast (show 1 ≤ D.m + D.k by have := D.hm; omega)
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 1 ≤ D.d * D.m * D.k from Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hE : 0 ≤ E := transportEnvelope_nonneg D hε0.le
  have hdN : (D.d : ℝ) ≤ N := by
    dsimp only [N]; push_cast
    exact le_mul_of_one_le_right (by positivity) hm |>.trans
      (le_mul_of_one_le_right (by positivity) hk)
  have hMN : M ≤ 2 * N := by
    dsimp only [M, N]; push_cast
    calc _ ≤ 2 * ((D.m : ℝ) * D.k) := by nlinarith
      _ ≤ _ := by
        rw [mul_assoc (D.d : ℝ)]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hd) (by norm_num)
  have hpoly : M ^ 10 * (D.d : ℝ) ^ 3 ≤ 1024 * N ^ 13 := by
    calc _ ≤ (2 * N) ^ 10 * N ^ 3 := by gcongr
      _ = _ := by ring
  have hlinear : M * (D.d : ℝ) ≤ M ^ 10 * (D.d : ℝ) ^ 3 := by
    gcongr
    · simpa using pow_le_pow_right₀ hM (by decide : 1 ≤ 10)
    · simpa using pow_le_pow_right₀ hd (by decide : 1 ≤ 3)
  have hpow : N ^ (13 : ℕ) ≤ N ^ a := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num [a])
  change _ ≤ a * N ^ a * E
  calc _ ≤ 19660800000000000000 * M ^ 10 * (D.d : ℝ) ^ 3 * E + M * (D.d : ℝ) * E :=
        add_le_add (mainFormalError_combined_le D hε0 hε1) (directCombinedRecoveryLoss_le D hε0)
    _ ≤ 19660800000000000001 * (M ^ 10 * (D.d : ℝ) ^ 3) * E := by
      linarith only [mul_le_mul_of_nonneg_right hlinear hE]
    _ ≤ 19660800000000000001 * (1024 * N ^ a) * E := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hpoly.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))) (by norm_num)) hE
    _ = (19660800000000000001 * 1024) * N ^ a * E := by ring
    _ ≤ _ := by gcongr; norm_num [a]

end MIPStarRE.QPBT
