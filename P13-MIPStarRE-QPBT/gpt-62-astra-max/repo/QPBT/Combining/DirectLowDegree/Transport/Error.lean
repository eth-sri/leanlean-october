module

public import QPBT.Combining.DirectLowDegree.Transport.Correspondence
public import QPBT.Games.DistanceTheorems.TensorSupport
public import MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.EnvelopeBounds

/-!
# The scalar error of the low-degree soundness transport

This module supplies the scalar half of the soundness transport for the
directly indexed low-degree game.  Its content is purely arithmetic: the
auxiliary sampling parameter with which the low individual degree theorem is
applied to a coordinate strategy, the resulting bounds on the three terms of
the LDT error `mainFormalError`, and the absorption of the
simultaneous-measurement estimate into the error function `deltaLd` of
`lem:ld-soundness`.

## Main definitions

* `directLdAuxParameter D = 2560000 m³ d` is the sampling parameter handed to
  `MIPStarRE.LDT.Test.mainFormal`.  It is the multiple of the exponential scale
  `2560000 m²` of `mainFormalError` with quotient `m d`, so that the
  exponential term of the LDT error is exactly `exp (-m d)`.

## Main results

* `directLdAuxParameter_pos` and `four_hundred_mul_le_directLdAuxParameter` are
  the two hypotheses `0 < k` and `400 m d ≤ k` of `mainFormal`, proved from the
  positivity of the dimension and of the degree alone.
* `directLd_test_term_le`, `directLd_field_term_le` and
  `directLd_exponential_term_le` bound the three terms of
  `mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 ε)`: the test
  term by `3 ε^(1/40000)`, the field term by `d q^(-1/40000)`, and the
  exponential term by `2^(-b m d)` for every `0 ≤ b ≤ 1`.
* `exists_directLdTransportConstants` exhibits, for a sandwich constant
  `C₀ ≥ 1`, the explicit universal constants `a = 2500000000 C₀` and
  `b = 1/80000` for which `C₀ k √(mainFormalError + m d / q + ε)` is at most
  `deltaLd a b ε q m d k` in the regime `0 < ε ≤ 1`.
* `one_le_deltaLd_of_one_le_error` and
  `one_le_deltaLd_of_fieldSize_le_degree` bound `deltaLd` below by one in the
  two degenerate regimes `1 ≤ ε` and `q ≤ d`, and
  `consistencyDefect_heteroKron_le_one` bounds every bipartite consistency
  defect on a unit state above by one.  Together they close both degenerate
  regimes, where the conclusion of `lem:ld-soundness` carries no information.

The exponent `b = 1/80000` is half the exponent `1/40000` carried by
`mainFormalError`; the halving is exactly what the square root of the
simultaneous-measurement estimate costs.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:139-167`
* `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:288-327`
* `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`
* `references/ldt-paper/test_definition.tex:180-202`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

/-! ## The auxiliary sampling parameter -/

section

variable (D : DirectLdParams)

/-- The auxiliary sampling parameter of the low-degree soundness transport.

The low individual degree theorem is applied to each coordinate strategy of
a directly indexed strategy with `k = 2560000 m³ d` samples.  This
is the multiple of the exponential scale `2560000 m²` of `mainFormalError`
whose quotient is `m d`, and it dominates the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal` uniformly in the
parameters.  Blueprint `ch13_qpbt_test.tex:139-167`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
def directLdAuxParameter : ℕ := 2560000 * D.m ^ 3 * D.d

/-! ## Elementary positivity of the parameters

The four lemmas below are formalization-only conveniences: they record the
positivity fields of `DirectLdParams` in the real numbers, where all the
scalar estimates of this module take place. -/

private theorem directLd_one_le_m : (1 : ℝ) ≤ (D.m : ℝ) := by
  exact_mod_cast D.hm

private theorem directLd_one_le_d : (1 : ℝ) ≤ (D.d : ℝ) := by
  exact_mod_cast D.hd

private theorem directLd_one_le_k : (1 : ℝ) ≤ (D.k : ℝ) := by
  exact_mod_cast D.hk

private theorem directLd_one_le_q : (1 : ℝ) ≤ (D.q : ℝ) := by
  exact_mod_cast D.toLDTParameters.hq

/-! ## The three terms of the LDT error -/

/-- With the auxiliary sampling parameter the exponential scale of
`mainFormalError` collapses: the argument of its exponential term is exactly
`m d`.

Formalization-only scalar identity for the error function displayed in
`MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`. -/
theorem directLdAuxParameter_exp_arg :
    (directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))) =
      (D.m : ℝ) * (D.d : ℝ) := by
  have hpow := pow_pos (lt_of_lt_of_le zero_lt_one (directLd_one_le_m D)) 2
  unfold directLdAuxParameter
  grind [ne_of_gt, mul_pos]

/-! ## The transport envelope

The three scalar quantities `ε^b`, `q^(-b)` and `2^(-b m d)` at the transport
exponent `b = 1/80000` are the inner factor of `deltaLd`; the abbreviation
below names their sum. -/

/-- The inner factor of `deltaLd` at the transport exponent `b = 1/80000`.
This is a formalization-only abbreviation, shared with the absorption of the
error of `prop:ld-simultaneous-general-k`. -/
noncomputable def transportEnvelope (ε : ℝ) : ℝ :=
  Real.rpow ε (1 / 80000) + Real.rpow (D.q : ℝ) (-(1 / 80000)) +
    Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))

theorem transportEnvelope_rpow_eps_le (ε : ℝ) :
    Real.rpow ε (1 / 80000) ≤ transportEnvelope D ε := by
  have hy : 0 ≤ Real.rpow D.q (-(1 / 80000)) :=
    Real.rpow_nonneg (by positivity) _
  have hz : 0 ≤ Real.rpow 2 (-((1 / 80000) * (D.m * D.d : ℕ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold transportEnvelope
  linarith

theorem transportEnvelope_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ transportEnvelope D ε := by
  exact le_trans (Real.rpow_nonneg hε _) (transportEnvelope_rpow_eps_le D ε)

/-! ## The LDT error at the auxiliary sampling parameter -/

/-- The LDT error at the auxiliary sampling parameter, written out in the
parameters of the directly indexed game. -/
private theorem mainFormalError_direct_eq (ε : ℝ) :
    Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) =
      100000 * ((directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)) *
        (Real.rpow (3 * ε) (1 / 40000) +
          Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
          Real.exp (-((directLdAuxParameter D : ℝ) /
            (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) := rfl

private theorem mainFormalError_direct_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) := by
  exact mul_nonneg (by positivity) ((by
                                      have h1 : _ ≤ Real.rpow (3 * _) (1 / 40000) := Real.rpow_nonneg (by linarith) _
                                      have h2 : _ ≤ Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) :=
                                        Real.rpow_nonneg (by positivity) _
                                      have h3 : _ ≤
                                          Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) :=
                                        (Real.exp_pos _).le
                                      linarith))

/-- The square root of the polynomial prefactor of the LDT error at the
auxiliary sampling parameter. -/
private theorem sqrt_directLdPrefactor_le :
    Real.sqrt (100000 * ((directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ))) ≤
      820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := by
  have hK : (directLdAuxParameter D : ℝ) = 2560000 * D.m ^ 3 * D.d := by
    unfold directLdAuxParameter
    push_cast
    ring
  have hX : 0 ≤ D.m ^ 10 * (D.d : ℝ) ^ 2 := by positivity
  have hC : 0 ≤ 820000000 * D.m ^ 5 * (D.d : ℝ) := by positivity
  have hlhs : 100000 * ((directLdAuxParameter D : ℝ) ^ 2) * (D.m ^ 4) =
      655360000000000000 * (D.m ^ 10 * D.d ^ 2) := by
    rw [hK]; ring
  have hrhs : (820000000 * D.m ^ 5 * D.d) ^ 2 =
      672400000000000000 * (D.m ^ 10 * (D.d : ℝ) ^ 2) := by ring
  rw [← Real.sqrt_sq hC]
  apply Real.sqrt_le_sqrt
  simp [hlhs]
  bound

/-- Halving the exponents: the square root of the LDT envelope at the
auxiliary sampling parameter is at most `3 d` times the transport envelope. -/
private theorem sqrt_directLdEnvelope_le {ε : ℝ} (hε0 : 0 < ε) :
    Real.sqrt (Real.rpow (3 * ε) (1 / 40000) +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
        Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) ≤
      3 * (D.d : ℝ) * transportEnvelope D ε := by
  have hd1 := directLd_one_le_d D
  have hb1 : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) ≤ 3 * Real.rpow ε (1 / 80000) := by
    have e : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) = Real.rpow (3 * ε) (1 / 80000) := by
      rw [Test.sqrt_rpow_one_div (by linarith : (0 : ℝ) ≤ 3 * ε)
        (by norm_num : (0 : ℝ) < 40000)]
      norm_num
    rw [e]
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by norm_num) hε0.le]
    have h3 : (3 : ℝ) ^ ((1 : ℝ) / 80000) ≤ 3 := by
      calc _ ≤ _ :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    bound
  have hb2 : Real.sqrt (Real.rpow (D.d / D.q) (1 / 40000)) ≤
      D.d * Real.rpow D.q (-(1 / 80000)) := by
    have e : Real.sqrt (Real.rpow (D.d / D.q) (1 / 40000)) =
        Real.rpow (D.d / D.q) (1 / 80000) := by
      rw [Test.sqrt_rpow_one_div (by positivity : (0 : ℝ) ≤ (D.d : ℝ) / (D.q : ℝ))
        (by norm_num : (0 : ℝ) < 40000)]
      norm_num
    rw [e]
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
    have hd : D.d ^ ((1 : ℝ) / 80000) ≤ (D.d : ℝ) := by
      calc _ ≤ _ :=
            Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
        _ = _ := Real.rpow_one _
    gcongr
  have hb3 : Real.sqrt
      (Real.exp (-((directLdAuxParameter D) / (2560000 * (D.m ^ 2))))) ≤
      Real.rpow 2 (-((1 / 80000) * (D.m * D.d : ℕ))) := by
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hmd : 0 ≤ D.m * (D.d : ℝ) := by positivity
    have hcast : (D.m * D.d : ℕ) = D.m * (D.d : ℝ) := by push_cast; ring
    rw [directLdAuxParameter_exp_arg, ← Real.exp_half, hcast]
    simp
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hmd]
  have hx := Real.rpow_nonneg hε0.le (1 / 80000)
  have hy := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (D.q : ℝ)) (-(1 / 80000))
  have hz := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    (-((1 / 80000) * (D.m * D.d : ℕ)))
  have p1 : 0 ≤ (D.d - 1) * Real.rpow ε (1 / 80000) :=
    mul_nonneg (by linarith) hx
  have p2 : 0 ≤ D.d * Real.rpow D.q (-(1 / 80000)) :=
    mul_nonneg (by linarith) hy
  have p3 : 0 ≤ (3 * D.d - 1) *
      Real.rpow 2 (-((1 / 80000) * (D.m * D.d : ℕ))) := mul_nonneg (by linarith) hz
  calc _
      ≤ Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) +
          Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) +
          Real.sqrt
            (Real.exp (-((directLdAuxParameter D : ℝ) /
              (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) :=
        MIPStarRE.LDT.sqrt_add3_le_add3_sqrt (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _) ((Real.exp_pos _).le)
    _ ≤ 3 * Real.rpow ε (1 / 80000) + D.d * Real.rpow D.q (-(1 / 80000)) +
          Real.rpow 2 (-((1 / 80000) * (D.m * D.d : ℕ))) := by
        linarith
    _ ≤ _ := by
        unfold transportEnvelope
        nlinarith [p1, p2, p3]

/-- The square root of the whole scalar error of the transport, bounded by an
explicit polynomial in the parameters times the transport envelope. -/
private theorem sqrt_directLdTransportError_le {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
      2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * transportEnvelope D ε := by
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hq1 := directLd_one_le_q D
  have hT := transportEnvelope_nonneg D hε0.le
  have hsE : Real.sqrt
      (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) ≤
      820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
        (3 * (D.d : ℝ) * transportEnvelope D ε) := by
    rw [mainFormalError_direct_eq, Real.sqrt_mul (by positivity)]
    exact mul_le_mul (sqrt_directLdPrefactor_le D) (sqrt_directLdEnvelope_le D hε0)
      (Real.sqrt_nonneg _) (by positivity)
  have hsmd : Real.sqrt (((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ)) ≤
      (D.m : ℝ) * (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    have hmd1 : (1 : ℝ) ≤ (D.m : ℝ) * (D.d : ℝ) := by nlinarith
    simp only [Real.rpow_eq_pow]
    rw [Real.sqrt_eq_rpow, Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
    have h1 : ((D.m : ℝ) * (D.d : ℝ)) ^ ((1 : ℝ) / 2) ≤ (D.m : ℝ) * (D.d : ℝ) := by
      calc _
          ≤ ((D.m : ℝ) * (D.d : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hmd1 (by norm_num)
        _ = _ := Real.rpow_one _
    have h2 : _ ^ (-((1 : ℝ) / 2)) ≤ (D.q : ℝ) ^ (-((1 : ℝ) / 80000)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    gcongr
  have hsε : Real.sqrt ε ≤ Real.rpow ε (1 / 80000) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  have hqT : (D.m : ℝ) * (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) ≤
      (D.m : ℝ) * (D.d : ℝ) * transportEnvelope D ε :=
    mul_le_mul_of_nonneg_left ((by
                                 have hx : _ ≤ Real.rpow _ (1 / 80000) := Real.rpow_nonneg hε0.le _
                                 have hz : _ ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
                                   Real.rpow_nonneg (by norm_num) _
                                 unfold transportEnvelope
                                 linarith)) (by positivity)
  have hεT : Real.rpow ε (1 / 80000) ≤ 1 * transportEnvelope D ε := by
    rw [one_mul]
    apply transportEnvelope_rpow_eps_le
  have hP : (D.m : ℝ) * (D.d : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by
    have e1 : (D.m : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) := by
      bound
    bound
  have hP1 : (1 : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hcoef : 2460000000 * ((D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) +
      (D.m : ℝ) * (D.d : ℝ) + 1 ≤
      2500000000 * ((D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by linarith
  calc _
      ≤ Real.sqrt
            (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)) +
          Real.sqrt (((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ)) + Real.sqrt ε :=
        MIPStarRE.LDT.sqrt_add3_le_add3_sqrt (mainFormalError_direct_nonneg D hε0.le) (by positivity) hε0.le
    _ ≤ 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
            (3 * (D.d : ℝ) * transportEnvelope D ε) +
          (D.m : ℝ) * (D.d : ℝ) * transportEnvelope D ε + 1 * transportEnvelope D ε := by
        linarith
    _ ≤ _ :=
        (by nlinarith [mul_le_mul_of_nonneg_right hcoef hT])

end

/-! ## Absorption into the error function of `lem:ld-soundness` -/

/-- Absorption of the simultaneous-measurement estimate into `deltaLd`.

For every universal constant `C₀ ≥ 1` of the sandwiched simultaneous
measurement estimate `consistencyDefect_sandwich_le`, the explicit universal
constants `a = 2500000000 C₀` and `b = 1/80000` satisfy the side conditions of
`lem:ld-soundness` and absorb

  `C₀ k √(mainFormalError (2560000 m³ d) (3 ε) + m d / q + ε)`

into `deltaLd a b ε q m d k` in the nontrivial regime `0 < ε ≤ 1`.  Blueprint
`ch13_qpbt_test.tex:139-167`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem direct_ld_transport_constants_explicit (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    1 ≤ 2500000000 * C₀ ∧ 0 < (1 / 80000 : ℝ) ∧ (1 / 80000 : ℝ) ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        C₀ * (D.k : ℝ) *
            Real.sqrt
              (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
          deltaLd (2500000000 * C₀) (1 / 80000) ε D.q D.m D.d D.k := by
  refine ⟨by linarith, by norm_num, by norm_num, ?_⟩
  intro D ε hε0 hε1
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hk1 := directLd_one_le_k D
  have hdelta : deltaLd (2500000000 * C₀) (1 / 80000) ε D.q D.m D.d D.k =
      2500000000 * C₀ * _ *
        transportEnvelope D ε := rfl
  have hbase : (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hpow : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by push_cast; linarith)
  calc _
      ≤ C₀ * (D.k : ℝ) *
          (2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) *
            transportEnvelope D ε) :=
        mul_le_mul_of_nonneg_left (sqrt_directLdTransportError_le D hε0 hε1) (mul_nonneg (by linarith) (by positivity))
    _ = 2500000000 * C₀ *
          ((D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) *
          transportEnvelope D ε := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (transportEnvelope_nonneg D hε0.le)
        exact mul_le_mul_of_nonneg_left (le_trans (by
          have e1 : (D.k : ℝ) ≤ (D.k : ℝ) ^ (8 : ℕ) := by
            bound
          have e2 : _ ^ (5 : ℕ) ≤ (D.m : ℝ) ^ (8 : ℕ) :=
            pow_le_pow_right₀ hm1 (by norm_num)
          have e3 : _ ^ (2 : ℕ) ≤ (D.d : ℝ) ^ (8 : ℕ) :=
            pow_le_pow_right₀ hd1 (by norm_num)
          push_cast
          calc _
              ≤ (D.k : ℝ) ^ (8 : ℕ) * (D.m : ℝ) ^ (8 : ℕ) * (D.d : ℝ) ^ (8 : ℕ) :=
                mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3
                  (by positivity) (by positivity)
            _ = _ := by ring) hpow) (by linarith)

/-! ## The degenerate regimes

In the two regimes `1 ≤ ε` and `q ≤ d` the error function `deltaLd` is at
least one, so the consistency conclusions of `lem:ld-soundness` hold for any
witnesses; the low-degree test carries no information there. -/

/-- In the regime `1 ≤ ε` the error function `deltaLd` is at least one.

Formalization-only scalar bound closing the trivial regime of
blueprint `lem:ld-soundness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
theorem one_le_deltaLd_of_one_le_error {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hε : 1 ≤ ε) {q m d k : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    1 ≤ deltaLd a b ε q m d k := by
  have hbase : (1 : ℝ) ≤ ((d * m * k : ℕ) : ℝ) := by
    bound
  have hX : (1 : ℝ) ≤ Real.rpow ((d * m * k : ℕ) : ℝ) a := by
    calc (1 : ℝ) = (1 : ℝ) ^ a := (Real.one_rpow a).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hY : (1 : ℝ) ≤ Real.rpow ε b := by
    calc (1 : ℝ) = (1 : ℝ) ^ b := (Real.one_rpow b).symm
      _ ≤ ε ^ b := Real.rpow_le_rpow (by norm_num) hε hb
  have hZ : _ ≤ Real.rpow (q : ℝ) (-b) := Real.rpow_nonneg (by positivity) _
  have hW : _ ≤ Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hax : (1 : ℝ) ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a := by nlinarith
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ _ :=
      mul_le_mul hax (by linarith) (by norm_num) (by linarith)

/-! ## A coarse universal bound on the consistency defect

The consistency defect compared with `deltaLd` in `lem:ld-soundness` is the
off-diagonal Born mass of a pair of measurement families acting on the two
tensor factors of a unit bipartite state.  Since the joint Born weights are
nonnegative and sum to one, that mass is at most one; combined with the two
lower bounds on `deltaLd` above this closes the regimes `1 ≤ ε` and `q ≤ d`.

The theorem below is formalization-only.  It is a generic statement about
`consistencyDefect` rather than about the low-degree game, and would naturally
live in `MIPStarRE/QPBT/Games/DistanceTheorems.lean`. -/

/-- Coarse bound on the consistency defect of a bipartite pair of measurement
families on a unit state: the off-diagonal Born mass is at most one.

This is the trivial estimate that closes the degenerate regimes of
`lem:ld-soundness`, where `deltaLd` is at least one by
`one_le_deltaLd_of_one_le_error` or by
`one_le_deltaLd_of_fieldSize_le_degree`.  Formalization-only support for
`blueprint/src/chapter/ch13_qpbt_test.tex:139-167`. -/
theorem consistencyDefect_heteroKron_le_one {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → Quantum.Measurement α ιA) (B : X → Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    bipartiteDefect μ A
        B ψ ≤ 1 := by
  have hEq : bipartiteDefect μ A
      B ψ =
      1 - avgOver μ (fun x => ∑ a : α,
        DistanceCalculus.stateQForm ψ
          (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap
      (fun x => DistanceCalculus.leftPlacedMeasurement (A x))
      (fun x => DistanceCalculus.rightPlacedMeasurement (B x)) hμ hψ
  have hnn : 0 ≤ avgOver μ (fun x => ∑ a : α,
      DistanceCalculus.stateQForm ψ
        (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) := by
    refine avgOver_nonneg μ _ (fun x => Finset.sum_nonneg (fun a _ => ?_))
    have hprod : heteroKron ((A x).effect a) (1 : Op ιB) *
        heteroKron (1 : Op ιA) ((B x).effect a) =
        heteroKron ((A x).effect a) ((B x).effect a) := by
      change Matrix.kroneckerMap _ ((A x).effect a)
            (1 : Op ιB) *
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Op ιA)
            ((B x).effect a) =
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            ((B x).effect a)
      simp [← Matrix.mul_kronecker_mul]
    rw [hprod]
    exact
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (Matrix.nonneg_iff_posSemidef.mp
          (kronecker_nonneg ((A x).pos a) ((B x).pos a)))).re_inner_nonneg_right ψ
  linarith

end MIPStarRE.QPBT
