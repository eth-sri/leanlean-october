module

public import QPBT.Games.ErrorFunctions
public import QPBT.Combining.DirectLowDegree.Game
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

open MIPStarRE.LDT MIPStarRE.Quantum DistanceCalculus

/-! ## The auxiliary sampling parameter -/

/-- The auxiliary sampling parameter of the low-degree soundness transport.

The low individual degree theorem is applied to each coordinate strategy of
a directly indexed strategy with `k = 2560000 m³ d` samples.  This
is the multiple of the exponential scale `2560000 m²` of `mainFormalError`
whose quotient is `m d`, and it dominates the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal` uniformly in the
parameters.  Blueprint `ch13_qpbt_test.tex:139-167`; paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`. -/
def directLdAuxParameter (D : DirectLdParams) : ℕ := 2560000 * D.m ^ 3 * D.d

/-- The auxiliary sampling parameter is positive, which is the boundary
hypothesis `0 < k` of `MIPStarRE.LDT.Test.mainFormal`. -/
theorem directLdAuxParameter_pos (D : DirectLdParams) : 0 < directLdAuxParameter D := by
  unfold directLdAuxParameter
  have := D.hm
  have := D.hd
  positivity

/-- The auxiliary sampling parameter satisfies the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal`, documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`. -/
theorem four_hundred_mul_le_directLdAuxParameter (D : DirectLdParams) :
    400 * D.toLDTParameters.m * D.toLDTParameters.d ≤ directLdAuxParameter D := by
  have hcube : D.m ≤ D.m ^ 3 := Nat.le_self_pow (by norm_num) D.m
  change 400 * D.m * D.d ≤ 2560000 * D.m ^ 3 * D.d
  exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hcube) le_rfl

/-! ## Elementary positivity of the parameters

The four lemmas below are formalization-only conveniences: they record the
positivity fields of `DirectLdParams` in the real numbers, where all the
scalar estimates of this module take place. -/

section

variable (D : DirectLdParams)
include D

private theorem directLd_one_le_m : (1 : ℝ) ≤ (D.m : ℝ) := by
  have h := D.hm
  simp_all

private theorem directLd_one_le_d : (1 : ℝ) ≤ (D.d : ℝ) := by
  have h := D.hd
  simp_all

private theorem directLd_one_le_k : (1 : ℝ) ≤ (D.k : ℝ) := by
  have h := D.hk
  simp_all

private theorem directLd_one_le_q : (1 : ℝ) ≤ (D.q : ℝ) := by
  have h : 1 ≤ D.q := D.toLDTParameters.hq
  simp_all

end

/-! ## The three terms of the LDT error -/

/-- With the auxiliary sampling parameter the exponential scale of
`mainFormalError` collapses: the argument of its exponential term is exactly
`m d`.

Formalization-only scalar identity for the error function displayed in
`MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`. -/
theorem directLdAuxParameter_exp_arg (D : DirectLdParams) :
    (directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))) =
      (D.m : ℝ) * (D.d : ℝ) := by
  have hm : (0 : ℝ) < D.m := zero_lt_one.trans_le (directLd_one_le_m D)
  unfold directLdAuxParameter
  push_cast
  field_simp

/-! ## The transport envelope

The three scalar quantities `ε^b`, `q^(-b)` and `2^(-b m d)` at the transport
exponent `b = 1/80000` are the inner factor of `deltaLd`; the abbreviation
below names their sum. -/

/-- The inner factor of `deltaLd` at the transport exponent `b = 1/80000`.
This is a formalization-only abbreviation, shared with the absorption of the
error of `prop:ld-simultaneous-general-k`. -/
noncomputable def transportEnvelope (D : DirectLdParams) (ε : ℝ) : ℝ :=
  Real.rpow ε (1 / 80000) + Real.rpow (D.q : ℝ) (-(1 / 80000)) +
    Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))

theorem transportEnvelope_rpow_eps_le (D : DirectLdParams) (ε : ℝ) :
    Real.rpow ε (1 / 80000) ≤ transportEnvelope D ε :=
  rpow_noise_le_soundnessTail D.q (D.m * D.d : ℕ) _ ε

section

variable (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε)
include D ε hε

theorem transportEnvelope_rpow_q_le :
    Real.rpow (D.q : ℝ) (-(1 / 80000)) ≤ transportEnvelope D ε :=
  rpow_field_le_soundnessTail D.q (D.m * D.d : ℕ) _ hε

theorem transportEnvelope_nonneg :
    0 ≤ transportEnvelope D ε :=
  soundnessTail_nonneg D.q (D.m * D.d : ℕ) _ hε

end

/-! ## The LDT error at the auxiliary sampling parameter -/

/-- The three noise terms when the auxiliary sample size is chosen to give
exponential decay in `m d`. -/
noncomputable abbrev directLdNoise (D : DirectLdParams) (η : ℝ) :=
  η ^ (1 / 40000 : ℝ) + ((D.d : ℝ) / D.q) ^ (1 / 40000 : ℝ) +
    Real.exp (-((D.m : ℝ) * D.d))

noncomputable abbrev directLdPrefactor (D : DirectLdParams) : ℝ :=
  655360000000000000 * (D.m : ℝ) ^ 10 * (D.d : ℝ) ^ 2

/-- The main LDT error with the sample size substituted. -/
theorem mainFormalError_direct_eq (D : DirectLdParams) (η : ℝ) :
    Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) η =
      directLdPrefactor D * directLdNoise D η := by
  change 100000 * (directLdAuxParameter D : ℝ) ^ 2 * (D.m : ℝ) ^ 4 *
    (η ^ (1 / 40000 : ℝ) + ((D.d : ℝ) / D.q) ^ (1 / 40000 : ℝ) +
      Real.exp (-((directLdAuxParameter D : ℝ) / (2560000 * (D.m : ℝ) ^ 2)))) = _
  rw [directLdAuxParameter_exp_arg]
  unfold directLdAuxParameter directLdPrefactor directLdNoise
  push_cast
  ring

/-- A positive scaling factor at least one can be pulled out of a small real power. -/
theorem transport_rpow_mul_le {c x b : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) (hb : b ≤ 1) :
    (c * x) ^ b ≤ c * x ^ b := by
  rw [Real.mul_rpow (zero_le_one.trans hc) hx]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hc hb) (Real.rpow_nonneg hx _)

/-- A degree/field ratio loses at most one power of its numerator. -/
theorem transport_rpow_ratio_le {d q b r : ℝ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hbr : b ≤ r) (hr : r ≤ 1) : (d / q) ^ r ≤ d * q ^ (-b) := by
  have hq0 := zero_le_one.trans hq
  rw [Real.div_rpow (zero_le_one.trans hd) hq0, div_eq_mul_inv, ← Real.rpow_neg hq0]
  exact mul_le_mul (Real.rpow_le_self_of_one_le hd hr)
    (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hbr))
    (Real.rpow_nonneg hq0 _) (zero_le_one.trans hd)

/-- Exponential decay implies base-two decay at any smaller rate. -/
theorem transport_exp_le {u v b : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp (-v) ≤ (2 : ℝ) ^ (-(b * u)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [mul_le_mul_of_nonneg_right hlog (mul_nonneg hb hu),
    mul_le_of_le_one_left hu hb1, huv]

private theorem sqrt_rpow_half {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    Real.sqrt (x ^ r) = x ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  simp [div_eq_mul_inv]

private theorem sqrt_directLdEnvelope_le (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt (directLdNoise D (3 * ε)) ≤ 3 * (D.d : ℝ) * transportEnvelope D ε := by
  have hd := directLd_one_le_d D
  have hq := directLd_one_le_q D
  have hε' : 0 ≤ 3 * ε := by positivity
  have hr : (1 / 40000 : ℝ) / 2 = 1 / 80000 := by norm_num
  simp only [directLdNoise, transportEnvelope, Real.rpow_eq_pow]
  refine (sqrt_add3_le_add3_sqrt (by positivity) (by positivity) (by positivity)).trans ?_
  rw [sqrt_rpow_half hε', sqrt_rpow_half (by positivity : 0 ≤ (D.d : ℝ) / D.q), hr, ← Real.exp_half]
  have h1 := transport_rpow_mul_le (c := 3) (b := 1 / 80000) (by norm_num) hε (by norm_num)
  have h2 := transport_rpow_ratio_le hd hq (b := 1 / 80000) le_rfl (by norm_num)
  have h3 : Real.exp (-((D.m : ℝ) * D.d) / 2) ≤
      (2 : ℝ) ^ (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
    push_cast
    convert transport_exp_le (u := (D.m : ℝ) * D.d / 2) (v := (D.m : ℝ) * D.d / 2)
      (b := 1 / 40000) (by positivity) le_rfl (by norm_num) (by norm_num) using 1 <;> ring_nf
  nlinarith only [h1, h2, h3,
    mul_nonneg (show 0 ≤ (D.d : ℝ) - 1 by linarith) (Real.rpow_nonneg hε (1 / 80000)),
    mul_nonneg (show 0 ≤ (D.d : ℝ) by positivity)
      (Real.rpow_nonneg (Nat.cast_nonneg D.q) (-(1 / 80000))),
    mul_nonneg (show 0 ≤ 3 * (D.d : ℝ) - 1 by linarith)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))))]

private theorem sqrt_directLdTransportError_le (D : DirectLdParams) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sqrt (Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
      2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * transportEnvelope D ε := by
  rw [mainFormalError_direct_eq]
  have hm := directLd_one_le_m D
  have hd := directLd_one_le_d D
  have hq := directLd_one_le_q D
  have hε := hε0.le
  let M := (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2
  let E := transportEnvelope D ε
  have hE : 0 ≤ E := transportEnvelope_nonneg D hε
  have hmd : 1 ≤ (D.m : ℝ) * D.d := one_le_mul_of_one_le_of_one_le hm hd
  have hM : (D.m : ℝ) * D.d ≤ M := by
    dsimp only [M]
    gcongr
    · simpa using pow_le_pow_right₀ hm (show 1 ≤ 5 by decide)
    · simpa using pow_le_pow_right₀ hd (show 1 ≤ 2 by decide)
  have hP : Real.sqrt (directLdPrefactor D) ≤ 820000000 * (D.m : ℝ) ^ 5 * D.d := by
    refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
    dsimp only [directLdPrefactor]
    nlinarith only [show 0 ≤ (D.m : ℝ) ^ 10 * (D.d : ℝ) ^ 2 by positivity]
  have h1 := mul_le_mul hP (sqrt_directLdEnvelope_le D hε) (Real.sqrt_nonneg _) (by positivity)
  have h2 : Real.sqrt ((D.m : ℝ) * D.d / D.q) ≤ M * E := by
    rw [Real.sqrt_eq_rpow]
    refine (transport_rpow_ratio_le hmd hq (by norm_num : (1 / 80000 : ℝ) ≤ 1 / 2) (by norm_num)).trans ?_
    exact mul_le_mul hM (transportEnvelope_rpow_q_le D hε) (by positivity) (zero_le_one.trans (hmd.trans hM))
  have h3 : Real.sqrt ε ≤ M * E := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num : (1 / 80000 : ℝ) ≤ 1 / 2)).trans
      ((transportEnvelope_rpow_eps_le D ε).trans (le_mul_of_one_le_left hE (hmd.trans hM)))
  refine (sqrt_add3_le_add3_sqrt (by positivity) (by positivity) hε).trans ?_
  rw [Real.sqrt_mul (by positivity : 0 ≤ directLdPrefactor D)]
  dsimp only [M, E] at h2 h3
  have hME := mul_nonneg (zero_le_one.trans (hmd.trans hM)) hE
  dsimp only [M, E] at hME
  nlinarith only [h1, h2, h3, hME]

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
  have hm := directLd_one_le_m D
  have hd := directLd_one_le_d D
  have hk := directLd_one_le_k D
  let N : ℝ := ((D.d * D.m * D.k : ℕ) : ℝ)
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 1 ≤ D.d * D.m * D.k from Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hT := transportEnvelope_nonneg D hε0.le
  have hpow : N ^ (5 : ℕ) ≤ N ^ (2500000000 * C₀) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)
  have hpoly : (D.k : ℝ) * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 ≤ N ^ (5 : ℕ) := by
    dsimp only [N]
    push_cast
    -- Keep the three real bases separate for monotonicity in each exponent.
    calc _ ≤ (D.k : ℝ) ^ 5 * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 5 := by
            gcongr
            · simpa using pow_le_pow_right₀ hk (by decide : 1 ≤ 5)
            · decide
         _ = _ := by ring
  change _ ≤ 2500000000 * C₀ * N ^ (2500000000 * C₀) * transportEnvelope D ε
  calc _ ≤ C₀ * (D.k : ℝ) * (2500000000 * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2 *
      transportEnvelope D ε) := by gcongr; exact sqrt_directLdTransportError_le D hε0 hε1
    _ = 2500000000 * C₀ * ((D.k : ℝ) * (D.m : ℝ) ^ 5 * (D.d : ℝ) ^ 2) *
        transportEnvelope D ε := by ring
    _ ≤ _ := by gcongr; exact hpoly.trans hpow

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
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hd hm) hk)
  have hX := Real.one_le_rpow hbase (zero_le_one.trans ha)
  have hY := Real.one_le_rpow hε hb
  simp only [deltaLd, Real.rpow_eq_pow]
  apply one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hX)
  exact hY.trans <| (le_add_of_nonneg_right (by positivity)).trans
    (le_add_of_nonneg_right (by positivity))

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
  rw [consistencyDefect_placed_eq_one_sub_overlap μ A B ψ hμ hψ, sub_le_self_iff]
  exact avgOver_nonneg _ _ fun x => Finset.sum_nonneg fun a _ =>
    stateQForm_nonneg ψ (kronecker_nonneg ((A x).pos a) ((B x).pos a))

end MIPStarRE.QPBT
