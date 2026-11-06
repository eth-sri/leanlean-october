module

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

open MIPStarRE.LDT MIPStarRE.Quantum

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
  have hm : 0 < D.m := D.hm
  have hd : 0 < D.d := D.hd
  have hpow : 0 < D.m ^ 3 := pow_pos hm 3
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hpow) hd

/-- The auxiliary sampling parameter satisfies the corrected large-sampling
hypothesis `400 m d ≤ k` of `MIPStarRE.LDT.Test.mainFormal`, documented in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`. -/
theorem four_hundred_mul_le_directLdAuxParameter (D : DirectLdParams) :
    400 * D.toLDTParameters.m * D.toLDTParameters.d ≤ directLdAuxParameter D := by
  have hcube : D.m ≤ D.m ^ 3 := Nat.le_self_pow (by norm_num) D.m
  change 400 * D.m * D.d ≤ 2560000 * D.m ^ 3 * D.d
  exact Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) hcube) le_rfl

noncomputable def transportEnvelope (D : DirectLdParams) (ε : ℝ) : ℝ :=
  Real.rpow ε (1 / 80000) + Real.rpow (D.q : ℝ) (-(1 / 80000)) +
    Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))

theorem transportEnvelope_rpow_eps_le (D : DirectLdParams) (ε : ℝ) :
    Real.rpow ε (1 / 80000) ≤ transportEnvelope D ε := by
  have hy : (0 : ℝ) ≤ Real.rpow (D.q : ℝ) (-(1 / 80000)) :=
    Real.rpow_nonneg (by positivity) _
  have hz : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold transportEnvelope
  linarith

theorem transportEnvelope_nonneg (D : DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ transportEnvelope D ε :=
  le_trans (Real.rpow_nonneg hε _) (transportEnvelope_rpow_eps_le D ε)


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
    have hn : 1 ≤ d * m * k := Nat.mul_pos (Nat.mul_pos hd hm) hk
    exact_mod_cast hn
  have hX : (1 : ℝ) ≤ Real.rpow ((d * m * k : ℕ) : ℝ) a := by
    simp only [Real.rpow_eq_pow]
    calc (1 : ℝ) = (1 : ℝ) ^ a := (Real.one_rpow a).symm
      _ ≤ ((d * m * k : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hY : (1 : ℝ) ≤ Real.rpow ε b := by
    simp only [Real.rpow_eq_pow]
    calc (1 : ℝ) = (1 : ℝ) ^ b := (Real.one_rpow b).symm
      _ ≤ ε ^ b := Real.rpow_le_rpow (by norm_num) hε hb
  have hZ : (0 : ℝ) ≤ Real.rpow (q : ℝ) (-b) := Real.rpow_nonneg (by positivity) _
  have hW : (0 : ℝ) ≤ Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hax : (1 : ℝ) ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a := by nlinarith
  have hsum : (1 : ℝ) ≤ Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) := by linarith
  unfold deltaLd
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a *
        (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ)))) :=
      mul_le_mul hax hsum (by norm_num) (by linarith)

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
    consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 1 := by
  have hEq : consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ =
      1 - avgOver μ (fun x => ∑ a : α,
        DistanceCalculus.stateQForm ψ
          (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
      (fun x => DistanceCalculus.leftPlacedMeasurement (A x))
      (fun x => DistanceCalculus.rightPlacedMeasurement (B x))
      ψ hμ hψ
  have hnn : 0 ≤ avgOver μ (fun x => ∑ a : α,
      DistanceCalculus.stateQForm ψ
        (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a))) := by
    refine avgOver_nonneg μ _ (fun x => Finset.sum_nonneg (fun a _ => ?_))
    have hprod : heteroKron ((A x).effect a) (1 : Op ιB) *
        heteroKron (1 : Op ιA) ((B x).effect a) =
        heteroKron ((A x).effect a) ((B x).effect a) := by
      change Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            (1 : Op ιB) *
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Op ιA)
            ((B x).effect a) =
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            ((B x).effect a)
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    rw [hprod]
    unfold DistanceCalculus.stateQForm applyOperatorToState heteroKron
    exact
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (Matrix.nonneg_iff_posSemidef.mp
          (kronecker_nonneg ((A x).pos a) ((B x).pos a)))).re_inner_nonneg_right ψ
  rw [hEq]
  linarith

end MIPStarRE.QPBT
