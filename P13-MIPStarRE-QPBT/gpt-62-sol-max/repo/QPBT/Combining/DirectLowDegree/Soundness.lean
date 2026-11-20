module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Error
public import QPBT.Combining.DirectLowDegree.Transport.Combining.SimultaneousGeneral
public import QPBT.ExplicitConstants

/-!
# Soundness for the directly indexed low-degree game

This module proves the quantum soundness statement for the directly indexed
low-degree game, in the form used by the Chapter 15 combining argument: the
polynomial-tuple measurements of `prop:ld-simultaneous-general-k` satisfy the
three consistency relations of `lem:ld-soundness` with the error function
`deltaLd` at the parameters `(q, m, d, k)` of the game.

In the regime `0 < ε ≤ 1` the error carried by
`prop:ld-simultaneous-general-k` — the error of `thm:main-formal` at the
combined parameters of `def:ld-combining-parameters` together with the recovery
loss `(m + k) d / q` — is absorbed into `deltaLd` at the universal constants
`a = 10^23` and `b = 1/80000` by
`exists_directCombinedTransportConstants`.  In the regime `1 ≤ ε` the error
function is at least one, while every bipartite consistency defect on a unit
state is at most one, so the conclusion carries no information there.

## Main statements

* `exists_direct_ld_soundness` — quantum soundness of the directly indexed
  low-degree game, with the error function `deltaLd`.
* `exists_direct_ld_soundness_of_k_eq_one` retains the one-coordinate proof
  used by the seed-indexed soundness transport.

## References

The obligation supports the Chapter 15 combining argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Quantum soundness of the directly indexed low-degree game.
This is the established directly indexed auxiliary form described in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, needed by the Chapter 15
combining argument at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.

This is a formalization auxiliary assertion, not the source-labelled
`lem:ld-soundness`.  Its proof invokes `MIPStarRE.LDT.Test.mainFormal` and
verifies that theorem's sampling condition `400 M d <= N` at combined dimension
`M = m + k`, using `N = 2560000 M^3 d`.  It does not invoke the tensor-code
theorem used in the source proof of `lem:ld-soundness`.  At seed-indexed
dimension `m`, that route chooses `K = m^3 d` but requires
`K >= 12 m (d + 1)`.  The direct proof therefore discharges neither that bound
nor the claimed game correspondence; both remain open for the printed source route.
The measurements are those of `prop:ld-simultaneous-general-k`, and the
universal constants exhibited are `a = 10^23` and `b = 1/80000`: for
`0 < ε ≤ 1` the error of that proposition is absorbed into `deltaLd` by
`exists_directCombinedTransportConstants`, and for `1 ≤ ε` the error function
is at least one while every bipartite consistency defect on a unit state is at
most one. -/
theorem exists_direct_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          let δ := deltaLd a b ε D.q D.m D.d D.k
          ∃ GA GB, DirectLdConsistency S GA GB δ δ := by
  obtain ⟨a, b, ha, hb0, hb1, habs⟩ := exists_directCombinedTransportConstants
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro D ε hε S hS hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_combinedError D S hS ε hwin
  by_cases hε1 : ε ≤ 1
  · have h := habs D ε hε hε1
    exact ⟨GA, GB, h1.trans h, h2.trans h,
      h3.trans ((le_add_of_nonneg_right (by positivity)).trans h)⟩
  · have h := one_le_deltaLd_of_one_le_error (q := D.q) ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk
    refine ⟨GA, GB, ?_, ?_, ?_⟩ <;>
      exact (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm).trans h

/-- The one-coordinate bound uses the trivial defect cap outside the small-error
regime, and the square-root transport bound inside it. -/
theorem direct_ld_soundness_of_k_eq_one_explicit (D : DirectLdParams) (ε : ℝ)
    (hk : D.k = 1) (hε : 0 < ε) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) (hwin : 1 - ε ≤ S.value) :
    let δ := deltaLd pauliBaselineLowDegreeConstant pauliBaselineLowDegreePower ε D.q D.m D.d D.k
    ∃ GA GB, DirectLdConsistency S GA GB δ δ := by
  intro δ
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_of_k_eq_one D hk S hS ε hwin
  let E := Test.mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 * ε)
  let T := E + ((D.m : ℝ) * D.d) / D.q + ε
  have hmin : min 1 E ≤ δ := by
    obtain ⟨ha, hb, _, h⟩ := direct_ld_transport_constants_explicit 1 le_rfl
    by_cases he : ε ≤ 1
    · have hs : Real.sqrt T ≤ δ := by
        simpa only [δ, T, E, hk, Nat.cast_one, one_mul, mul_one, pauliBaselineLowDegreeConstant,
          pauliBaselineLowDegreePower] using h D ε hε he
      apply le_trans _ hs
      by_cases ht : T ≤ 1
      · have hET : E ≤ T := (le_add_of_nonneg_right (by positivity)).trans
          (le_add_of_nonneg_right hε.le)
        exact (min_le_right ..).trans (hET.trans (Real.le_sqrt_self_iff.mpr ht))
      · exact (min_le_left ..).trans (by simpa using Real.sqrt_le_sqrt (not_le.mp ht).le)
    · exact (min_le_left ..).trans <| one_le_deltaLd_of_one_le_error
        (by norm_num [pauliBaselineLowDegreeConstant]) (by norm_num [pauliBaselineLowDegreePower])
        (not_le.mp he).le D.hm D.hd D.hk
  refine ⟨GA, GB, ?_, ?_, ?_⟩ <;>
    refine (le_min (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _)
      _ _ S.ψ S.ψ_norm) ?_).trans hmin
  exacts [h1, h2, h3]

end

end MIPStarRE.QPBT
