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

theorem le_sqrt_of_le_of_le_one {x T : ℝ} (hxT : x ≤ T) (hT : T ≤ 1) :
    x ≤ Real.sqrt T := by
  rcases le_or_gt x 0 with hx | hx
  · exact le_trans hx (Real.sqrt_nonneg T)
  · exact (Real.sqrt_sq hx.le).symm.trans_le (Real.sqrt_le_sqrt (by nlinarith))

theorem direct_ld_soundness_of_k_eq_one_explicit :
    ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      (((S.A (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      (((S.B (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k := by
  intro D ε hε S hS hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_directSimultaneousPolynomialMeasurements_combinedError D S hS ε hwin
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  all_goals by_cases hε1 : ε ≤ 1
  · exact le_trans h1 (exists_directCombinedTransportConstants D ε hε hε1)
  · exact le_trans
      (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (one_le_deltaLd_of_one_le_error (by unfold pauliBaselineLowDegreeConstant; norm_num)
        (by unfold pauliBaselineLowDegreePower; norm_num) (not_le.mp hε1).le D.hm D.hd D.hk)
  · exact le_trans h2 (exists_directCombinedTransportConstants D ε hε hε1)
  · exact le_trans
      (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (one_le_deltaLd_of_one_le_error (by unfold pauliBaselineLowDegreeConstant; norm_num)
        (by unfold pauliBaselineLowDegreePower; norm_num) (not_le.mp hε1).le D.hm D.hd D.hk)
  · refine le_trans h3 (le_trans ?_ (exists_directCombinedTransportConstants D ε hε hε1))
    have hloss : (0 : ℝ) ≤ ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) := by positivity
    linarith
  · exact le_trans
      (consistencyDefect_heteroKron_le_one _ (uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (one_le_deltaLd_of_one_le_error (by unfold pauliBaselineLowDegreeConstant; norm_num)
        (by unfold pauliBaselineLowDegreePower; norm_num) (not_le.mp hε1).le D.hm D.hd D.hk)

theorem exists_direct_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      (((S.A (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      ((GB.postprocess (evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect
                  (uniformDistribution (Fin D.m → DirectScalarQ D))
                  (fun u outcome =>
                    heteroKron
                      ((GA.postprocess (evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    heteroKron 1
                      (((S.B (directLdPointQuestionOf D u)).postprocess
                        (directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k ∧
              consistencyDefect (uniformDistribution Unit)
                  (fun _ g => heteroKron (GA.effect g) 1)
                  (fun _ g => heteroKron 1 (GB.effect g))
                  S.ψ ≤ deltaLd a b ε D.q D.m D.d D.k :=
  ⟨pauliBaselineLowDegreeConstant, pauliBaselineLowDegreePower,
    by unfold pauliBaselineLowDegreeConstant; norm_num,
    by unfold pauliBaselineLowDegreePower; norm_num,
    by unfold pauliBaselineLowDegreePower; norm_num,
    direct_ld_soundness_of_k_eq_one_explicit⟩

end

end MIPStarRE.QPBT
