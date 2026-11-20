module

public import QPBT.Combining.DirectLowDegree.Soundness
public import QPBT.Combining.DirectLowDegree.Transport.PointAgreement
public import QPBT.Combining.DirectLowDegree.Transport.SeedError
public import QPBT.Games.Sandwich.Support

/-!
# Quantum soundness of the seed-indexed low-degree game

The general simultaneity reduction for the directly indexed game is transported
through the correlated seed dilation. Point consistency survives compression
exactly; global polynomial consistency is recovered by point agreement and
Schwartz--Zippel, with the square-root loss absorbed into `deltaLd`.

## References

* `arXiv:2001.04383v3, Section 7.1, Theorem 7.8`
* `arXiv:1904.05870v3, Theorem 4.43 and its proof`
* Blueprint `lem:ld-soundness`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Distinct polynomial tuples collide only where one of their distinct
coordinates collides. This formalization auxiliary for `lem:ld-soundness`
therefore has the same Schwartz--Zippel bound for every simultaneity parameter. -/
theorem polyTupleAgreement_avg_le_mdq (L : LdParams)
    (g g' : PolyTuple L) (hne : g ≠ g') :
    avgOver (uniformDistribution (LdPoint L))
        (fun u => if evalPolyTupleAt u g = evalPolyTupleAt u g' then
          (1 : ℝ) else 0) ≤
      ((L.m : ℝ) * (L.d : ℝ)) / (L.q : ℝ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine le_trans (avgOver_mono _ _ _ fun u => ?_)
    (directPolynomialAgreement_avg_le_mdq L.toDirectLdParams (g i) (g' i) hi)
  split_ifs with h h'
  · rfl
  · exact False.elim (h' (congrFun h i))
  · norm_num
  · rfl

set_option maxHeartbeats 1000000 in
/-- Quantum soundness of the simultaneous classical low individual degree
test (blueprint `lem:ld-soundness`; paper theorem and proof
`arXiv:2001.04383v3, Section 7.1, Theorem 7.8`).

The first two consistency bounds compare the point-answer postprocessing of the
strategy with evaluations of the polynomial measurements. Answers of the wrong
form are folded into the zero tuple so that the point family remains a POVM.

The printed proof of MIP*=RE Theorem 7.8 claims a game correspondence and
applies arXiv:2111.08131v3, Theorem 4.7, with `K = m ^ 3 * d`. The latter
theorem assumes `K ≥ 12 * m * t`, where `t = d + 1` for the Reed-Solomon code;
the printed choice fails this hypothesis for small `m`. MIP*=RE does not print
that inequality. Neither the correspondence nor the bound for that choice of
`K` is used or established here. They are detailed in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`rem:ld-soundness-provider`, and are tracked by issue Dengnifer/MIPStarRE-QPBT-bak#527.

The proof here instead uses the established direct low individual degree
reduction and transports it through the correlated seed dilation. It works for
every `L.k`: simultaneity comes from the single-polynomial case by the combining
reduction of Theorem 4.43 in the NEEXP paper, not coordinatewise; the
coordinatewise route planned for the formalization is refuted in
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`. The combining reduction
is proved for the directly indexed game in
`QPBT/Combining/DirectLowDegree/Transport/Combining/SimultaneousGeneral.lean`;
the two mixed relations survive seed compression exactly. Global consistency
is recovered from point agreement and the tuple Schwartz--Zippel bound, rather
than double compression. The resulting square-root loss is absorbed by replacing
the direct constants `(a, b)` with `(10 * a, b / 2)`. This discharges the
general-`k` seed-indexed extension tracked by issue Dengnifer/MIPStarRE-QPBT-bak#527,
without using either of these obligations of the printed tensor-code route;
the proof avoids them, and the source gap above stays open.
(Issues #16 and #210, cited by earlier revisions of this docstring, are
closed; #527 is the live tracker.) -/
theorem exists_ld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (L : LdParams) (ε : ℝ), 0 < ε →
        ∀ S : Strategy (ldGame L), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : PolyMeasTuple L S.ιA, ∃ GB : PolyMeasTuple L S.ιB,
            bipartiteDefect (uniformDistribution (LdPoint L))
                (ldPointReadout S.A)
                (fun u => GB.postprocess (evalPolyTupleAt u))
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            bipartiteDefect (uniformDistribution (LdPoint L))
                (fun u => GA.postprocess (evalPolyTupleAt u))
                (ldPointReadout S.B)
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k ∧
            bipartiteDefect (uniformDistribution Unit)
                (fun _ => GA)
                (fun _ => GB)
                S.ψ ≤ deltaLd a b ε L.q L.m L.d L.k := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hs⟩ := exists_direct_ld_soundness
  refine ⟨10 * a, b / 2, by linarith, by positivity, by linarith, ?_⟩
  intro L ε hε S hS hwin
  let D := L.toDirectLdParams
  let E := deltaLd a b ε L.q L.m L.d L.k
  let F := deltaLd (10 * a) (b / 2) ε L.q L.m L.d L.k
  obtain ⟨GA₀, GB₀, h1, h2, _⟩ := hs D ε hε (ldStrategyToDirect L S)
    (ldStrategyToDirect_isProjective L S hS)
    (by simp_all [ldStrategyToDirect_value_eq])
  let GA := seedFiberCompressPolyMeasTuple L GA₀
  let GB := seedFiberCompressPolyMeasTuple L GB₀
  let μ := uniformDistribution (LdPoint L)
  let A := ldPointReadout S.A
  let B := ldPointReadout S.B
  let A' u := GA.postprocess (evalPolyTupleAt u)
  let B' u := GB.postprocess (evalPolyTupleAt u)
  erw [ldStrategyToDirect_pointPolynomial_compression L S GB₀] at h1
  erw [ldStrategyToDirect_polynomialPoint_compression L S GA₀] at h2
  have c1 : bipartiteDefect μ A B' S.ψ ≤ E := h1
  have c2 : bipartiteDefect μ A' B S.ψ ≤ E := h2
  have c3 := ldPointPair_consistencyDefect_le L S ε hwin
  have ctrans : bipartiteDefect μ A' B' S.ψ ≤ E + 2 * Real.sqrt (9 * ε + E) :=
    consistencyDefect_trans_le μ (fun u => DistanceCalculus.leftPlacedMeasurement (A' u))
      (fun u => DistanceCalculus.rightPlacedMeasurement (B u))
      (fun u => DistanceCalculus.leftPlacedMeasurement (A u))
      (fun u => DistanceCalculus.rightPlacedMeasurement (B' u)) S.ψ _ _ _
      (uniformDistribution_isProbability _) S.ψ_norm c2 c3 c1
  have ccode : bipartiteDefect (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) S.ψ ≤
      E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    have h := SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) S.ψ
      (fun g u => evalPolyTupleAt u g) ((L.m : ℝ) * L.d / L.q)
      (uniformDistribution_isProbability _) S.ψ_norm (by positivity)
      (fun g g' hne => polyTupleAgreement_avg_le_mdq L g g' hne)
    simp only [bipartiteDefect, consistencyDefect, Distribution.avgOver_prod,
      avgOver_uniform_const] at h
    simpa only [bipartiteDefect, consistencyDefect, avgOver_uniform_const] using
      h.trans (add_le_add_left ctrans _)
  have hsqrt : 10 * Real.sqrt E ≤ F := ten_sqrt_deltaLd_le D ha hε.le
  have hEnn : 0 ≤ E := by dsimp [E, deltaLd]; positivity
  have hbound {X α : Type} [Fintype X] [DecidableEq X] [Nonempty X]
      [Fintype α] [DecidableEq α]
      (A : X → MIPStarRE.Quantum.Measurement α S.ιA)
      (B : X → MIPStarRE.Quantum.Measurement α S.ιB)
      (hc : bipartiteDefect (uniformDistribution X)
        A
        B S.ψ ≤
        E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q) :
      bipartiteDefect (uniformDistribution X)
        A
        B S.ψ ≤ F := by
    have hone := consistencyDefect_heteroKron_le_one
      (uniformDistribution X) (uniformDistribution_isProbability _) A B S.ψ S.ψ_norm
    by_cases hε1 : ε ≤ 1
    · by_cases hE1 : E ≤ 1
      · obtain ⟨he, hm⟩ := error_and_collision_le_deltaLd D ha hb1 hε hε1
        change ε ≤ E at he
        change (L.m : ℝ) * L.d / L.q ≤ E at hm
        have hEs := Real.le_sqrt_self_iff.mpr hE1
        have hroot : Real.sqrt (9 * ε + E) ≤ 4 * Real.sqrt E := by
          apply (Real.sqrt_le_iff).mpr
          refine ⟨by positivity, ?_⟩
          nlinarith [Real.sq_sqrt hEnn]
        exact hc.trans (by linarith)
      · have hEs : 1 ≤ Real.sqrt E := by
          simpa using Real.sqrt_le_sqrt (not_le.mp hE1).le
        exact hone.trans (by linarith)
    · exact hone.trans (one_le_deltaLd_of_one_le_error (by linarith) (by positivity)
        (not_le.mp hε1).le L.hm L.hd L.hk)
  have hrem : E ≤ E + 2 * Real.sqrt (9 * ε + E) + (L.m : ℝ) * L.d / L.q := by
    exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  exact ⟨GA, GB, hbound A B' (c1.trans hrem), hbound A' B (c2.trans hrem), hbound _ _ ccode⟩

end

end MIPStarRE.QPBT
