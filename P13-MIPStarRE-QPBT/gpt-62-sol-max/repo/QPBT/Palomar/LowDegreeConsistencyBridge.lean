module

public import QPBT.Palomar.Definitions
public import QPBT.Palomar.LowDegreeGameStrategyBridge
public import QPBT.Test.LowDegreeGameTheorems

/-!
# Exact bridges for compact low-degree consistency

This module identifies the compact effect sums and three low-degree defects
with the corresponding library measurements and consistency defects.  It also
gives the inverse numerical-record conversion needed to apply the registered
soundness theorem to compact parameters.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248` and
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:394-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- A compact parameter record carries the registered admissible-size predicate. -/
theorem LowDegreeParams.is_admissible_size (P : LowDegreeParams) :
    MIPStarRE.QPBT.IsAdmissibleSize P.q :=
  P.hq

private theorem toMeasurement_relabel_postprocess_effect {A B C I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
    (e : A ≃ B) (M : POVM A I) (f : B → C) (c : C) :
    (((POVM.relabel e M).toMeasurement).postprocess f).effect c =
      postprocessEffect M (fun a => f (e a)) c := by
  simp only [Measurement.postprocess_effect, Finset.sum_filter, postprocessEffect,
    POVM.toMeasurement, Measurement.ofSumEqOne, POVM.relabel_effect]
  simpa only [Function.comp_apply, e.apply_symm_apply] using
    Equiv.sum_comp e.symm (fun a => if f (e a) = c then M.effect a else 0)

/-- The registered low-degree parameters and their canonical field. -/
def LowDegreeParams.toLdParams (P : LowDegreeParams) : QPBT.LdParams :=
  ⟨P.q, P.m, P.d, P.k, P.hm, P.hd, P.hk, P.is_admissible_size, P.hdvd⟩

abbrev LowDegreeParams.model (P : LowDegreeParams) := P.toLdParams.model

/-- The wrong-form-to-zero point map is unchanged by answer relabeling. -/
@[simp] theorem ldPointValuesOrZero_answerEquiv (L : MIPStarRE.QPBT.LdParams)
    (a : LowDegreeAnswer (LowDegreeParams.ofLdParams L)
      (MIPStarRE.QPBT.ScalarQ L)) :
    MIPStarRE.QPBT.ldPointValuesOrZero L (lowDegreeAnswerEquiv L a) =
      lowDegreePointValuesOrZero a := by
  rcases a with a | (a | a) <;> rfl

/-- Point-answer effects are unchanged by the game and answer relabelings. -/
private theorem pointReadout_toLibrary (L : LdParams) {I : Type*} [Fintype I] [DecidableEq I]
    (M : LowDegreeQuestion (LowDegreeParams.ofLdParams L) (ScalarQ L) →
      POVM (LowDegreeAnswer (LowDegreeParams.ofLdParams L) (ScalarQ L)) I)
    (u : LdPoint L) (a : Fin L.k → ScalarQ L) :
    (ldPointReadout (L := L) (fun q =>
      (POVM.relabel (lowDegreeAnswerEquiv L) (M ((lowDegreeQuestionEquiv L).symm q))).toMeasurement)
        u).effect a =
      postprocessEffect (M (lowDegreePointQuestion (LowDegreeParams.ofLdParams L) u))
        lowDegreePointValuesOrZero a := by
  simp only [ldPointReadout, toMeasurement_relabel_postprocess_effect, ldPointValuesOrZero_answerEquiv]
  rfl

/-- The compact PMF defect is exactly the library defect for the same distribution. -/
theorem consistencyDefect_toPMF {X O I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → O → Matrix I I ℂ) (B : X → O → Matrix J J ℂ)
    (ψ : EuclideanSpace ℂ (I × J)) :
    Palomar.consistencyDefect (μ.toPMF hμ) A B ψ =
      MIPStarRE.QPBT.consistencyDefect μ
        (fun x a => MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => MIPStarRE.QPBT.heteroKron 1 (B x a)) ψ := by
  unfold Palomar.consistencyDefect MIPStarRE.QPBT.consistencyDefect
  rw [MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum μ hμ]
  rfl

section

variable (L : LdParams) (S : LowDegreeStrategy (LowDegreeParams.ofLdParams L) (ScalarQ L))
variable (GA : PolyMeasTuple L S.ιA) (GB : PolyMeasTuple L S.ιB)

/-- The compact point--polynomial defect is exactly the registered first defect. -/
theorem ldPointPolynomialDefect_ofMeasurement_eq :
    ldPointPolynomialDefect (LowDegreeParams.ofLdParams L) S (POVM.ofMeasurement GB) =
      bipartiteDefect (uniformDistribution (LdPoint L))
        (ldPointReadout (lowDegreeStrategyToLibrary L S).A)
        (fun u => GB.postprocess (evalPolyTupleAt u)) S.ψ := by
  rw [ldPointPolynomialDefect, ← MIPStarRE.LDT.uniformDistribution_toPMF, consistencyDefect_toPMF]
  exact QPBT.consistencyDefect_congr _ _ _ _ _ _
    (fun u a => congrArg (fun E => heteroKron E 1) (pointReadout_toLibrary L S.alice u a).symm)
    (fun _ _ => rfl)

/-- The compact polynomial--point defect is exactly the registered second defect. -/
theorem ldPolynomialPointDefect_ofMeasurement_eq :
    ldPolynomialPointDefect (LowDegreeParams.ofLdParams L) S (POVM.ofMeasurement GA) =
      bipartiteDefect (uniformDistribution (LdPoint L)) (fun u => GA.postprocess (evalPolyTupleAt u))
        (ldPointReadout (lowDegreeStrategyToLibrary L S).B) S.ψ := by
  rw [ldPolynomialPointDefect, ← MIPStarRE.LDT.uniformDistribution_toPMF, consistencyDefect_toPMF]
  exact QPBT.consistencyDefect_congr _ _ _ _ _ _ (fun _ _ => rfl)
    (fun u a => congrArg (heteroKron 1) (pointReadout_toLibrary L S.bob u a).symm)

/-- The compact polynomial--polynomial defect is exactly the registered third defect. -/
theorem ldPolynomialPolynomialDefect_ofMeasurement_eq :
    ldPolynomialPolynomialDefect (LowDegreeParams.ofLdParams L) S
        (POVM.ofMeasurement GA) (POVM.ofMeasurement GB) =
      bipartiteDefect (uniformDistribution Unit) (fun _ => GA) (fun _ => GB) S.ψ := by
  rw [ldPolynomialPolynomialDefect, ← MIPStarRE.LDT.uniformDistribution_toPMF, consistencyDefect_toPMF]
  rfl

end

end

end MIPStarRE.QPBT.Palomar
