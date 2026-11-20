module

public import QPBT.Extraction.CharacterConsistency
public import QPBT.Extraction.EncodingSupport
public import QPBT.Extraction.Observables
public import QPBT.Extraction.PolynomialCollision

/-!
# Polynomial outcomes in the pulling argument

The joint measurement of a polynomial marginal and an ideal Pauli register
returns the difference between the polynomial and the encoding of the register.
Decoding this difference gives exactly the pulled-apart measurement. Polynomial
collision estimates apply to these representatives without an encoding-support
restriction on the original marginal.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1530-1605`,
  `eq:qld-pulling-11`, `eq:qld-pulling-12`, and the following symmetry argument.
- `docs/paper-gaps/qpbt_decoding-identity.tex`; only decoder linearity and its
  left-inverse identity are used here.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the `eq:qld-pulling-cons` extraction obligation;
  these
  auxiliary results do not assert it. This module was originally filed
  under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
- The collision estimate compares unequal difference polynomials under uniform
  evaluation.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section

open scoped Classical

/-- The outcome `g - g_h` in `eq:qld-pulling-12` is a bounded polynomial
representative, even when `g` is not in the encoding image. -/
def pullingPoly {P : AdmissibleParams} (outcome : Poly P × PauliRegister P) : Poly P :=
  outcome.1 - encodingPoly outcome.2

/-- Decoder linearity identifies the label in `eq:qld-pulling-12`. This uses
`Dec(g_h) = h`, never the reverse identity on arbitrary polynomials. -/
theorem decodeFq_pullingPoly {P : AdmissibleParams}
    (outcome : Poly P × PauliRegister P) :
    decodeFq (pullingPoly outcome) = decodeFq outcome.1 - outcome.2 := by
  have hsub (g h : Poly P) : decodeFq (g - h) = decodeFq g - decodeFq h := by
    funext y
    simp [decodeOn, decodeAt, evalPoly, MvPolynomial.eval_sub]
  rw [pullingPoly, hsub, decodeFq_lowDegreeEncoding]

section

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind)
include P epsilon deltaG S w side W

/-- The projective measurement with polynomial outcomes `g - g_h` used to
organize the last step of the pulling argument. Its input witness remains
supplied; no global witness is constructed by this definition. -/
def pullingMeas :
    Measurement (Poly P) (ExtractionBlock P (S.LocalSpace side)) :=
  (tensorMeasurement (w.marginalPoly side W) (pauliRegisterMeas W)).postprocess pullingPoly

/-- The joint effects are tensor products of orthogonal projections, and
postprocessing retains projectivity. -/
theorem pullingMeas_isProjective :
    Measurement.IsProjective (pullingMeas w side W) := by
  exact SandwichProduct.postprocess_isProjective _
    (tensorMeasurement_isProjective (w.marginalPoly_isProjective side W)
      (pauliRegisterMeas_isProjective W)) _

/-- Decoding the difference-polynomial measurement recovers `eq:tilde_M`
exactly. The equality holds on the full bounded polynomial carrier. -/
theorem pullingMeas_postprocess_effect (u : PauliRegister P) (a : PauliScalar P) :
    ((pullingMeas w side W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a =
      tildeM w side W u a := by
  simp only [pullingMeas, Measurement.postprocess_comp, tildeM, tildeMMeasurement,
    decodeFq_pullingPoly, sub_dotProduct]

end

/-- Polynomial collision and deterministic decoding, before choosing a
register placement. This separates the finite probability calculation from
the six-register coordinate identities. -/
private theorem polynomial_decoding_defect_le_evaluated_add {P : AdmissibleParams}
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement (Poly P) I) (B : Measurement (Poly P) J)
    (psi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) :
    bipartiteDefect (uniformDistribution (PauliRegister P))
        (fun u => A.postprocess (fun g => dotProduct (decodeFq g) u))
        (fun u => B.postprocess (fun g => dotProduct (decodeFq g) u)) psi ≤
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (fun u => A.postprocess (fun g => evalPoly g u))
        (fun u => B.postprocess (fun g => evalPoly g u)) psi +
          (P.m * P.d : ℝ) / P.q := by
  have hcollision := SandwichProduct.point_codeword_defect_le_avg_evaluated_add
    A B psi evalPoly ((P.m * P.d : ℝ) / P.q) hpsi
    (by positivity) (fun g h hne => poly_eval_collision_le g h hne)
  have hpost (u : PauliRegister P) := consistencyDefect_postprocess_le
    (uniformDistribution Unit) (fun _ => A) (fun _ => B) psi
    (fun g => dotProduct (decodeFq g) u)
  simp only [consistencyDefect, avgOver_uniform_const,
    placed_product_stateQForm_eq] at hpost
  simp only [consistencyDefect, placed_product_stateQForm_eq]
  exact (avgOver_mono _ _ _ hpost).trans
    ((avgOver_uniform_const _).le.trans hcollision)

section

variable {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind)
include P epsilon deltaG S w W

/-- The last polynomial-collision step of the pulling argument, followed by
decoding. The field-measurement defect is bounded by the evaluated
difference-polynomial defect plus exactly `m * d / q`.

This is an unconditional comparison of two actual defects for the supplied
measurement. Bounding the evaluated defect from the witness's point
consistency remains the preceding steps of `eq:qld-pulling-cons`; no estimate
for that defect is assumed here. The state and placements are the original
six-register ones. -/
theorem tildeM_consistencyDefect_le_pulling_eval_add :
    consistencyDefect (uniformDistribution (PauliRegister P))
        (fun u a => S.placeSide .alice (tildeM w .alice W u a))
        (fun u a => S.placeSide .bob (tildeM w .bob W u a)) S.psiHat ≤
      consistencyDefect (uniformDistribution (PauliPoint P))
        (fun u a => S.placeSide .alice
          (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))
        S.psiHat + (P.m * P.d : ℝ) / P.q := by
  classical
  rw [S.consistencyDefect_placeSide, S.consistencyDefect_placeSide]
  have h := polynomial_decoding_defect_le_evaluated_add
      (pullingMeas w .alice W) (pullingMeas w .bob W)
      (reindexState S.extractionBlocks S.psiHat)
      (by rw [reindexState_norm_eq, S.psiHat_norm])
  simp_rw [← pullingMeas_postprocess_effect]
  exact h

/-- Observable consistency reduces to the evaluated difference-polynomial
defect. The coefficient four, uniform register average, and fixed basis
coordinate are exactly those of the established character conversion.
This estimate assumes no bound on the remaining evaluated defect. -/
theorem tildeObs_opDistSq_le_pulling_eval_add (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
        (fun u => S.placeSide .alice (tildeObs w .alice W u j))
        (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat ≤
      4 * (consistencyDefect (uniformDistribution (PauliPoint P))
        (fun u a => S.placeSide .alice
          (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))
        S.psiHat + (P.m * P.d : ℝ) / P.q) := by
  exact (tildeObs_opDistSq_le_four_consistencyDefect w W j).trans
    (mul_le_mul_of_nonneg_left (tildeM_consistencyDefect_le_pulling_eval_add w W)
      (by norm_num))

end

end

end MIPStarRE.QPBT
