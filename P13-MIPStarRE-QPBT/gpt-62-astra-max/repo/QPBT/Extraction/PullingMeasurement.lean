module

public import QPBT.Extraction.CharacterConsistency
public import QPBT.Extraction.EncodingSupport
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

variable {P : AdmissibleParams} {epsilon : ℝ} (outcome : Poly P × PauliRegister P) {deltaG : ℝ}
  {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG) (side : PlayerSide)
  (W : PauliKind)

/-- The outcome `g - g_h` in `eq:qld-pulling-12` is a bounded polynomial
representative, even when `g` is not in the encoding image. -/
def pullingPoly : Poly P :=
  outcome.1 - encodingPoly outcome.2

/-- Decoder linearity identifies the label in `eq:qld-pulling-12`. This uses
`Dec(g_h) = h`, never the reverse identity on arbitrary polynomials. -/
theorem decodeFq_pullingPoly :
    decodeFq (pullingPoly outcome) = decodeFq outcome.1 - outcome.2 := by
  have hsub (g h : Poly P) : decodeFq (g - h) = decodeFq g - decodeFq h := by
    funext y
    simp [decodeOn, decodeAt, evalPoly, MvPolynomial.eval_sub]
  rw [pullingPoly, hsub, decodeFq_lowDegreeEncoding]

/-- The projective measurement with polynomial outcomes `g - g_h` used to
organize the last step of the pulling argument. Its input witness remains
supplied; no global witness is constructed by this definition. -/
def pullingMeas :
    Measurement (Poly P) (ExtractionBlock P (S.LocalSpace side)) :=
  (tensorMeasurement (w.marginalPoly side W) (pauliRegisterMeas W)).postprocess pullingPoly

/-- Decoding the difference-polynomial measurement recovers `eq:tilde_M`
exactly. The equality holds on the full bounded polynomial carrier. -/
theorem pullingMeas_postprocess_effect (u : PauliRegister P) (a : PauliScalar P) :
    ((pullingMeas w side W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a =
      tildeM w side W u a := by
  classical
  rw [pullingMeas, Measurement.postprocess_comp]
  simp only [Measurement.postprocess_effect, Finset.sum_filter,
    decodeFq_pullingPoly, tensorMeasurement, Measurement.ofSumEqOne, pauliRegisterMeas]
  rw [Fintype.sum_prod_type]
  unfold tildeM tauDotProj bracketOp
  simp_rw [heteroKron_finset_sum_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  congr 1 with h
  have hlabel : dotProduct (decodeFq g - h) u = a ↔
      dotProduct h u = dotProduct (decodeFq g) u - a := by
    simp
    constructor <;> intro heq <;> linear_combination -heq
  simp only [hlabel]

/-- The coordinate change to two extraction blocks preserves the consistency
defect, including every off-diagonal outcome and the question distribution. -/
private theorem consistencyDefect_placeSide_eq
    {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    (S : ProjectiveSetting P epsilon) (mu : Distribution X)
    (left : X → A → Op (ExtractionBlock P (S.LocalSpace .alice)))
    (right : X → A → Op (ExtractionBlock P (S.LocalSpace .bob))) :
    consistencyDefect mu (fun x a => S.placeSide .alice (left x a))
        (fun x a => S.placeSide .bob (right x a)) S.psiHat =
      consistencyDefect mu (fun x a => heteroKron (left x a) 1)
        (fun x a => heteroKron 1 (right x a))
        (reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat) := by
  simp only [bipartiteDefect, consistencyDefect]
  apply avgOver_congr
  intro x
  congr 1 with a
  congr 1 with b
  by_cases hab : a = b
  · simp_all
  · simp only [if_neg, consistency_term_eq_stateQForm]
    rw [stateQForm_reindexState, reindexOp_mul]
    rfl

/-- Polynomial collision and deterministic decoding, before choosing a
register placement. This separates the finite probability calculation from
the six-register coordinate identities. -/
private theorem polynomial_decoding_defect_le_evaluated_add
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
  have hpost (u : PauliRegister P) := consistencyDefect_postprocess_le
    (uniformDistribution Unit) (fun _ => A) (fun _ => B) psi
    (fun g => dotProduct (decodeFq g) u)
  simp only [consistencyDefect, avgOver_uniform_const,
    consistency_term_eq_stateQForm, placed_product_stateQForm_eq] at hpost
  simp only [consistencyDefect, consistency_term_eq_stateQForm,
    placed_product_stateQForm_eq]
  exact (avgOver_mono _ _ _ hpost).trans
    ((avgOver_uniform_const _).le.trans (SandwichProduct.point_codeword_defect_le_avg_evaluated_add
      A B psi evalPoly ((P.m * P.d : ℝ) / P.q) hpsi
      (by positivity) (fun g h hne => poly_eval_collision_le g h hne)))

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
  simp [consistencyDefect_placeSide_eq]
  have h := polynomial_decoding_defect_le_evaluated_add
      (pullingMeas w .alice W) (pullingMeas w .bob W)
      (reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat)
      (by rw [reindexState_norm_eq, S.psiHat_norm])
  have hAlice :
      (fun u a => heteroKron (tildeM w .alice W u a)
        1) =
        fun u a => heteroKron
          (((pullingMeas w .alice W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a)
          (1 : Op (ExtractionBlock P S.toStrategy.ιB)) := by
    funext u a
    rw [pullingMeas_postprocess_effect]
  have hBob :
      (fun u a => heteroKron 1
        (tildeM w .bob W u a)) =
        fun u a => heteroKron (1 : Op (ExtractionBlock P S.toStrategy.ιA))
          (((pullingMeas w .bob W).postprocess (fun g => dotProduct (decodeFq g) u)).effect a) := by
    funext u a
    rw [pullingMeas_postprocess_effect]
  simp_all
  exact h

end

end MIPStarRE.QPBT
