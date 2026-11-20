module

public import QPBT.Extraction.Consistency
public import QPBT.Extraction.EPRState
public import QPBT.Extraction.Bounds
public import QPBT.Extraction.StateExtraction
public import QPBT.Extraction.PauliComparison
public import QPBT.Extraction.EvaluatedPauliConsistency
public import QPBT.Extraction.ConcretePauliComparison
public import QPBT.Combining.QldEnvelope

/-!
# Extraction by the swap unitaries

The concrete swap operators below yield the Pauli extraction conclusion. The
local maps are constructed from the global polynomial
measurements, and all operators retain the heterogeneous Alice and Bob
placements. The generalized Pauli projectors use the field and basis fixed by
`P.model`.

## References

The extraction witness records the conclusion of blueprint `lem:qld-unitary`,
from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
The error-form comparison formalizes `lem:qld-extraction-error-form` and
supports `rem:pauli-robustness-form` in the blueprint; its paper source is
lines 1855-1858 and 1868-1876.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-- The concrete conclusion of `lem:qld-unitary`: the two swap maps extract an
EPR state and conjugate each player's total Pauli measurement to the canonical
Pauli projectors. The answer sum in `pauli_close` is over
`PauliRegister P`; the uniform distribution on `Unit` records that there is no
average over questions.

Blueprint `lem:qld-unitary`; paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685,1827-1859`. The swap maps
are `swapUnitary w .alice` and `swapUnitary w .bob`, defined from the
side-indexed global measurements, and use only the basis fixed by `P.model`.
-/
structure ExtractionWitness {P : AdmissibleParams} {epsilon deltaS : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaS)
    (delta : ℝ) where
  /-- The auxiliary state on registers `AA'BB'`. -/
  aux : EuclideanSpace ℂ
    (S.ExtractionAux)
  /-- The auxiliary state is normalized. -/
  aux_norm : ‖aux‖ = 1
  /-- Applying both concrete swap maps to the expanded state extracts the ideal
  auxiliary-state/EPR tensor product. -/
  state_close :
    ‖S.swappedState w -
        S.idealExpState aux‖ ^ 2 ≤ delta
  /-- On the ideal extracted state, conjugated total-Pauli effects are close to
  the canonical projectors, for both players and both Pauli bases. -/
  pauli_close : ∀ (side : PlayerSide) (W : PauliKind),
    S.swapPauliDistance w aux side W ≤ delta

/-- Construct a conditional extraction witness when the allowed squared error
is at least four. The auxiliary vector is the normalized original state tensored
with EPR on the auxiliary registers. Both distances are bounded independently
of the dimensions and the number of Pauli answers.

**Scope restriction:** This proves the large-error case of blueprint
`lem:qld-unitary`, paper `14_analysis_of_the_pauli_basis_test.tex:1666-1860`,
as required by the normalization correction in
`docs/paper-gaps/qpbt_extraction-transfer.tex`. It does not assert the small-error
case or construction of the supplied global witness.

**Unfaithful:** The global measurement is supplied as `GlobalPairWitness`,
rather than constructed from `lem:qld-4-7`. The discrepancy and planned
composition with `exists_globalPairWitness` are recorded in
`docs/paper-gaps/qpbt_extraction-transfer.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#123. The
source-facing
composition is `exists_extractionWitness`. -/
theorem exists_extractionWitness_ofGlobalPairWitness_of_four_le
    {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
    (hdelta : 4 ≤ delta) : Nonempty (ExtractionWitness S w delta) := by
  refine ⟨{
    aux := S.extractionAuxReference
    aux_norm := S.extractionAuxReference_norm
    state_close := ?_
    pauli_close := ?_
  }⟩
  · have hnorm := norm_sub_le
      (S.swappedState w)
      (S.idealExpState S.extractionAuxReference)
    rw [S.swappedState_norm w, S.idealExpState_norm,
      S.extractionAuxReference_norm] at hnorm
    nlinarith [norm_nonneg
      (S.swappedState w -
        S.idealExpState S.extractionAuxReference)]
  · intro side W
    exact (S.extraction_pauli_dist_le_four w S.extractionAuxReference
      S.extractionAuxReference_norm side W).trans hdelta

/-- At construction error at least one, a universal extraction constant at
least four suffices for the complete witness. This is the large-error branch
at the unchanged nested scale of `exists_extractionWitness_ofGlobalPairWitness`.

**Scope restriction:** Only the region where `deltaConstructPaulis` is at least
one is covered. See the normalization correction in
`docs/paper-gaps/qpbt_extraction-transfer.tex` for blueprint `lem:qld-unitary`,
paper `14_analysis_of_the_pauli_basis_test.tex:1743-1783`.

**Unfaithful:** The proof uses the supplied-witness helper
`exists_extractionWitness_ofGlobalPairWitness_of_four_le`. The global-witness
construction is supplied by `exists_globalPairWitness` in the source-facing
`exists_extractionWitness`; see issue Dengnifer/MIPStarRE-QPBT-bak#123 and
`docs/paper-gaps/qpbt_extraction-transfer.tex`. -/
theorem exists_extractionWitness_ofGlobalPairWitness_of_one_le_construct
    {P : AdmissibleParams} {epsilon deltaG C : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
    (hC : 4 ≤ C)
    (hconstruct : 1 ≤ deltaConstructPaulis C epsilon deltaG P.m P.d P.q) :
    Nonempty (ExtractionWitness S w
      (deltaExtract C (deltaConstructPaulis C epsilon deltaG P.m P.d P.q) P.m P.d P.q)) := by
  apply exists_extractionWitness_ofGlobalPairWitness_of_four_le S w
  have hroot := Real.one_le_rpow hconstruct (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hratio : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ) := by positivity
  unfold deltaExtract
  exact hC.trans (le_mul_of_one_le_right (by linarith)
    (hroot.trans (le_add_of_nonneg_right hratio)))

/-- Conditional extraction for the concrete swap maps at the explicit scale
obtained by applying `deltaExtract` to `deltaConstructPaulis`. Given a
`GlobalPairWitness`, it supplies the extraction data appearing in
blueprint `lem:qld-unitary` and paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1860`.

**Unfaithful:** This result assumes `w : GlobalPairWitness S deltaG`, which is
derived inside `lem:qld-unitary` rather than assumed by the paper statement.
The discrepancy is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex`. Elimination: obtain `w` from
`exists_globalPairWitness` before applying this conditional extraction result;
`exists_extractionWitness` performs that composition under issue Dengnifer/MIPStarRE-QPBT-bak#123.

**Local fix:** the positive-contraction estimate and normalization case split
repair the two numerical defects at paper lines 1743-1783 without changing the
conclusion; see `docs/paper-gaps/qpbt_extraction-transfer.tex`.

The auxiliary state is supplied by `exists_extraction_aux_ofGlobalPairWitness`.
The two evaluated consistency bounds are transported by the concrete swaps in
`ProjectiveSetting.extraction_pauli_dist_le`. Choose one universal constant
above both construction coefficients and eighteen, and use
`extraction_small_error_absorption` when the construction error is at most one.
The complete large-error witness covers the other case. Thus every supplied
global polynomial-pair witness yields a normalized auxiliary state, the
transformed-state estimate, and both total-Pauli comparison bounds. This result
neither constructs the global witness nor passes from the swap unitaries to the
isometries of the source theorem. -/
theorem exists_extraction_witness_of_global_pair_witness_explicit
    (P : AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG) :
    Nonempty (ExtractionWitness S w
      (deltaExtract pauliBaselineExtractionConstant
        (deltaConstructPaulis pauliBaselineExtractionConstant
          epsilon deltaG P.m P.d P.q) P.m P.d P.q)) := by
  let C : ℝ := pauliBaselineExtractionConstant
  have hCE_C : 2 + 4 * Real.sqrt 172 ≤ C := by
    have hroot := Real.sqrt_nonneg (172 : ℝ)
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 172)
    dsimp [C, pauliBaselineExtractionConstant]
    nlinarith
  have hC18 : 18 ≤ C := by
    dsimp [C, pauliBaselineExtractionConstant]
    norm_num
  let delta := deltaConstructPaulis C epsilon deltaG P.m P.d P.q
  have hmono (K : ℝ) (hK : K ≤ C) :
      deltaConstructPaulis K epsilon deltaG P.m P.d P.q ≤ delta :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have hdelta : 0 ≤ delta := by
    dsimp [delta, C, deltaConstructPaulis, pauliBaselineExtractionConstant]
    positivity
  by_cases hdelta_one : delta ≤ 1
  · obtain ⟨aux, haux, hclose⟩ :=
      exists_extraction_aux_of_global_pair_witness_explicit
        P epsilon deltaG hepsilon hepsilon_one hdeltaG S w
    have hstate_delta :
        ‖S.swappedState w -
          S.idealExpState aux‖ ^ 2 ≤ 16 * delta :=
      hclose
    have hnorm :
        ‖S.swappedState w -
          S.idealExpState aux‖ ≤ 4 * Real.sqrt delta := by
      nlinarith [Real.sq_sqrt hdelta, Real.sqrt_nonneg delta, norm_nonneg
        (S.swappedState w -
          S.idealExpState aux)]
    have habsorb := extraction_small_error_absorption C delta P.m P.d P.q
      hC18 hdelta hdelta_one
    refine ⟨{
      aux := aux
      aux_norm := haux
      state_close := hstate_delta.trans habsorb.1
      pauli_close := ?_
    }⟩
    intro side W
    have hdefect := (evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
      hepsilon hepsilon_one hdeltaG S w side W).trans (hmono _ hCE_C)
    apply (S.extraction_pauli_dist_le w aux haux side W).trans
    apply le_trans _ habsorb.2
    push_cast
    linarith
  · exact exists_extractionWitness_ofGlobalPairWitness_of_one_le_construct S w
      (by linarith) (le_of_lt (lt_of_not_ge hdelta_one))

/-- A universal constant guarantees an extraction witness at the composed
construction-and-extraction error. -/
theorem exists_extractionWitness_ofGlobalPairWitness :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (P : AdmissibleParams) (epsilon deltaG : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
          ∀ (S : ProjectiveSetting P epsilon)
            (w : GlobalPairWitness S deltaG),
            Nonempty
              (ExtractionWitness S w
                (deltaExtract C
                  (deltaConstructPaulis C epsilon deltaG P.m P.d P.q)
                  P.m P.d P.q)) := by
  refine ⟨pauliBaselineExtractionConstant, ?_, ?_⟩
  · unfold pauliBaselineExtractionConstant
    norm_num
  · exact exists_extraction_witness_of_global_pair_witness_explicit

section

variable (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1)
include C a b hC ha hb hb1

/-- Every admissible input coefficient and exponent yield new universal constants
that bound the composed extraction error by an error of `deltaQld` form. -/
theorem deltaExtract_le_deltaQld :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        epsilon ≤ 1 →
        deltaExtract C
            (deltaConstructPaulis C epsilon
              (P.qldError a b epsilon) P.m P.d P.q)
            P.m P.d P.q ≤
          P.qldError a' b' epsilon := by
  have hG : QldInput.domain.Polynomial (fun w => w.1.qldError a b w.error) := by
    simpa only [AdmissibleParams.qldError, deltaQld, Real.rpow_eq_pow] using
      QldInput.polynomial_soundness QldInput.polynomial_error (fun w => w.1.degreeBudget) (C := 1)
        zero_le_one (zero_le_one.trans ha.le) hb (fun _ => ⟨le_rfl, by simp⟩)
  have hc := ((hG.add QldInput.polynomial_error.sqrt).add QldInput.polynomial_ratio).scale
    (zero_le_one.trans hC)
  have he := ((hc.rpow (p := 1 / 4) (by norm_num)).add QldInput.polynomial_ratio).scale
    (zero_le_one.trans hC)
  obtain ⟨A, B, hA, hB, hB1, h⟩ := QldInput.exists_qldEnvelope he
  exact ⟨A, B, hA.le, hB, hB1, fun P e he₀ he₁ => h (P, ⟨e, he₀, he₁⟩)⟩

end

end

end MIPStarRE.QPBT
