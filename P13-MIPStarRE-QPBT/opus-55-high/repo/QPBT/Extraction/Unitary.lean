module

public import QPBT.Extraction.Consistency
public import QPBT.Extraction.EPRState
public import QPBT.Extraction.Bounds
public import QPBT.Extraction.StateExtraction
public import QPBT.Extraction.PauliComparison
public import QPBT.Extraction.EvaluatedPauliConsistency
public import QPBT.Extraction.ConcretePauliComparison
public import QPBT.Test.SoundnessDefs

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
  /-- Each swap map is a left unitary. -/
  swap_left_unitary : ∀ side : PlayerSide,
    (swapUnitary w side)ᴴ * swapUnitary w side = 1
  /-- The auxiliary state on registers `AA'BB'`. -/
  aux : EuclideanSpace ℂ
    (ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB)
  /-- The auxiliary state is normalized. -/
  aux_norm : ‖aux‖ = 1
  /-- Applying both concrete swap maps to the expanded state extracts the ideal
  auxiliary-state/EPR tensor product. -/
  state_close :
    ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState aux‖ ^ 2 ≤ delta
  /-- On the ideal extracted state, conjugated total-Pauli effects are close to
  the canonical projectors, for both players and both Pauli bases. -/
  pauli_close : ∀ (side : PlayerSide) (W : PauliKind),
    opFamilyDistSq (uniformDistribution Unit)
      (fun (_ : Unit) (h : PauliRegister P) =>
        conjBy (S.placeSide side (swapUnitary w side))
          (S.placePlayer side ((S.pauliMeas side W).effect h)))
      (fun (_ : Unit) (h : PauliRegister P) =>
        S.placeExtractedRegister side (pauliProj W h))
      (S.idealExpState aux) ≤ delta

variable {P : AdmissibleParams}

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
    {epsilon deltaG delta : ℝ}
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
    (hdelta : 4 ≤ delta) : Nonempty (ExtractionWitness S w delta) := by
  refine ⟨{
    swap_left_unitary := conjTranspose_mul_swapUnitary w
    aux := S.extractionAuxReference
    aux_norm := S.extractionAuxReference_norm
    state_close := ?_
    pauli_close := ?_
  }⟩
  · have hnorm := norm_sub_le
      (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat)
      (S.idealExpState S.extractionAuxReference)
    rw [S.applyBoth_swap_norm w, S.idealExpState_norm,
      S.extractionAuxReference_norm] at hnorm
    nlinarith [norm_nonneg
      (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState S.extractionAuxReference)]
  · intro side W
    exact (S.extraction_pauli_dist_le_four w S.extractionAuxReference
      S.extractionAuxReference_norm side W).trans hdelta

/-- A universal constant guarantees an extraction witness at the composed
construction-and-extraction error. The auxiliary state is supplied by
`exists_extraction_aux_of_global_pair_witness_explicit`; when the construction
error is at most one, `extraction_small_error_absorption` absorbs the error
terms, and otherwise the complete large-error witness applies. -/
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
  have hCE_C : 2 + 4 * Real.sqrt 172 ≤ pauliBaselineExtractionConstant := by
    dsimp [pauliBaselineExtractionConstant]
    nlinarith [Real.sqrt_nonneg (172 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 172)]
  have hC18 : 18 ≤ pauliBaselineExtractionConstant := by
    dsimp [pauliBaselineExtractionConstant]
    norm_num
  refine ⟨_, by linarith, fun P epsilon deltaG hepsilon hepsilon_one hdeltaG S w => ?_⟩
  have hmono : deltaConstructPaulis (2 + 4 * Real.sqrt 172) epsilon deltaG P.m P.d P.q ≤
      deltaConstructPaulis _ epsilon deltaG P.m P.d P.q :=
    mul_le_mul_of_nonneg_right hCE_C (by positivity)
  set δ := deltaConstructPaulis pauliBaselineExtractionConstant epsilon deltaG P.m P.d P.q
  have hdelta : 0 ≤ δ := by
    dsimp [δ, deltaConstructPaulis]
    positivity
  by_cases hdelta_one : δ ≤ 1
  · obtain ⟨aux, haux, hclose⟩ :=
      exists_extraction_aux_of_global_pair_witness_explicit
        P epsilon deltaG hepsilon hepsilon_one hdeltaG S w
    have habsorb := extraction_small_error_absorption _ _ P.m P.d P.q hC18 hdelta hdelta_one
    refine ⟨{
      swap_left_unitary := conjTranspose_mul_swapUnitary w
      aux := aux
      aux_norm := haux
      state_close := hclose.trans habsorb.1
      pauli_close := fun side W => (S.extraction_pauli_dist_le w aux haux side W).trans
        (le_trans ?_ habsorb.2)
    }⟩
    have he := evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
      P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W
    have hdefect : S.evaluatedPauliDefect w side W ≤ δ := by
      cases side
      exacts [he.1.trans hmono, he.2.trans hmono]
    push_cast
    nlinarith [Real.sq_sqrt hdelta, Real.sqrt_nonneg δ, norm_nonneg
      (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat - S.idealExpState aux)]
  · apply exists_extractionWitness_ofGlobalPairWitness_of_four_le S w
    exact (by linarith : (4 : ℝ) ≤ _).trans (le_mul_of_one_le_right (by linarith)
      ((Real.one_le_rpow (le_of_not_ge hdelta_one) (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans
        (le_add_of_nonneg_right (by positivity))))

variable (C a b : ℝ)

/-- The composed construction and extraction errors preserve the error family
of `thm:pauli`: when `deltaG` has the form
`deltaQld a b epsilon m d q`, the result is bounded by another member of that
family after decreasing the exponent and enlarging the universal constant.

This is `lem:qld-extraction-error-form` in the blueprint and the named
quantitative obligation behind `rem:pauli-robustness-form`; the concluding
paper comparison is at
`14_analysis_of_the_pauli_basis_test.tex:1855-1858,1868-1876`.

One may take `a' = 4 * C^2 * a` and `b' = b / 8`. Subadditivity of the
fourth root bounds the three construction terms separately. Admissibility
gives `md ≥ 1` and `q ≥ 1`, so their polynomial factors and the term `md/q`
are absorbed into the enlarged prefactor. This discharges the scalar
estimate tracked by issue Dengnifer/MIPStarRE-QPBT-bak#241. -/
theorem deltaExtract_le_deltaQld (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        epsilon ≤ 1 →
        deltaExtract C
            (deltaConstructPaulis C epsilon
              (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
            P.m P.d P.q ≤
          deltaQld a' b' epsilon P.m P.d P.q := by
  have hconstant : a ≤ 4 * C ^ 2 * a := by nlinarith [mul_le_mul hC hC zero_le_one (by linarith : (0:ℝ) ≤ C)]
  refine ⟨4 * C ^ 2 * a, b / 8, ha.le.trans hconstant, by positivity, by linarith,
    fun P ε he0 he1 => ?_⟩
  have hn : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hq : (1 : ℝ) ≤ P.q := by exact_mod_cast one_le_two.trans P.hq.two_le
  simp only [deltaExtract, deltaConstructPaulis, deltaQld, Real.rpow_eq_pow, Real.sqrt_eq_rpow]
  generalize ((P.m * P.d : ℕ) : ℝ) = n at hn ⊢
  generalize (P.q : ℝ) = q at hq ⊢
  have hA : 1 ≤ a * n ^ a := one_le_mul_of_one_le_of_one_le ha.le (Real.one_le_rpow hn (by linarith))
  have hnA : n ≤ a * n ^ a :=
    (Real.self_le_rpow_of_one_le hn ha.le).trans (le_mul_of_one_le_left (by positivity) ha.le)
  have hs : (ε ^ (b / 2) + q ^ (-(b / 2)) + 2 ^ (-(b * n / 2))) ^ (1 / 4 : ℝ) ≤
      ε ^ (b / 8) + q ^ (-(b / 8)) + 2 ^ (-(b / 8 * n)) := by
    refine ((Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by norm_num)
      (by norm_num)).trans (add_le_add (Real.rpow_add_le_add_rpow (by positivity) (by positivity)
        (by norm_num) (by norm_num)) le_rfl)).trans (le_of_eq ?_)
    rw [← Real.rpow_mul he0, ← Real.rpow_mul (by linarith), ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hR := add_le_add (add_le_add
    (Real.rpow_le_rpow_of_exponent_ge' he0 he1 (by positivity : 0 ≤ b / 2) (by linarith : b / 2 ≤ b))
    (Real.rpow_le_rpow_of_exponent_le hq (by linarith : -b ≤ -(b / 2))))
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by nlinarith : -(b * n) ≤ -(b * n / 2)))
  have h2 := Real.rpow_le_rpow_of_exponent_ge' he0 he1 (by positivity : 0 ≤ b / 2)
    (by linarith : b / 2 ≤ 1 / 2)
  have h4 := Real.rpow_le_rpow_of_exponent_le hq (by linarith : (-1 : ℝ) ≤ -(b / 2))
  have h6 := Real.rpow_le_rpow_of_exponent_le hq (by linarith : (-1 : ℝ) ≤ -(b / 8))
  have p1 : 0 ≤ ε ^ (b / 2) := by positivity
  have p2 : 0 ≤ q ^ (-(b / 2)) := by positivity
  have p3 : 0 ≤ (2 : ℝ) ^ (-(b * n / 2)) := by positivity
  have p4 : 0 ≤ ε ^ (b / 8) := by positivity
  have p5 : 0 ≤ q ^ (-(b / 8)) := by positivity
  have p6 : 0 ≤ (2 : ℝ) ^ (-(b / 8 * n)) := by positivity
  rw [Real.rpow_neg_one] at h4 h6
  simp only [div_eq_mul_inv n q]
  set s := ε ^ (b / 2) + q ^ (-(b / 2)) + 2 ^ (-(b * n / 2))
  set r := ε ^ (b / 8) + q ^ (-(b / 8)) + 2 ^ (-(b / 8 * n))
  set A := a * n ^ a
  have hX := mul_le_mul_of_nonneg_left (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ A))
    (h2.trans ((by linarith : _ ≤ s).trans (le_mul_of_one_le_left (by positivity) hA))))
    (mul_le_mul hnA (h4.trans (by linarith : _ ≤ s)) (by positivity) (by positivity)))
    (by linarith : 0 ≤ C)
  have h11 : (C * (A * s + A * s + A * s)) ^ (1 / 4 : ℝ) ≤ 3 * C * A * r := by
    rw [show C * (A * s + A * s + A * s) = 3 * C * A * s by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    exact mul_le_mul (Real.rpow_le_self_of_one_le (by nlinarith) (by norm_num)) hs (by positivity)
      (by positivity)
  have h12 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hconstant)
    (by positivity : 0 ≤ 4 * C ^ 2 * a * r)
  have h13 := mul_le_mul_of_nonneg_right (by nlinarith : C * (3 * C + 1) ≤ 4 * C ^ 2)
    (by positivity : 0 ≤ A * r)
  have h14 := (Real.rpow_le_rpow (by positivity) hX (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans h11
  have h15 := mul_le_mul hnA (h6.trans (by linarith : _ ≤ r)) (by positivity) (by positivity)
  nlinarith

end

end MIPStarRE.QPBT
