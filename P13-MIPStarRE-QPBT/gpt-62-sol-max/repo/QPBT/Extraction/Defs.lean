module

public import QPBT.Observables.ExpandedDefs
public import QPBT.Games.Sandwich.Support

/-!
# Extraction foundations

This module defines the register identifications used to pull the Pauli
measurements apart. It retains the distinct local spaces of a
heterogeneous strategy, coarse-grains the generalized Pauli projectors by a
dot product, and records the state and error expressions needed by the later
extraction witness.

The binary phases use the existing `phaseSign`; the fixed field basis remains
the basis stored in `P.model` and is not re-quantified here.

## References

The Pauli dot-product projectors formalize blueprint
`def:tau-dot-product-projector`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429`.
The register and state helpers support blueprint `def:tilde-m-measurement`,
`def:v-swap-unitary`, and `lem:qld-unitary`, from paper lines 1429-1435 and
1666-1713.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Heterogeneous extraction registers -/

/-- One player's registers after adjoining the two generalized-Pauli
registers: `AA'A''` or `BB'B''`. This identifies the register order and spaces for
paper `14_analysis_of_the_pauli_basis_test.tex:1429-1435,1687-1713` and
blueprint `def:tilde-m-measurement` and `def:v-swap-unitary`. -/
abbrev ExtractionBlock (P : AdmissibleParams) (ι : Type*) :=
  (ι × PauliRegister P) × PauliRegister P

/-- The two heterogeneous extraction blocks in the order
`AA'A'' | BB'B''`. This is the block presentation of the existing `SixReg`
space used in blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
abbrev ExtractionRegisters (P : AdmissibleParams) (ιA ιB : Type*) :=
  ExtractionBlock P ιA × ExtractionBlock P ιB

/-- The auxiliary registers `AA'BB'` occurring before the extracted EPR
factor in blueprint `lem:qld-unitary`,
paper `14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
abbrev ExtractionAuxRegisters (P : AdmissibleParams) (ιA ιB : Type*) :=
  (ιA × PauliRegister P) × (ιB × PauliRegister P)

/-- Reassociate the six-register order with the two extraction blocks.
This equivalence identifies the register order in paper
`14_analysis_of_the_pauli_basis_test.tex:1429-1435,1687-1713`. -/
def sixRegExtractionEquiv (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃ ExtractionRegisters P ιA ιB where
  toFun p := (((p.1.1, p.1.2.1), p.1.2.2),
    ((p.2.1, p.2.2.1), p.2.2.2))
  invFun p := ((p.1.1.1, (p.1.1.2, p.1.2)),
    (p.2.1.1, (p.2.1.2, p.2.2)))
  left_inv p := by rfl
  right_inv p := by rfl

/-- Shuffle `AA'BB' | A''B''` into the six-register order. This equivalence
places the ideal state in the order used in blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
def extractionIdealShuffle (P : AdmissibleParams) (ιA ιB : Type*) :
    (ExtractionAuxRegisters P ιA ιB ×
      (PauliRegister P × PauliRegister P)) ≃ SixReg P ιA ιB where
  toFun p := ((p.1.1.1, (p.1.1.2, p.2.1)),
    (p.1.2.1, (p.1.2.2, p.2.2)))
  invFun p := (((p.1.1, p.1.2.1), (p.2.1, p.2.2.1)),
    (p.1.2.2, p.2.2.2))
  left_inv p := by rfl
  right_inv p := by rfl

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- Auxiliary register indices, in player order. -/
abbrev ExtractionAux (S : ProjectiveSetting P ε) := ExtractionAuxRegisters P S.toStrategy.ιA S.toStrategy.ιB

/-- Group the registers into the two local blocks. -/
abbrev extractionBlocks (S : ProjectiveSetting P ε) := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB

/-- Place the auxiliary/EPR coordinates in the expanded register order. -/
abbrev extractionShuffle (S : ProjectiveSetting P ε) := extractionIdealShuffle P S.toStrategy.ιA S.toStrategy.ιB

/-- Place an operator on one complete extraction block, with the identity on
the other player's block, as in the side-qualified operators of paper
`14_analysis_of_the_pauli_basis_test.tex:1429-1435,1687-1713`. -/
noncomputable def placeSide (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (ExtractionBlock P (S.LocalSpace side))) :
    Op (S.ExpandedSpace) := by
  cases side with
  | alice =>
      exact reindexOp
        S.extractionBlocks
        (heteroKron O 1)
  | bob =>
      exact reindexOp
        S.extractionBlocks
        (heteroKron 1 O)

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one (S : ProjectiveSetting P ε)
    (B : Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (heteroKron B (1 : Op (PauliRegister P))) = S.place .AA' B := by
  rw [place_eq_reindex]
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    placeSplit, aaBaBipartition, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl

/-- Placing a tensor with an identity on Bob's last register recovers `BB'`. -/
theorem placeSide_bob_tensor_one (S : ProjectiveSetting P ε)
    (B : Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (heteroKron B (1 : Op (PauliRegister P))) = S.place .BB' B := by
  rw [place_eq_reindex]
  ext row col
  simp [placeSide, sixRegExtractionEquiv, reindexOp, heteroKron, Matrix.kronecker,
    placeSplit, swapPaired, abBbBipartition, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> rfl

/-- Extraction block placement preserves finite sums. -/
theorem placeSide_finset_sum (S : ProjectiveSetting P ε) (side : PlayerSide)
    {I : Type*} (s : Finset I) (B : I → Op (ExtractionBlock P (S.LocalSpace side))) :
    S.placeSide side (∑ i ∈ s, B i) = ∑ i ∈ s, S.placeSide side (B i) := by
  cases side <;> ext row col <;>
    simp only [placeSide, heteroKron_finset_sum_left, heteroKron_finset_sum_right,
      reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]

/-- Place a complete measurement on a player's full extraction block. -/
noncomputable def blockMeasurement (S : ProjectiveSetting P ε) (side : PlayerSide)
    {α : Type*} [Fintype α] (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) :
    Measurement α (S.ExpandedSpace) := by
  let e := S.extractionBlocks
  letI : DecidableEq (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    instDecidableEqProd
  cases side
  · exact reindexMeasurement e (leftPlacedMeasurement A)
  · exact reindexMeasurement e (rightPlacedMeasurement A)

@[simp] theorem blockMeasurement_effect (S : ProjectiveSetting P ε) (side : PlayerSide)
    {α : Type*} [Fintype α] (A : Measurement α (ExtractionBlock P (S.LocalSpace side))) (a : α) :
    (S.blockMeasurement side A).effect a = S.placeSide side (A.effect a) := by
  cases side <;> rfl

/-- Placing a projective measurement on an extraction block preserves projectivity. -/
theorem blockMeasurement_isProjective (S : ProjectiveSetting P ε) (side : PlayerSide)
    {α : Type*} [Fintype α] (A : Measurement α (ExtractionBlock P (S.LocalSpace side)))
    (hA : Measurement.IsProjective A) : Measurement.IsProjective (S.blockMeasurement side A) := by
  let e := S.extractionBlocks
  letI : DecidableEq (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB) :=
    instDecidableEqProd
  cases side
  · exact reindexMeasurement_isProjective e _ (fun a =>
      MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker (hA a) (IsStarProjection.one _))
  · exact reindexMeasurement_isProjective e _ (fun a =>
      MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker (IsStarProjection.one _) (hA a))

/-- Lift an operator on a player's original strategy register to that player's
full extraction block. This places the Pauli and point measurements appearing
in blueprint `lem:qld-construct-the-paulis` and `lem:qld-unitary`. -/
noncomputable def onPlayer (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (S.LocalSpace side)) :
    Op (ExtractionBlock P (S.LocalSpace side)) :=
  heteroKron (heteroKron O 1) 1

/-- Place an operator on the original strategy register of the selected
player. This is the player-side placement used in blueprint
`lem:qld-unitary`. -/
noncomputable def placePlayer (S : ProjectiveSetting P ε) (side : PlayerSide)
    (O : Op (S.LocalSpace side)) :
    Op (S.ExpandedSpace) := by
  cases side with
  | alice => exact S.place .AA' (heteroKron O 1)
  | bob => exact S.place .BB' (heteroKron O 1)

/-- Place an operator on the selected extracted register `A''` or `B''`.
The unused strategy register in the crossed placement is assigned the
identity. This is the placement of the ideal Pauli operators in
blueprint `lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def placeExtractedRegister (S : ProjectiveSetting P ε)
    (side : PlayerSide) (O : Op (PauliRegister P)) :
    Op (S.ExpandedSpace) :=
  S.placeSide side (heteroKron (1 : Op (S.ExpandedLocalSpace side)) O)

/-- Place a pair of block operators simultaneously on `AA'A''` and
`BB'B''`. This is the simultaneous placement used for the transformed state in
blueprint `lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def placeBoth (S : ProjectiveSetting P ε)
    (VA : Op (ExtractionBlock P S.toStrategy.ιA))
    (VB : Op (ExtractionBlock P S.toStrategy.ιB)) :
    Op (S.ExpandedSpace) :=
  reindexOp S.extractionBlocks
    (heteroKron VA VB)

/-- The state `aux tensor EPR_q^{tensor M}` in the six-register order.
This is the ideal state in Item 1 of blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def idealExpState (S : ProjectiveSetting P ε)
    (aux : EuclideanSpace ℂ
      (S.ExtractionAux)) :
    EuclideanSpace ℂ (S.ExpandedSpace) := by
  classical
  exact
    reindexState S.extractionShuffle
      (vecTensor aux (eprState (PauliRegister P)))

end ProjectiveSetting

/-! ## Coarse-grained Pauli projectors -/

/-- Coarse-grain a finite operator family along a map of outcomes. This is the
operator-valued sum corresponding to `Measurement.postprocess`, used by
blueprint
`def:tau-dot-product-projector`. -/
noncomputable def bracketOp {α β ι : Type*} [Fintype α] [DecidableEq β]
    (N : α → Op ι) (f : α → β) (b : β) : Op ι :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), N a

/-- The projector obtained by measuring in basis `W` and retaining outcomes
whose dot product with `u` is `a`. This is Equation `eq:def-tauwu` in
blueprint
`def:tau-dot-product-projector`, paper
`14_analysis_of_the_pauli_basis_test.tex:1426-1429`. -/
noncomputable def tauDotProj {P : AdmissibleParams} (W : PauliKind)
    (u : PauliRegister P) (a : PauliScalar P) : Op (PauliRegister P) :=
  bracketOp (pauliProj W) (fun h => dotProduct h u) a

/-! ## Conjugation and extraction error -/

/-- Conjugation of an operator by a square matrix, as used in the exact
conjugation equations in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1713`. -/
noncomputable def conjBy {ι : Type*} [Fintype ι]
    (V N : Op ι) : Op ι :=
  V * N * Vᴴ

/-- The common error scale for constructing the pulled-apart measurements from
a global polynomial-pair witness. Here `deltaG` is its consistency error. The
remaining terms record the point-measurement transfer
and the Schwartz--Zippel loss; when `0 ≤ epsilon ≤ 1`, `sqrt epsilon` also
dominates terms of order `epsilon`.

This makes explicit the enlargement of the error called `deltaS` in
blueprint
`lem:qld-construct-the-paulis`, paper
`14_analysis_of_the_pauli_basis_test.tex:1458-1605`. -/
noncomputable def deltaConstructPaulis (C epsilon deltaG : ℝ)
    (m d q : ℕ) : ℝ :=
  C * (deltaG + Real.sqrt epsilon +
    ((m * d : ℕ) : ℝ) / (q : ℝ))

/-- The explicit extraction scale
`C * (deltaS^(1/4) + md/q)` from blueprint
`lem:qld-unitary`, paper
`14_analysis_of_the_pauli_basis_test.tex:1666-1685`. -/
noncomputable def deltaExtract (C deltaS : ℝ) (m d q : ℕ) : ℝ :=
  C * (Real.rpow deltaS (1 / 4 : ℝ) + ((m * d : ℕ) : ℝ) / (q : ℝ))

end

end MIPStarRE.QPBT
