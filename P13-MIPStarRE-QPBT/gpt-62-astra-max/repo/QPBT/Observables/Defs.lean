module

public import QPBT.Games.Sandwich.Support
public import QPBT.Observables.LineDefs
public import QPBT.Test.PauliBasisTest

/-!
# Typed strategy measurements and point observables

This file fixes a projective, possibly heterogeneous strategy for the Pauli
basis test and extracts the typed measurement families used in the analysis.
Malformed answers are folded into a fixed valid answer, so the extracted
families remain complete measurements. The winning hypothesis bounds their
original wrong-form mass by the rejection probability. `Option` is used only
for the completed line-evaluation classes.

## References

The ambient strategy convention and the observable `W^r(u)` are in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`,
corresponding to blueprint `def:strategy-observables`. The typed question
and answer forms come from blueprint `def:pauli-question-distribution` and
`def:pauli-win-predicate`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Coefficient outcomes for diagonal lines of the Pauli test. -/
abbrev PauliLinePoly (P : AdmissibleParams) := DegPoly P.toLdParams (P.m * P.d)

/-- The two local registers of a heterogeneous bipartite strategy. This is
formalization-only indexing for the player-dependent notation at paper
`14_analysis_of_the_pauli_basis_test.tex:160-190`. -/
inductive PlayerSide where
  | alice
  | bob
  deriving DecidableEq, Repr, Inhabited

/-- A projective strategy satisfying the winning premise used throughout
Section `sec:commutation`. The structure retains the distinct player spaces and
measurement families of `Strategy`. Paper
`14_analysis_of_the_pauli_basis_test.tex:160-172`; blueprint
`sec:commutation`. -/
structure ProjectiveSetting (P : AdmissibleParams) (ε : ℝ) where
  toStrategy : Strategy (pauliBasisTest P)
  isProjective : toStrategy.IsProjective
  win : 1 - ε ≤ toStrategy.value

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

section

variable (S : ProjectiveSetting P ε)

/-- The local Hilbert-space index type on a specified player side. It indexes
the side-qualified operators at paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`. -/
@[reducible] def LocalSpace : PlayerSide → Type
  | .alice => S.toStrategy.ιA
  | .bob => S.toStrategy.ιB

instance localSpaceFintype (side : PlayerSide) :
    Fintype (S.LocalSpace side) := by
  cases side <;> simp only [LocalSpace] <;> infer_instance

instance localSpaceDecidableEq (side : PlayerSide) :
    DecidableEq (S.LocalSpace side) := by
  cases side <;> simp only [LocalSpace] <;> infer_instance

/-- Select the strategy measurement before outcome postprocessing on one
player side. This is the heterogeneous interpretation of the shared symbol `M` at
paper `14_analysis_of_the_pauli_basis_test.tex:160-184`. -/
def strategyMeasurement (side : PlayerSide)
    (question : PauliQuestion P) :
    Measurement (PauliAnswer P) (S.LocalSpace side) := by
  cases side with
  | alice => exact S.toStrategy.A question
  | bob => exact S.toStrategy.B question

end

section

variable (P : AdmissibleParams)

/-- Embed a point into the full Pauli question space in basis `W`. This is the
point-question content from `def:pauli-question-distribution`, paper
`08_classical_and_quantum_low_degree_tests.tex:997-1008`, blueprint
`def:pauli-question-distribution`. -/
def contentOfPoint (W : PauliKind)
    (u : PauliPoint P) : PauliSpace P :=
  embedLd P W fun i =>
    match i with
    | .inl (.inl j) => u j
    | .inl (.inr _) => 0
    | .inr _ => 0

/-- Embed a canonical line description into the full Pauli question space.
Axis lines clear the direction block, whereas diagonal lines retain their
canonical projected direction. Paper
`08_classical_and_quantum_low_degree_tests.tex:997-1008`; blueprint
`def:pauli-question-distribution` and `rem:deg-line-representatives`. -/
def contentOfLine (W : PauliKind)
    (line : LineDesc P.toLdParams) : PauliSpace P :=
  embedLd P W fun i =>
    match i with
    | .inl (.inl j) => line.base j
    | .inl (.inr _) => line.seed
    | .inr j =>
        match line with
        | .axis _ _ _ => 0
        | .diagonal _ _ direction _ _ => direction j

/-- Fill the point, scalar, and phase blocks shared by Pair, Pair/W, and Magic
Square questions. This is the type-4 content of
`def:pauli-question-distribution`, paper
`08_classical_and_quantum_low_degree_tests.tex:1030-1120`, blueprint
`def:pauli-question-distribution`. -/
def contentOfTuple
    (uX uZ : PauliPoint P) (rX rZ : PauliScalar P) : PauliSpace P :=
  fun i =>
    match i with
    | .inl (.inl (.inl (.inl (.inl j)))) => uX j
    | .inl (.inl (.inl (.inl (.inr j)))) => uZ j
    | .inl (.inl (.inl (.inr _))) => 0
    | .inl (.inl (.inr _)) => 0
    | .inl (.inr _) => rX
    | .inr _ => rZ

/-- The typed point question in basis `W`, from the strategy notation at paper
`14_analysis_of_the_pauli_basis_test.tex:174-190` and
blueprint `def:pauli-question-distribution`. -/
def pointQuestion (W : PauliKind)
    (u : PauliPoint P) : PauliQuestion P :=
  (.point W, contentOfPoint P W u)

/-- The typed axis or diagonal line question represented by a canonical
`LineDesc`. Paper `14_analysis_of_the_pauli_basis_test.tex:174-184`; blueprint
`def:strategy-observables` and `rem:deg-line-representatives`. -/
def lineQuestion (W : PauliKind)
    (line : LineDesc P.toLdParams) : PauliQuestion P :=
  match line.kind with
  | .axis => (.aline W, contentOfLine P W line)
  | .diagonal => (.dline W, contentOfLine P W line)

/-- The typed Pair question for a tuple `(u_X,u_Z,r_X,r_Z)`. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-249`; blueprint
`lem:qld-win-implications`. -/
def pairQuestion
    (uX uZ : PauliPoint P) (rX rZ : PauliScalar P) : PauliQuestion P :=
  (.pair, contentOfTuple P uX uZ rX rZ)

/-- The typed Pair/W question for a tuple `(u_X,u_Z,r_X,r_Z)`. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-249`; blueprint
`lem:qld-win-implications`. -/
def pairWQuestion (W : PauliKind)
    (uX uZ : PauliPoint P) (rX rZ : PauliScalar P) : PauliQuestion P :=
  (.pairW W, contentOfTuple P uX uZ rX rZ)

/-- The typed Magic Square question for a tuple `(u_X,u_Z,r_X,r_Z)`. Paper
`14_analysis_of_the_pauli_basis_test.tex:213-258`; blueprint
`lem:qld-win-implications`. -/
def msQuestion (t : MsType)
    (uX uZ : PauliPoint P) (rX rZ : PauliScalar P) : PauliQuestion P :=
  (.ms t, contentOfTuple P uX uZ rX rZ)

end

-- The support rewrites below elaborate the `Fintype` instance of
-- `PauliEdge × PauliSpace P`, whose nested sigma/sum instance chain exceeds the
-- default recursion depth.

/-- Fold every non-point answer into the fixed point answer `0`. This realizes
the typed point family without adding a bottom outcome; wrong-form mass remains
visible through `wrongFormEffect`. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`; blueprint
`def:strategy-observables`. -/
def pointAnswerOrZero {P : AdmissibleParams} : PauliAnswer P → PauliScalar P
  | .value a => a
  | _ => 0

/-- Fold every answer not prescribed for `line` into the zero coefficient
list. Axis answers are padded from degree `d` to degree `m*d`. This realizes
the coefficient convention of `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-62`, blueprint
`def:ideg-deg-polynomials`. -/
def lineAnswerOrZero {P : AdmissibleParams} (line : LineDesc P.toLdParams) :
    PauliAnswer P → PauliLinePoly P :=
  match line with
  | .axis _ _ _ => fun answer =>
      match answer with
      | .alinePoly f =>
          DegPoly.padTo (Nat.le_mul_of_pos_left P.d (Nat.zero_lt_of_lt P.one_le_m)) f
      | _ => 0
  | .diagonal _ _ _ _ _ => fun answer =>
      match answer with
      | .dlinePoly f => f
      | _ => 0

section

variable {P : AdmissibleParams}

/-- Fold every non-Pair answer into `(0,0)`. This is the complete typed Pair
family used in items 4 and 6 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-258`. -/
def pairAnswerOrZero : PauliAnswer P → ZMod 2 × ZMod 2
  | .pairBits bits => bits
  | _ => (0, 0)

/-- Fold every non-Pair/W answer into bit `0`. This is the complete typed
Pair/W family used in items 4 and 7 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-263`. -/
def pairWAnswerOrZero : PauliAnswer P → ZMod 2
  | .bit bit => bit
  | _ => 0

/-- Fold wrong-form Pauli-test answers into a fixed valid Magic Square answer
of the requested question type. This supplies the typed families needed for an
actual `Strategy msGame`; paper
`14_analysis_of_the_pauli_basis_test.tex:213-258`, blueprint
`lem:qld-win-implications`. -/
def msAnswerOrZero (t : MsType) : PauliAnswer P → MsAnswer :=
  match t with
  | .constraint _ => fun answer =>
      match answer with
      | .msTriple bits => .triple bits
      | _ => .triple 0
  | .var _ => fun answer =>
      match answer with
      | .bit bit => .bit bit
      | _ => .bit 0

end

section

variable (S : ProjectiveSetting P ε) (side : PlayerSide)

/-- The complete typed point measurement on one player side. It is the
corresponding strategy measurement postprocessed by `pointAnswerOrZero`; paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
noncomputable def pointMeas
    (W : PauliKind) (u : PauliPoint P) :
    Measurement (PauliScalar P) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pointQuestion P W u)).postprocess pointAnswerOrZero

/-- The complete typed line measurement on one player side, uniformly indexed
by degree-`m*d` coefficient lists. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-184`; blueprint
`def:ideg-deg-polynomials` and `lem:qld-win-implications`. -/
noncomputable def lineMeas
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    Measurement (PauliLinePoly P) (S.LocalSpace side) :=
  (S.strategyMeasurement side (lineQuestion P W line)).postprocess
    (lineAnswerOrZero line)

/-- The completed evaluation classes of a typed line measurement. This is the
only strategy-side family whose outcome uses `Option`; `none` is precisely the
non-evaluating class of `def:ideg-deg-polynomials`, paper
`14_analysis_of_the_pauli_basis_test.tex:51-62`, blueprint
`def:ideg-deg-polynomials`. -/
noncomputable def lineEvalMeas
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : PauliPoint P) :
    Measurement (Option (PauliScalar P)) (S.LocalSpace side) :=
  (S.lineMeas side W line).postprocess (evalOpt line u)

/-- The complete typed Pair measurement on one player side. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-249`; blueprint
`lem:qld-win-implications`. -/
noncomputable def pairMeas
    (uX uZ : PauliPoint P) (rX rZ : PauliScalar P) :
    Measurement (ZMod 2 × ZMod 2) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pairQuestion P uX uZ rX rZ)).postprocess pairAnswerOrZero

/-- The complete typed Pair/W measurement on one player side. Paper
`14_analysis_of_the_pauli_basis_test.tex:210-263`; blueprint
`lem:qld-win-implications`. -/
noncomputable def pairWMeas
    (W : PauliKind) (uX uZ : PauliPoint P)
    (rX rZ : PauliScalar P) : Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pairWQuestion P W uX uZ rX rZ)).postprocess
    pairWAnswerOrZero

/-- The complete typed Pauli/W measurement on one player side. Paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`; blueprint
`lem:qld-win-implications`. -/
noncomputable def pauliMeas
    (W : PauliKind) : Measurement (PauliRegister P) (S.LocalSpace side) :=
  (S.strategyMeasurement side (pauliQuestion P W)).postprocess pauliAnswerOrZero

/-- The complete typed Magic Square measurement on one player side. Its answer
alphabet is exactly `MsAnswer`; these families therefore define a Magic Square
strategy. Paper `14_analysis_of_the_pauli_basis_test.tex:213-258`;
blueprint `lem:qld-win-implications`. -/
noncomputable def msMeas
    (t : MsType) (uX uZ : PauliPoint P)
    (rX rZ : PauliScalar P) : Measurement MsAnswer (S.LocalSpace side) :=
  (S.strategyMeasurement side (msQuestion P t uX uZ rX rZ)).postprocess
    (msAnswerOrZero t)

end

/-- The sum of effects corresponding to answers that are invalid for a given
question type. This mass is kept separate from the fixed valid outcome into
which typed postprocessing folds it. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`def:pauli-win-predicate`. -/
noncomputable def wrongFormEffect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : PauliType) (M : Measurement (PauliAnswer P) ι) : Op ι :=
  ∑ answer ∈ Finset.univ.filter (fun answer => validPauliAnswer t answer = false),
    M.effect answer

variable (S : ProjectiveSetting P ε) (side : PlayerSide)

/-- The side-indexed strategy observable
`W^r(u) = sum_a (-1)^(tr(ar)) M_a^((Point,W),u)`. It uses the canonical
character `phaseSign` and the fixed trace of `P.model`. This is
`def:strategy-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
noncomputable def pointObs
    (W : PauliKind) (r : PauliScalar P) (u : PauliPoint P) :
    Op (S.LocalSpace side) :=
  ∑ a : PauliScalar P,
    phaseSign (fixedBinTrace P.model (a * r)) • (S.pointMeas side W u).effect a

section

variable (W : PauliKind)

/-- The point observables form an additive representation, as follows from
`eq:qld-strat-obs`, paper `14_analysis_of_the_pauli_basis_test.tex:174-190`.
This multiplication law is a formalization-only consequence of that definition. -/
theorem pointObs_mul (r s : PauliScalar P)
    (u : PauliPoint P) :
    S.pointObs side W r u * S.pointObs side W s u =
      S.pointObs side W (r + s) u := by
  classical
  let M := S.pointMeas side W u
  have hM : Measurement.IsProjective (S.pointMeas side W u) := by
         apply SandwichProduct.postprocess_isProjective
         cases side with
         | alice => exact S.isProjective.1 _
         | bob => exact S.isProjective.2 _
  change (∑ a : PauliScalar P,
      phaseSign (fixedBinTrace P.model (a * r)) • M.effect a) *
      (∑ a : PauliScalar P,
        phaseSign (fixedBinTrace P.model (a * s)) • M.effect a) =
    _
  calc
    _ = ∑ a : PauliScalar P, ∑ b : PauliScalar P,
        (phaseSign (fixedBinTrace P.model (a * r)) *
          phaseSign (fixedBinTrace P.model (b * s))) •
            (M.effect a * M.effect b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single]
      · rw [(hM a).isIdempotentElem.eq]
        simp [mul_add, fixedBinTrace, phaseSign_add]
      · intro b hb hba
        rw [DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (fun h => hba h.symm)]
        simp
      · intro ha'
        exact (ha' (Finset.mem_univ a)).elim

/-- The zero-label point observable is the identity by measurement completeness. -/
theorem pointObs_zero (u : PauliPoint P) :
    S.pointObs side W 0 u = 1 := by
  classical
  simpa [pointObs, fixedBinTrace, phaseSign] using (S.pointMeas side W u).sum_eq_one

/-- The point observable squares to the identity. This is the assertion that
the operator in `def:strategy-observables` has eigenvalues in `{+1,-1}`;
paper `14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_sq_eq_one (r : PauliScalar P) (u : PauliPoint P) :
    S.pointObs side W r u * S.pointObs side W r u = 1 := by
  haveI :=
    (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
  rw [pointObs_mul, CharTwo.add_self_eq_zero, pointObs_zero]

/-- The point observable is Hermitian. This is the self-adjoint part of the
observable assertion following `eq:qld-strat-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_isHermitian (r : PauliScalar P) (u : PauliPoint P) :
    (S.pointObs side W r u).IsHermitian := by
  classical
  rw [pointObs, Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.conjTranspose_smul, star_phaseSign, (Matrix.nonneg_iff_posSemidef.mp
    ((S.pointMeas side W u).pos a)).isHermitian.eq]

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
