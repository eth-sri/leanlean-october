module

public import QPBT.Games.DistanceTheorems
public import QPBT.Observables.Anticommuting
public import QPBT.Observables.Defs

/-!
# Definitions for winning implications

This module defines the measurements, marginals, and induced Magic Square
strategy used by the exact and approximate winning implications.

## References

The definitions support `lem:qld-win-implications` and
`lem:qld-win-implications-obs` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-354` and
blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

section

variable (P : AdmissibleParams)
include P

/-- Equality of Pauli question pairs is decidable. This is used in the
consistency defect from item 1 of blueprint
`lem:qld-win-implications`. -/
noncomputable instance pauliQuestionPairDecidableEq :
    DecidableEq (PauliQuestion P × PauliQuestion P) :=
  Classical.decEq _

/-- The coordinate space records the base and seed of an axis line, or the
base, seed, and direction of a diagonal line. It is finite and indexes the
line-point average in blueprint
`lem:qld-win-implications`. -/
abbrev LineDescCode :=
  ((PauliPoint P) × PauliScalar P) ⊕
    ((PauliPoint P) × PauliScalar P ×
      (PauliPoint P))

/-- Map a canonical line to its kind and coordinate data: base and seed for an
axis line, and base, seed, and direction for a diagonal line. Blueprint
`lem:qld-win-implications`. -/
def lineDescCode :
    LineDesc P.toLdParams → LineDescCode P
  | .axis base seed _ => .inl (base, seed)
  | .diagonal base seed direction _ _ => .inr (base, seed, direction)

/-- The coordinate-data map on canonical lines is injective: lines of the same
kind with equal base, seed, and direction data are equal. This supports the
line-point average in blueprint
`lem:qld-win-implications`. -/
private theorem lineDescCode_injective :
    Function.Injective (lineDescCode P) := by
  intro x y h
  cases x <;> cases y <;> simp_all [lineDescCode]

/-- The set of canonical axis and diagonal lines is finite. This finiteness is
used in the line-point average from item 2 of blueprint
`lem:qld-win-implications`. -/
noncomputable instance lineDescFintype :
    Fintype (LineDesc P.toLdParams) :=
  Fintype.ofInjective (lineDescCode P) (by
    exact lineDescCode_injective P)

/-- The set of pairs consisting of a canonical line and a point is finite.
These pairs index the line-point distribution in the low-degree winning
implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:200-204`, blueprint
`lem:qld-win-implications`. -/
noncomputable instance linePointFintype :
    Fintype (LinePointSample P.toLdParams) :=
  Fintype.ofFinite _

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

section

variable (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind)

/-- Complete a point measurement with a zero `none` outcome. This is the
right-hand family in the corrected low-degree item of
blueprint
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-204`. -/
noncomputable def pointMeasOption (u : PauliPoint P) :
    Measurement (Option (PauliScalar P)) (S.LocalSpace side) :=
  (S.pointMeas side W u).postprocess some

/-- Trace-coarse-graining of a strategy point measurement. This is the family
`M^((Point,W),u)_[tr(·r)=a]` in items 5 and 7 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:232-263`, blueprint
`lem:qld-win-implications`. -/
noncomputable def pointTraceMeas (u : PauliPoint P)
    (r : PauliScalar P) : Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.pointMeas side W u).postprocess fun a => fixedBinTrace P.model (a * r)

/-- The families sampled by the shared Pauli tuple. -/
abbrev pointTraceAt
    (ω : PauliTuple P) := S.pointTraceMeas side W (ω.point W) (ω.scalar W)

abbrev pointObsAt
    (ω : PauliTuple P) := S.pointObs side W (ω.scalar W) (ω.point W)

abbrev pointProductAt
    (ω : PauliTuple P) := S.pointObsAt side W ω * S.pointObsAt side W.other ω

abbrev pairWAt
    (ω : PauliTuple P) := S.pairWMeas side W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

abbrev pairAt (S : ProjectiveSetting P ε) (side : PlayerSide) (ω : PauliTuple P) :=
  S.pairMeas side ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

/-- Evaluate a Pauli-register answer through its low-degree encoding at `u`.
This is `M^(Pauli,W)_[g_h(u)=a]` in item 3 of
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:205-209`, blueprint
`lem:qld-win-implications`. -/
noncomputable def pauliEvalMeas (u : PauliPoint P) :
    Measurement (PauliScalar P) (S.LocalSpace side) :=
  (S.pauliMeas side W).postprocess fun h => lowDegreeEnc h u

/-- Select the `W` bit of a Pair answer. This is the bracketed Pair family in
item 4 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-231`, blueprint
`lem:qld-win-implications`. -/
noncomputable def pairComponentMeas (ω : PauliTuple P) :
    Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.pairAt side ω).postprocess W.component

end

section

variable (S : ProjectiveSetting P ε)
include S

/-- The bit measurement for a Magic Square variable question. This is
`M^(Variable_j,omega)_a` in item 7 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:250-263`, blueprint
`lem:qld-win-implications`. -/
noncomputable def msVarBitMeas
    (side : PlayerSide) (j : Fin 9) (ω : PauliTuple P) :
    Measurement (ZMod 2) (S.LocalSpace side) :=
  (S.msMeas side (.var j) ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).postprocess msBitOrZero

/-- The Magic Square strategy induced by the test measurements at a fixed
Pauli tuple. It retains the original heterogeneous local spaces and state, as
required by item 6 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`lem:qld-win-implications`. -/
noncomputable def msStrategyAt
    (ω : PauliTuple P) : Strategy msGame where
  ιA := S.toStrategy.ιA
  ιB := S.toStrategy.ιB
  ψ := S.toStrategy.ψ
  ψ_norm := S.toStrategy.ψ_norm
  A t := S.msMeas .alice t ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  B t := S.msMeas .bob t ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

/-- The Magic Square value `Lambda_omega` is the ordinary tensor-product game
value of `msStrategyAt`. This is item 6 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:240-249`, blueprint
`lem:qld-win-implications`. -/
noncomputable def msValueAt (ω : PauliTuple P) : ℝ :=
  (S.msStrategyAt ω).value

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
