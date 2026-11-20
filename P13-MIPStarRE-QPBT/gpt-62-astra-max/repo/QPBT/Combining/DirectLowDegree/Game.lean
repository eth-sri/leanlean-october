module

public import QPBT.Combining.DirectLowDegree.Geometry
public import QPBT.Test.LowDegreeGameMeasurements

/-!
# The directly indexed low-degree game

This module defines polynomial evaluation, questions, answers, and the game
for the directly indexed low-degree interface.

## References

The underlying game is blueprint
`def:ld-game`, with source origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Coefficient lists for a univariate polynomial of degree at most `c` in the
direct scalar field. -/
abbrev DirectDegPoly (D : DirectLdParams) (c : ℕ) :=
  Fin (c + 1) → DirectScalarQ D

section

variable {D : DirectLdParams} {c : ℕ} (line : DirectLineDesc D)

/-- A direct line polynomial evaluates to `a` at `u` when `u` lies on the line
and every parameter presenting `u` gives value `a`.  The universal clause
keeps the zero-direction case explicit. -/
def DirectEvaluatesTo
    (f : DirectDegPoly D c) (u : DirectPoint D)
    (a : DirectScalarQ D) : Prop :=
  (∃ t : DirectScalarQ D, u = line.base + t • line.direction) ∧
    ∀ t : DirectScalarQ D, u = line.base + t • line.direction →
      evalCoefficient f t = a

/-- Option-completed evaluation of a direct line polynomial.  `none` is an
explicit outcome when the point does not determine an evaluation; no field
value is used as a fallback. -/
noncomputable def directEvalOpt (u : DirectPoint D)
    (f : DirectDegPoly D c) : Option (DirectScalarQ D) := by
  classical
  exact if h : ∃ a : DirectScalarQ D, DirectEvaluatesTo line f u a then
    some (Classical.choose h)
  else none

end

section

variable (D : DirectLdParams)

/-- The typed question alphabet of the directly indexed game. -/
abbrev DirectLdQuestion := LdType × DirectLdSpace D

variable {D} in
/-- Canonicalize a common direct sample for one question type.  Irrelevant
coordinates are fixed, so point questions reveal no sampled line index and
axis-line questions reveal no diagonal direction. -/
noncomputable def directLdMap :
    LdType → DirectLdSpace D → DirectLdSpace D
  | .point, sample => ⟨sample.point, D.firstIndex, 0⟩
  | .aline, sample =>
      let direction := coordinateDirection sample.index
      ⟨lineRepMap direction sample.point, sample.index, 0⟩
  | .dline, sample =>
      let direction := directPrefixProjection sample.index sample.direction
      ⟨lineRepMap direction sample.point, sample.index, direction⟩

/-- The directly indexed question distribution.  It has the same uniform
ordered type-pair branches as `ldQuestionDistribution`, but its common sample
contains an actual coordinate index rather than a field seed. -/
noncomputable def directLdQuestionDistribution :
    Distribution (DirectLdQuestion D × DirectLdQuestion D) :=
  (uniformDistribution ((LdType × LdType) × DirectLdSpace D)).map fun sample =>
    ((sample.1.1, directLdMap sample.1.1 sample.2),
      (sample.1.2, directLdMap sample.1.2 sample.2))

/-- The answer alphabet of the directly indexed game. -/
inductive DirectLdAnswer where
  | pointVals (a : Fin D.k → DirectScalarQ D)
  | alinePolys (a : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
  | dlinePolys (a : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
  deriving DecidableEq

/-- A finite code for the directly indexed answer alphabet. -/
abbrev DirectLdAnswerCode :=
  (Fin D.k → DirectScalarQ D) ⊕
    ((Fin D.k → Fin (D.d + 1) → DirectScalarQ D) ⊕
      (Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D))

/-- The canonical code equivalence for `DirectLdAnswer`, sending point,
axis-line, and diagonal-line answers to the three summands. -/
noncomputable def directLdAnswerEquiv :
    DirectLdAnswer D ≃ DirectLdAnswerCode D where
  toFun
    | .pointVals a => .inl a
    | .alinePolys a => .inr (.inl a)
    | .dlinePolys a => .inr (.inr a)
  invFun
    | .inl a => .pointVals a
    | .inr (.inl a) => .alinePolys a
    | .inr (.inr a) => .dlinePolys a
  left_inv := by intro answer; cases answer <;> rfl
  right_inv := by
    intro answer
    rcases answer with a | a
    · rfl
    · rcases a with a | a <;> rfl

instance instInhabitedDirectLdAnswer : Inhabited (DirectLdAnswer D) :=
  ⟨.pointVals 0⟩

noncomputable instance instFintypeDirectLdAnswer :
    Fintype (DirectLdAnswer D) :=
  Fintype.ofEquiv (DirectLdAnswerCode D) (directLdAnswerEquiv D).symm

end

/-- Check that a direct-game answer has the constructor required by its
question type. -/
def validDirectLdAnswer {D : DirectLdParams} (t : LdType)
    (answer : DirectLdAnswer D) : Bool :=
  match t, answer with
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

section

variable (D : DirectLdParams)

/-- The directly indexed axis-line versus point acceptance relation. -/
def directAlinePointCondition
    (line point : DirectLdSpace D)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
    (a : Fin D.k → DirectScalarQ D) : Prop :=
  ∀ t : DirectScalarQ D,
    point.point = line.point + t • coordinateDirection line.index →
      ∀ j : Fin D.k, evalCoefficient (f j) t = a j

/-- The directly indexed diagonal-line versus point acceptance relation. -/
def directDlinePointCondition
    (line point : DirectLdSpace D)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (a : Fin D.k → DirectScalarQ D) : Prop :=
  ∀ t : DirectScalarQ D,
    point.point = line.point + t • line.direction →
      ∀ j : Fin D.k, evalCoefficient (f j) t = a j

/-- The directly indexed low-degree win predicate.  It differs from
`ldWinPredicate` only by reading the coordinate index directly from each line
question. -/
noncomputable def directLdWinPredicate :
    DirectLdQuestion D → DirectLdQuestion D →
      DirectLdAnswer D → DirectLdAnswer D → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if validDirectLdAnswer tA a && validDirectLdAnswer tB b then
      match tA, tB, a, b with
      | .point, .point, .pointVals u, .pointVals v => decide (u = v)
      | .aline, .point, .alinePolys f, .pointVals u =>
          decide (directAlinePointCondition D xA xB f u)
      | .point, .aline, .pointVals u, .alinePolys f =>
          decide (directAlinePointCondition D xB xA f u)
      | .dline, .point, .dlinePolys f, .pointVals u =>
          decide (directDlinePointCondition D xA xB f u)
      | .point, .dline, .pointVals u, .dlinePolys f =>
          decide (directDlinePointCondition D xB xA f u)
      | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
      | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
      | _, _, _, _ => true
    else false

/-- Swapping both players preserves the direct verifier's decision. -/
theorem directLdWinPredicate_swap (x y : DirectLdQuestion D)
    (a b : DirectLdAnswer D) :
    directLdWinPredicate D x y a b = directLdWinPredicate D y x b a := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  cases i <;> cases j <;> cases a <;> cases b <;>
    first | rfl | simp [directLdWinPredicate, validDirectLdAnswer, eq_comm]

/-- The directly indexed low-degree game at an arbitrary positive dimension.
It is an internal analysis game, not the conditionally linear verifier game
`ldGame`. -/
@[reducible] noncomputable def directLdGame : Game where
  QuestionA := DirectLdQuestion D
  QuestionB := DirectLdQuestion D
  AnswerA := DirectLdAnswer D
  AnswerB := DirectLdAnswer D
  μ := directLdQuestionDistribution D
  μ_prob := ((uniformDistribution_isProbability
            ((LdType × LdType) × DirectLdSpace D)).map _)
  decide := directLdWinPredicate D

/-- The canonical point question associated with a geometric point. -/
def directLdPointQuestionOf
    (u : DirectPoint D) : DirectLdQuestion D :=
  (.point, ⟨u, D.firstIndex, 0⟩)

/-- Total point-answer relabeling used in the direct soundness conclusion.
Wrong-form answers are folded into the zero tuple, exactly as for
`ldPointValuesOrZero`. -/
def directLdPointValuesOrZero :
    DirectLdAnswer D → Fin D.k → DirectScalarQ D
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- A simultaneous tuple of bounded polynomials for the directly indexed
game. -/
noncomputable abbrev DirectPolyTuple :=
  Fin D.k → PolyIndex D.m (DirectScalarQ D) D.d

/-- A polynomial-tuple POVM for the directly indexed game. -/
noncomputable abbrev DirectPolyMeasTuple (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  MIPStarRE.Quantum.Measurement (DirectPolyTuple D) ι

end

/-- Evaluate every component of a direct polynomial tuple at a point. -/
def evalDirectPolyTupleAt {D : DirectLdParams}
    (u : DirectPoint D) (g : DirectPolyTuple D) :
    Fin D.k → DirectScalarQ D :=
  fun j => MvPolynomial.eval u (g j).1

end

end MIPStarRE.QPBT
