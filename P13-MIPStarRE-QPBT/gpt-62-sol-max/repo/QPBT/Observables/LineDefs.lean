module

public import QPBT.Games.DistributionAux
public import QPBT.Test.LowDegreeGame
public import MIPStarRE.LDT.Preliminaries.Polynomials

/-!
# Lines, bounded line polynomials, and line-point distributions

This file provides the seed-bearing line descriptions and coefficient-list
polynomials shared by the observable and combining chapters. It also realizes
the line-point distribution directly from the conditionally linear sampler.
Over a finite coefficient field, bounded individual-degree multivariate
polynomials form a finite outcome set for the associated measurements.

## References

The line and bounded-polynomial definitions are blueprint
`def:ideg-deg-polynomials`, with source origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:51-58`. The
line-point sampler is `def:line-point-dist` in blueprint chapter 13, from
`08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- The two presentations of lines used by the low-degree question sampler. -/
inductive LineKind where
  | axis
  | diagonal
  deriving DecidableEq

/-- A seed-bearing line description for blueprint
`def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:143-174,243-287`.

An axis description stores its canonical base and seed. A diagonal description
stores only the projected direction, together with its prefix-zero invariant.
Both cases carry the assertion that their base is fixed by the
appropriate `lineRepMap`. Coordinates are numbered from zero; coordinate `j`
corresponds to the paper's coordinate `j + 1`. -/
inductive LineDesc (L : LdParams) where
  | axis (base : LdPoint L) (seed : ScalarQ L)
      (baseFixed : lineRepMap (coordinateDirection (chiIndex L seed)) base = base)
  | diagonal (base : LdPoint L) (seed : ScalarQ L)
      (direction : LdPoint L)
      (baseFixed : lineRepMap direction base = base)
      (prefixZero : ∀ j : Fin L.m, j.val < (chiIndex L seed).val → direction j = 0)
  deriving DecidableEq

section

variable {L : LdParams}
include L

/-- The tag of a canonical line description. -/
def LineDesc.kind : LineDesc L → LineKind
  | .axis _ _ _ => .axis
  | .diagonal _ _ _ _ _ => .diagonal

/-- The seed retained by a canonical line description. -/
def LineDesc.seed : LineDesc L → ScalarQ L
  | .axis _ seed _ => seed
  | .diagonal _ seed _ _ _ => seed

/-- The canonical base stored by a line description. -/
def LineDesc.base : LineDesc L → LdPoint L
  | .axis base _ _ => base
  | .diagonal base _ _ _ _ => base

/-- The geometric direction represented by a canonical line description.
Diagonal descriptions already store the projected data, so this map does
not apply a second projection. -/
def LineDesc.direction (line : LineDesc L) :
    LdPoint L :=
  match line with
  | .axis _ seed _ => coordinateDirection (chiIndex L seed)
  | .diagonal _ _ direction _ _ => direction

/-- The point set represented by a seed-bearing line description. -/
noncomputable def LineDesc.pointSet (line : LineDesc L) :
    Set (LdPoint L) :=
  linePoints line.base line.direction

end

/-- Coefficient-list representation of a univariate polynomial of degree at
most `c` over the scalar field of `L`. -/
abbrev DegPoly (L : LdParams) (c : ℕ) := Fin (c + 1) → ScalarQ L

/-- A seed-bearing line with its sampled point. -/
abbrev LinePointSample (L : LdParams) := LineDesc L × LdPoint L


/-- Extend a coefficient list by zero from degree bound `c` to `c'`. -/
def DegPoly.padTo {L : LdParams} {c c' : ℕ} (h : c ≤ c')
    (f : DegPoly L c) : DegPoly L c' :=
  padCoefficients (Nat.succ_le_succ h) f

section

variable {L : LdParams} {c : ℕ} (line : LineDesc L)
include L c line

/-- A line polynomial evaluates to `a` at `u` when `u` has a line parameter
and every such parameter gives the same value.  The universal clause handles
the zero-direction presentation without choosing a sentinel parameter. -/
def EvaluatesTo
    (f : DegPoly L c) (u : LdPoint L) (a : ScalarQ L) : Prop :=
  LineEvaluation.Determines (fun t => u = line.base + t • line.direction) (evalCoefficient f) a

/-- Partially evaluate a line polynomial at a point. The value is undefined
when the point does not determine an evaluation. This formalization-only
completion is used in blueprint chapter 14; the displayed family at paper
`14_analysis_of_the_pauli_basis_test.tex:197-206` has no bottom outcome. -/
noncomputable def evalOpt
    (u : LdPoint L) (f : DegPoly L c) : Option (ScalarQ L) :=
  LineEvaluation.value (fun t => u = line.base + t • line.direction) (evalCoefficient f)

theorem evalOpt_eq_some_iff
    (u : LdPoint L) (f : DegPoly L c) (a : ScalarQ L) :
    evalOpt line u f = some a ↔ EvaluatesTo line f u a :=
  LineEvaluation.value_eq_some_iff

end

section

variable (L : LdParams)
include L

/-- Convert an axis-line CL output to its seed-bearing presentation; paper
`08_classical_and_quantum_low_degree_tests.tex:243-257,276-287`. -/
def aLineDescOf (line : LdSpace L) : LineDesc L :=
  let direction := coordinateDirection (chiIndex L line.seed)
  let base := lineRepMap direction line.point
  LineDesc.axis base line.seed (lineRepMap_apply_self direction line.point)

/-- Convert a diagonal-line CL output to its seed-bearing presentation; paper
`08_classical_and_quantum_low_degree_tests.tex:261-287`. -/
def dLineDescOf (line : LdSpace L) : LineDesc L :=
  let direction := prefixProjection (chiIndex L line.seed) line.direction
  let base := lineRepMap direction line.point
  LineDesc.diagonal base line.seed direction
    (lineRepMap_apply_self direction line.point) (by
      intro j hj
      change prefixProjection (chiIndex L line.seed) line.direction j = 0
      simp_all [prefixProjection])

/-- The canonical line decoded from a single ambient sample. -/
def sampledLine : LineKind → LdSpace L → LineDesc L
  | .axis => aLineDescOf L
  | .diagonal => dLineDescOf L

/-- The line and point are decoded directly from their common uniform sample. -/
noncomputable def lineKindPointDist (kind : LineKind) :
    Distribution (LinePointSample L) :=
  (uniformDistribution (LdSpace L)).map fun z => (sampledLine L kind z, z.point)

noncomputable abbrev aLinePointDist := lineKindPointDist L .axis
noncomputable abbrev dLinePointDist := lineKindPointDist L .diagonal

/-- The equal mixture of axis and diagonal line-point samples from
`def:line-point-dist`; paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
noncomputable def linePointDist :
    Distribution (LinePointSample L) :=
  Distribution.mix (1 / 2) (by norm_num) (by norm_num)
    (aLinePointDist L) (dLinePointDist L)

/-- The affine line-point component has total probability one. -/
theorem aLinePointDist_isProbability :
    (aLinePointDist L).IsProbability :=
  (uniformDistribution_isProbability _).map _

/-- The diagonal line-point component has total probability one. -/
theorem dLinePointDist_isProbability :
    (dLinePointDist L).IsProbability :=
  (uniformDistribution_isProbability _).map _

/-- The line-point mixture has total probability one. -/
theorem linePointDist_isProbability :
    (linePointDist L).IsProbability := by
  exact Distribution.mix_isProbability _ _ _
    (aLinePointDist_isProbability L) (dLinePointDist_isProbability L)
    (by norm_num) (by norm_num)

end

end

end MIPStarRE.QPBT
