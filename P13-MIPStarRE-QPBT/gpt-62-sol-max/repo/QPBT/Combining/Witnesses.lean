module

public import QPBT.Combining.Defs
public import QPBT.Combining.DirectLowDegree.Soundness
public import QPBT.Combining.DirectLowDegree.AnyStrategySoundness
public import QPBT.Combining.DirectLowDegree.CoefficientCollision
public import QPBT.Combining.DirectLowDegree.CoefficientConsistency
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Compression
public import QPBT.Combining.DirectLowDegree.Transport.Consistency.Defect
public import QPBT.Combining.DirectLowDegree.Transport.LineResampling
public import QPBT.Combining.DirectLowDegree.Transport.Strategy
public import QPBT.Combining.DirectLowDegree.GameValue
public import QPBT.Combining.DirectLowDegree.RejectionBounds
public import QPBT.Combining.DirectLowDegree.Transport.PassConversion
public import QPBT.Combining.DirectLowDegree.Transport.SeedFiberValue
public import QPBT.Combining.DirectLowDegree.Transport.Error
public import QPBT.Combining.DirectLowDegree.Transport.Simultaneous
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Linearity
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Strategy
public import QPBT.Combining.DirectLowDegree.Transport.Combining.QuestionLaw
public import QPBT.Combining.DirectLowDegree.Transport.Combining.GameValue
public import QPBT.Combining.DirectLowDegree.Transport.Combining.WinPredicate
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Value
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Restriction
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Coefficients
public import QPBT.Combining.DirectLowDegree.Transport.Combining.ExactLinearity
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Recovery
public import QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryDefect
public import QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryTransport
public import QPBT.Combining.DirectLowDegree.Transport.Combining.SimultaneousGeneral
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Error
public import QPBT.Combining.DirectLowDegree.Transport.PointAgreement
public import QPBT.Games.Sandwich.Support
public import QPBT.Combining.DirectLowDegree.ExtendedCoefficientLoss
public import QPBT.Games.Consistency
public import QPBT.Observables.LineMeasurement
public import QPBT.Observables.WinImplications.InterchangedCommutation

/-!
# Witnesses for combining the Pauli bases

This module defines the five measurement and distribution witnesses used in
the combining argument.  Every measurement is indexed by the player side, so
Alice's and Bob's local spaces remain distinct.  The extended-dimensional
line objects use the directly indexed low-degree interface and therefore do
not require a dimension-divisibility hypothesis.

## References

`CombinedPointsWitness`, `CombinedLinesWitness`, and `GlobalPairWitness` record
the measurement conclusions of `lem:qld-4-10`, `lem:qld-xz-lines`, and
`lem:qld-4-7`, respectively, in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  `SubLineWitness` and
`ExtendedLinesWitness` instead support `lem:qld-sublines` and `lem:qld-4-13`
through the directly indexed extended-line carrier and probability law.  The
latter also uses the completed answer alphabet, rather than the field-valued
answer sum in the source statement.  The paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709,
882-894,1020-1069,1267-1274`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

noncomputable section

/-! ## The canonical scalar identification -/

/-- Identify the direct extended game's scalar field with the Pauli scalar
field.  Both are selected by `fixedFieldModel`; only their proof argument for
admissibility differs. -/
noncomputable def extendedDirectScalarEquiv (P : AdmissibleParams) :
    DirectScalarQ P.extendedDirectLd ≃+* PauliScalar P := by
  have h : P.extendedDirectLd.hq = P.hq := Subsingleton.elim _ _
  cases h
  exact RingEquiv.refl _

/-- Transport an extended direct point into the canonical Pauli scalar field. -/
def directPointToPauli (P : AdmissibleParams)
    (u : DirectPoint P.extendedDirectLd) :
    Fin (2 * P.m + 2) -> PauliScalar P :=
  fun i => extendedDirectScalarEquiv P (u i)

/-! ## Combined point and line measurements -/

/-- The effect selected by `W` from the two point measurement families. -/
abbrev ProjectiveSetting.pointPairEffect {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (xz : PointPair P)
    (ab : PauliScalar P × PauliScalar P) :=
  (S.pointMeasExp side W (W.component xz)).effect (W.component ab)

/-- The equivalence ordering the two coordinates by the first Pauli basis. -/
def PauliKind.pairOrder {α : Type*} : PauliKind → (α × α ≃ α × α)
  | .X => Equiv.refl _
  | .Z => Equiv.prodComm _ _

@[simp] theorem PauliKind.component_pairOrder {α : Type*} (W : PauliKind) (ab : α × α) :
    W.component (W.pairOrder ab) = ab.1 := by cases W <;> rfl

@[simp] theorem PauliKind.other_component_pairOrder {α : Type*} (W : PauliKind) (ab : α × α) :
    W.other.component (W.pairOrder ab) = ab.2 := by cases W <;> rfl

@[simp] theorem PauliKind.other_other (W : PauliKind) : W.other.other = W := by cases W <;> rfl

/-- The local ordered product of the two point effects. -/
abbrev ProjectiveSetting.orderedPointProduct {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (xz : PointPair P) (ab : PauliScalar P × PauliScalar P) :=
  S.pointPairEffect side W xz ab * S.pointPairEffect side W.other xz ab

abbrev ProjectiveSetting.placedOrderedPointProduct {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) (W : PauliKind)
    (xz : PointPair P) (ab : PauliScalar P × PauliScalar P) :=
  S.place p (S.orderedPointProduct p.side W xz ab)

/-- A local joint measurement for each point pair on either player. -/
abbrev PointPairFamily {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) :=
  (side : PlayerSide) → PauliPoint P → PauliPoint P →
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side)

abbrev ProjectiveSetting.placedPointPairFamily {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (Q : PointPairFamily S) (p : Placement)
    (xz : PointPair P) (ab : PauliScalar P × PauliScalar P) :=
  S.place p ((Q p.side xz.1 xz.2).effect ab)

/-- Projective joint point measurements and their consistency with both ordered products. -/
structure CombinedPointsWitness {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (δ : ℝ) where
  Q : PointPairFamily S
  projective : ∀ side x z, Measurement.IsProjective (Q side x z)
  self_consistent : ∀ p q : Placement, p.IsOpposite q →
    opFamilyDistSq (uniformDistribution (PointPair P))
      (S.placedPointPairFamily Q p) (S.placedPointPairFamily Q q) S.psiHat ≤ δ
  consistent_ordered : ∀ p q : Placement, p.IsOpposite q → ∀ W : PauliKind,
    opFamilyDistSq (uniformDistribution (PointPair P))
      (S.placedPointPairFamily Q p) (S.placedOrderedPointProduct q W) S.psiHat ≤ δ

/-- The two source line-point pairs of a subline sample. -/
abbrev SourceLinePointPair (P : AdmissibleParams) :=
  (LinePointSample P.toLdParams) ×
  (LinePointSample P.toLdParams)

/-- An independent draw of a line and point for each Pauli basis. -/
abbrev sourceLinePointPairDist (P : AdmissibleParams) : Distribution (SourceLinePointPair P) :=
  Distribution.prod (linePointDist P.toLdParams) (linePointDist P.toLdParams)

/-- Read out the values of the two line answers at the two queried points. -/
abbrev pairedLineReadout {P : AdmissibleParams} {I : Type*} [Fintype I] [DecidableEq I]
    (T : LineDesc P.toLdParams → LineDesc P.toLdParams →
      Measurement (PauliLinePoly P × PauliLinePoly P) I) (s : SourceLinePointPair P) :=
  (T s.1.1 s.2.1).postprocess fun fs => (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)

/-- The point-pair measurement with labels in the evaluated line-answer alphabet. -/
abbrev CombinedPointsWitness.completedPair {P : AdmissibleParams} {ε δQ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δQ)
    (side : PlayerSide) (x z : PauliPoint P) :=
  (points.Q side x z).postprocess fun ab => (some ab.1, some ab.2)

/-- Joint line measurements and their evaluation consistency from
`lem:qld-xz-lines`, paper lines 882--894.  Evaluation uses explicit `Option`
outcomes, including the class of answers not determined at the sampled point. -/
structure CombinedLinesWitness {P : AdmissibleParams} {ε δQ : ℝ}
    (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
    (δ : ℝ) where
  /-- The complete paired-line measurement on each expanded local space. -/
  T : (side : PlayerSide) ->
    LineDesc P.toLdParams -> LineDesc P.toLdParams ->
    Measurement
      (PauliLinePoly P ×
        PauliLinePoly P)
      (S.ExpandedLocalSpace side)
  /-- On an axis-parallel X line, outcomes outside degree `d` have zero effect. -/
  axis_degree_X : ∀ side lineX lineZ fX fZ,
    lineX.kind = .axis -> Not (DegPoly.FitsDegree P.d fX) ->
      (T side lineX lineZ).effect (fX, fZ) = 0
  /-- On an axis-parallel Z line, outcomes outside degree `d` have zero effect. -/
  axis_degree_Z : ∀ side lineX lineZ fX fZ,
    lineZ.kind = .axis -> Not (DegPoly.FitsDegree P.d fZ) ->
      (T side lineX lineZ).effect (fX, fZ) = 0
  /-- Evaluated line pairs are consistent with the completed point-pair
  measurement on every directed opposite placement. -/
  consistent : ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
    S.placedDefect p1 p2 (sourceLinePointPairDist P) (pairedLineReadout (T p1.side))
      (fun s => points.completedPair p2.side s.1.2 s.2.2) ≤ δ

/-- Evaluate the supplied paired-line measurement at the queried points. -/
abbrev CombinedLinesWitness.evalPair {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP) (side : PlayerSide) :=
  pairedLineReadout (lines.T side)

/-! ## The subline distribution -/

/-- A tuple consisting of an extended line and its projected X and Z lines. -/
abbrev SubLineTriple (P : AdmissibleParams) :=
  DirectLineDesc P.extendedDirectLd ×
    (LineDesc P.toLdParams × LineDesc P.toLdParams)

/-- An extended line tuple together with a point sampled uniformly on it. -/
abbrev SubLinePointSample (P : AdmissibleParams) :=
  SubLineTriple P ×
    (DirectPoint P.extendedDirectLd)

/-- The shared restricted line kind and two coordinate indices in one mixture
component of the subline law. -/
abbrev SubLineComponent (P : AdmissibleParams) :=
  LineKind × (Fin P.m × Fin P.m)

/-- Select the restricted line-point distribution of a given kind and index. -/
noncomputable def restrictedLinePointDist (P : AdmissibleParams)
    (kind : LineKind) (i : Fin P.m) :
    Distribution (LinePointSample P.toLdParams) :=
  restrictedLineDist P.toLdParams kind i

/-- Sample a subline tuple and then a uniform affine parameter on its
extended line. -/
noncomputable def subLinePointDist (P : AdmissibleParams)
    (D : Distribution (SubLineTriple P)) :
    Distribution (SubLinePointSample P) :=
  (Distribution.prod D
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map fun sample =>
      (sample.1, sample.1.1.base + sample.2 • sample.1.1.direction)

def subLineJointProjection {P : AdmissibleParams} (s : SubLinePointSample P) : SourceLinePointPair P :=
  ((s.1.2.1, projX (directPointToPauli P s.2)), (s.1.2.2, projZ (directPointToPauli P s.2)))

def subLineComponentProduct (P : AdmissibleParams) (c : SubLineComponent P) :
    Distribution (SourceLinePointPair P) :=
  Distribution.prod (restrictedLinePointDist P c.1 c.2.1) (restrictedLinePointDist P c.1 c.2.2)

/-- Directly indexed form of the subline distribution of `lem:qld-sublines`,
paper lines 1063--1069.  Its extended-line marginal is the directly indexed
line-point law rather than the seed-indexed line-point distribution over
`F_q^(2m+2)` of the source statement; that replacement is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, so this is a
formalization auxiliary record, not the source-labelled statement.  Its
source-mixture field records the X and Z point marginals separately; it does
not assert a joint conditional law for the pair of projected points. -/
structure SubLineWitness (P : AdmissibleParams) where
  /-- The actual distribution of an extended line and two projected lines. -/
  D : Distribution (SubLineTriple P)
  /-- The distribution has total mass one. -/
  isProbability : D.IsProbability
  /-- Its extended-line marginal is the direct line-point marginal. -/
  extended_marginal : D.map Prod.fst =
    (directLinePointDist P.extendedDirectLd).map Prod.fst
  /-- Every point of an extended line projects onto both stored source lines. -/
  incidence : ∀ sample ∈ D.support, ∀ u ∈ sample.1.pointSet,
    projX (directPointToPauli P u) ∈ sample.2.1.pointSet ∧
      projZ (directPointToPauli P u) ∈ sample.2.2.pointSet
  /-- Each line triple carries affine data sufficient for
  `combineLinePoly_spec`. -/
  compatibility : ∀ sample ∈ D.support,
    ∃ aX bX aZ bZ uAlpha vAlpha uBeta vBeta : PauliScalar P,
      IsCombineLineCompatible
        (directPointToPauli P sample.1.base)
        (directPointToPauli P sample.1.direction)
        sample.2.1.base sample.2.1.direction
        sample.2.2.base sample.2.2.direction
        aX bX aZ bZ uAlpha vAlpha uBeta vBeta
  /-- The joint projected law is a mixture of restricted product laws.
  The two source draws are independent within a component, not across the mixture. -/
  source_mixture : ∃ components : Distribution (SubLineComponent P),
    components.IsProbability ∧
      (subLinePointDist P D).map subLineJointProjection =
        Distribution.bind components (subLineComponentProduct P)
  /-- An extended axis line has axis-parallel projected lines. -/
  axis_closure : ∀ sample ∈ D.support, sample.1.kind = .axis ->
    sample.2.1.kind = .axis ∧ sample.2.2.kind = .axis

/-! ## Extended lines and global polynomial pairs -/

/-- A pair of source points and the two scalar coefficients used by the
extended point measurement. -/
abbrev ExtendedPointQuestion (P : AdmissibleParams) :=
  (PointPair P) ×
    (PauliScalar P × PauliScalar P)

/-- The affine scalar readout on a pair of point answers. -/
def ExtendedPointQuestion.read {P : AdmissibleParams} (x : ExtendedPointQuestion P)
    (ab : PauliScalar P × PauliScalar P) : PauliScalar P :=
  x.2.1 * ab.1 + x.2.2 * ab.2

/-- Split the direct point into the two point coordinates and scalar weights. -/
def ExtendedPointQuestion.ofDirect (P : AdmissibleParams)
    (u : DirectPoint P.extendedDirectLd) : ExtendedPointQuestion P :=
  let v := directPointToPauli P u
  ((projX v, projZ v), (v (alphaVar P.m), v (betaVar P.m)))

namespace CombinedPointsWitness

/-- Coarse-grain a joint point measurement by `(a,b) |-> alpha*a + beta*b`
on the selected player side.  This is the concrete measurement of
`lem:qld-4-12`, paper lines 993--1011. -/
noncomputable def extendedQ {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ)
    (side : PlayerSide) (x : ExtendedPointQuestion P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  (points.Q side x.1.1 x.1.2).postprocess x.read

end CombinedPointsWitness

namespace ExtendedLineGame

variable {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}

/-- Read the scalar linear combination of the two point answers. -/
abbrev completedPointReadout (points : CombinedPointsWitness S δQ)
    (side : PlayerSide) (u : DirectPoint P.extendedDirectLd) :=
  (points.extendedQ side (ExtendedPointQuestion.ofDirect P u)).postprocess some

/-- Evaluate a line answer, keeping the option for points off the line. -/
abbrev readLineAt {I : Type*} [Fintype I] [DecidableEq I] {c : ℕ}
    (M : Measurement (DirectDegPoly P.extendedDirectLd c) I)
    (line : DirectLineDesc P.extendedDirectLd)
    (u : DirectPoint P.extendedDirectLd) :=
  M.postprocess fun c => (directEvalOpt line u c).map (extendedDirectScalarEquiv P)

/-- The defect of a completed line/point measurement pair at the indicated placements. -/
abbrev completedDefect (points : CombinedPointsWitness S δQ) (p q : Placement)
    (μ : Distribution (DirectLinePointSample P.extendedDirectLd))
    (M : DirectLineDesc P.extendedDirectLd →
      Measurement (DirectDegPoly P.extendedDirectLd (P.m * P.d + 1)) (S.ExpandedLocalSpace p.side)) : ℝ :=
  S.placedDefect p q μ (fun z => readLineAt (M z.1) z.1 z.2)
    (fun z => completedPointReadout points q.side z.2)

end ExtendedLineGame

/-- Extended-line POVMs and directly indexed, completed-answer forms of the two
consistency relations in `lem:qld-4-13`, paper lines 1020--1034. The direct line
carrier avoids the dimension-divisibility obstruction documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. -/
structure ExtendedLinesWitness {P : AdmissibleParams} {ε δQ : ℝ}
    (S : ProjectiveSetting P ε) (points : CombinedPointsWitness S δQ)
    (δ : ℝ) where
  /-- The complete extended-line measurement on each player side. -/
  Qline : (side : PlayerSide) -> DirectLineDesc P.extendedDirectLd ->
    Measurement (DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
      (S.ExpandedLocalSpace side)
  /-- Axis-line outcomes outside degree `d` have zero effect. -/
  axis_degree : ∀ side line f, line.kind = .axis ->
    Not (∀ i, P.d < i.val -> f i = 0) ->
      (Qline side line).effect f = 0
  /-- Each player's evaluated lines agree with the opposite completed points. -/
  consistent : ∀ {p : Placement}, p.Primary →
    ExtendedLineGame.completedDefect points p (ProjectiveSetting.overlapPartner p)
      (directLinePointDist P.extendedDirectLd) (Qline p.side) ≤ δ

/-- Side-indexed global polynomial-pair measurements, as in `lem:qld-4-7`. -/
structure GlobalPairWitness {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (δ : ℝ) where
  Smeas : (side : PlayerSide) → Measurement (PolyPair P) (S.ExpandedLocalSpace side)
  projective : ∀ side, Measurement.IsProjective (Smeas side)
  /-- Each player's global evaluations agree with the opposite source points. -/
  point_consistent : ∀ {p : Placement}, p.Primary → ∀ W : PauliKind,
    let q := ProjectiveSetting.overlapPartner p
    S.placedDefect p q (uniformDistribution (PauliPoint P))
      (fun u => (Smeas p.side).postprocess (evalAt W u)) (S.pointMeasExp q.side W) ≤ δ

end

end MIPStarRE.QPBT
