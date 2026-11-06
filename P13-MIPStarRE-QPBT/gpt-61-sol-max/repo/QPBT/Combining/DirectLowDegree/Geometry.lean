module

public import QPBT.Observables.LineDefs
public import QPBT.Games.DistributionMarginals
public import QPBT.Test.PauliBasisTest

/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

/-- Parameters for the directly indexed low-degree game.  Unlike `LdParams`,
this directly indexed line-space construction has no divisibility field: its coordinate index is
sampled from `Fin m` rather than encoded by fibers of `chiIndex`.

This is the direct-index repair described in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`; it is not a second
definition of the source verifier game. -/
structure DirectLdParams where
  q : ℕ
  m : ℕ
  d : ℕ
  k : ℕ
  hm : 1 ≤ m
  hd : 1 ≤ d
  hk : 1 ≤ k
  hq : IsAdmissibleSize q

variable (D : DirectLdParams)

/-- The canonical scalar model for directly indexed parameters. -/
@[reducible] def DirectLdParams.model
     : FixedFieldModel D.q :=
  fixedFieldModel D.q D.hq

/-- The scalar field of a directly indexed low-degree game. -/
abbrev DirectScalarQ  := D.model.K

abbrev DirectPoint := Fin D.m → DirectScalarQ D

abbrev DirectValues := Fin D.k → DirectScalarQ D

/-- The first coordinate, available because directly indexed dimensions are
positive. -/
def DirectLdParams.firstIndex  : Fin D.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one D.hm⟩

instance instNonemptyFinM_1 (D : DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩

/-- The direct game used at the extended dimension of the combining map.  Its
field, degree, and simultaneity parameters are inherited from `P`, while its
dimension is `2 * P.m + 2`; no divisibility assertion is introduced.

The construction has dimension `2 * P.m + 2` without requiring
`2 * P.m + 2 ∣ P.q`; it supplies the directly indexed line and coordinate
spaces used in the dimension-extension argument of blueprint `lem:qld-sublines`.
-/
@[reducible] def AdmissibleParams.extendedDirectLd (P : AdmissibleParams) : DirectLdParams where
  q := P.q
  m := 2 * P.m + 2
  d := P.d
  k := 1
  hm := by omega
  hd := P.hd
  hk := by decide
  hq := P.hq

/-- A common random sample for the directly indexed question distribution.
The point, coordinate index, and unrestricted direction are mutually uniform. -/
structure DirectLdSpace (D : DirectLdParams) where
  point : MIPStarRE.QPBT.DirectPoint D
  index : Fin D.m
  direction : MIPStarRE.QPBT.DirectPoint D
  deriving DecidableEq, Fintype

instance instNonemptyDirectLdSpace (D : DirectLdParams) : Nonempty (DirectLdSpace D) :=
  ⟨⟨0, D.firstIndex, 0⟩⟩

/-- Decompose a direct sample into its point and the remaining independent
coordinates. -/
def directLdSpacePointEquiv  :
    DirectLdSpace D ≃
       MIPStarRE.QPBT.DirectPoint D  ×
         Fin D.m ×  MIPStarRE.QPBT.DirectPoint D   where
  toFun sample := (sample.point, sample.index, sample.direction)
  invFun sample := ⟨sample.1, sample.2.1, sample.2.2⟩
  left_inv sample := by cases sample; rfl
  right_inv sample := by cases sample; rfl

/-- Decompose a direct sample into its stored index and the remaining
independent coordinates. -/
def directLdSpaceIndexEquiv  :
    DirectLdSpace D ≃
      Fin D.m ×
          MIPStarRE.QPBT.DirectPoint D  ×
           MIPStarRE.QPBT.DirectPoint D   where
  toFun sample := (sample.index, sample.point, sample.direction)
  invFun sample := ⟨sample.2.1, sample.1, sample.2.2⟩
  left_inv sample := by cases sample; rfl
  right_inv sample := by cases sample; rfl

/-- Zero the coordinates preceding the directly sampled prefix index. -/
def directPrefixProjection {D : DirectLdParams} (i : Fin D.m)
    (v : MIPStarRE.QPBT.DirectPoint D) : MIPStarRE.QPBT.DirectPoint D :=
  fun j => if j.val < i.val then 0 else v j

/-- Zeroing the coordinates preceding a prefix index is idempotent: the
coordinates it leaves unchanged are exactly those it does not zero. -/
theorem directPrefixProjection_idem  (i : Fin D.m)
    (v : MIPStarRE.QPBT.DirectPoint D) :
    directPrefixProjection i (directPrefixProjection i v) =
      directPrefixProjection i v := by
  funext j
  unfold directPrefixProjection
  split_ifs <;> rfl

/-- Canonical line descriptions whose coordinate index is stored directly.
Coordinates are numbered from zero, so `index = i` represents coordinate
`i + 1` in the paper. -/
inductive DirectLineDesc (D : DirectLdParams) where
  | axis (base : MIPStarRE.QPBT.DirectPoint D) (index : Fin D.m)
      (baseFixed : lineRepMap (coordinateDirection index) base = base)
  | diagonal (base : MIPStarRE.QPBT.DirectPoint D) (index : Fin D.m)
      (direction : MIPStarRE.QPBT.DirectPoint D)
      (baseFixed : lineRepMap direction base = base)
      (prefixZero : ∀ j : Fin D.m, j.val < index.val → direction j = 0)
  deriving DecidableEq

/-! ## Finite direct-line carrier -/

/-- A finite code for directly indexed lines, omitting only proof fields. -/
abbrev DirectLineDescCode  :=
    MIPStarRE.QPBT.DirectPoint D  × Fin D.m  ⊕
      MIPStarRE.QPBT.DirectPoint D  × Fin D.m ×
       MIPStarRE.QPBT.DirectPoint D  

/-- Encode a directly indexed line by its tag and mathematical data. -/
def directLineDescCode  :
    DirectLineDesc D → DirectLineDescCode D
  | .axis base index _ => .inl (base, index)
  | .diagonal base index direction _ _ => .inr (base, index, direction)

/-- The direct-line code is injective by proof irrelevance. -/
private theorem directLineDescCode_injective  :
    Function.Injective (directLineDescCode D) := by
  intro line line' h
  classical aesop (add simp [directLineDescCode])

/-- Directly indexed line descriptions form a finite type. -/
instance directLineDescFintype (D : DirectLdParams) :
    Fintype (DirectLineDesc D) :=
  Fintype.ofInjective (directLineDescCode D) (by
    exact directLineDescCode_injective D)

/-- The kind of a directly indexed line. -/
def DirectLineDesc.kind {D : DirectLdParams} : DirectLineDesc D → LineKind
  | .axis _ _ _ => .axis
  | .diagonal _ _ _ _ _ => .diagonal

/-- The coordinate index stored in a directly indexed line. -/
def DirectLineDesc.index {D : DirectLdParams} : DirectLineDesc D → Fin D.m
  | .axis _ index _ => index
  | .diagonal _ index _ _ _ => index

/-- The canonical base point of a directly indexed line. -/
def DirectLineDesc.base {D : DirectLdParams} :
    DirectLineDesc D → MIPStarRE.QPBT.DirectPoint D
  | .axis base _ _ => base
  | .diagonal base _ _ _ _ => base

/-- The geometric direction of a directly indexed line. -/
def DirectLineDesc.direction {D : DirectLdParams} (line : DirectLineDesc D) :
    MIPStarRE.QPBT.DirectPoint D :=
  match line with
  | .axis _ index _ => coordinateDirection index
  | .diagonal _ _ direction _ _ => direction

/-- The point set represented by a directly indexed line. -/
def DirectLineDesc.pointSet {D : DirectLdParams}
    (line : DirectLineDesc D) : Set (MIPStarRE.QPBT.DirectPoint D) :=
  linePoints line.base line.direction

/-- Turn a direct sample into its canonical axis-line description. -/
def directALineDescOf
    (sample : DirectLdSpace D) : DirectLineDesc D :=
  let direction := coordinateDirection sample.index
  let base := lineRepMap direction sample.point
  .axis base sample.index (lineRepMap_apply_self direction sample.point)

/-- Turn a direct sample into its canonical diagonal-line description. -/
def directDLineDescOf
    (sample : DirectLdSpace D) : DirectLineDesc D :=
  let direction := directPrefixProjection sample.index sample.direction
  let base := lineRepMap direction sample.point
  .diagonal base sample.index direction
    (lineRepMap_apply_self direction sample.point) (by
      intro j hj
      change directPrefixProjection sample.index sample.direction j = 0
      rw [directPrefixProjection, if_pos hj])

/-- The axis-line/point law with a directly sampled coordinate index. -/
def directALinePointDist  :
    Distribution (DirectLineDesc D ×  MIPStarRE.QPBT.DirectPoint D ) :=
  (uniformDistribution (DirectLdSpace D)).map fun sample =>
    (directALineDescOf D sample, sample.point)

/-- The diagonal-line/point law with a directly sampled prefix index. -/
def directDLinePointDist  :
    Distribution (DirectLineDesc D ×  MIPStarRE.QPBT.DirectPoint D ) :=
  (uniformDistribution (DirectLdSpace D)).map fun sample =>
    (directDLineDescOf D sample, sample.point)

/-- The equal mixture of the directly indexed axis and diagonal line-point
laws.  This is the replacement for the otherwise undefined extended-dimension
instance used at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`. -/
def directLinePointDist  :
    Distribution (DirectLineDesc D ×  MIPStarRE.QPBT.DirectPoint D ) :=
  Distribution.mix (1 / 2) (by norm_num) (by norm_num)
    (directALinePointDist D) (directDLinePointDist D)

/-- The directly indexed axis-line/point law is probabilistic. -/
theorem directALinePointDist_isProbability  :
    (directALinePointDist D).IsProbability := by
  exact (uniformDistribution_isProbability (DirectLdSpace D)).map _

/-- The directly indexed diagonal-line/point law is probabilistic. -/
theorem directDLinePointDist_isProbability  :
    (directDLinePointDist D).IsProbability := by
  exact (uniformDistribution_isProbability (DirectLdSpace D)).map _

/-- The directly indexed line-point mixture is probabilistic. -/
theorem directLinePointDist_isProbability  :
    (directLinePointDist D).IsProbability := Distribution.mix_isProbability _ _ _
    (directALinePointDist_isProbability D) (directDLinePointDist_isProbability D)
    (by norm_num) (by norm_num)

end

end MIPStarRE.QPBT
