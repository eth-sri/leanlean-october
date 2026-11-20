module

public import QPBT.Games.StrategyClasses

/-!
# Ground-slice compression of measurements

This module restricts a POVM on a product space to one distinguished ancillary
coordinate. It also records that this restriction commutes with deterministic
outcome postprocessing, recovers a POVM from its one-measurement Naimark
dilation, and preserves consistency defects evaluated on the correspondingly
padded bipartite state.

The construction supports the pullback after the first paragraph of the proof
of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1289`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.Quantum.Measurement

/-- Principal submatrix on the slice with ancillary coordinate `k₀`. -/
def sliceEffects {I κ : Type*} (k₀ : κ) :
    MIPStarRE.Quantum.Op (I × κ) →+ MIPStarRE.Quantum.Op I where
  toFun M := M.submatrix (fun i => (i, k₀)) (fun i => (i, k₀))
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restrict every effect of a POVM to the matrix block at one fixed ancillary
coordinate. The principal submatrix of a positive semidefinite effect remains
positive semidefinite, and restricting the sum of the effects restricts the
identity to the identity. -/
noncomputable def compressAt
    {Outcome I κ : Type*}
    [Fintype Outcome] [Fintype I] [DecidableEq I]
    [Fintype κ] [DecidableEq κ]
    (k₀ : κ) (M : MIPStarRE.Quantum.Measurement Outcome (I × κ)) :
    MIPStarRE.Quantum.Measurement Outcome I :=
  M.mapEffects (sliceEffects k₀)
    (by
      ext i j
      change (1 : MIPStarRE.Quantum.Op (I × κ)) (i, k₀) (j, k₀) = _
      simp [Matrix.one_apply])
    (fun {_} h => Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp h).submatrix (fun i => (i, k₀))))

/-- Restricting a POVM to a fixed ancillary coordinate commutes with
deterministic relabeling of its outcomes. -/
theorem compressAt_postprocess
    {A B I κ : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] [Fintype κ] [DecidableEq κ]
    (k₀ : κ) (M : MIPStarRE.Quantum.Measurement A (I × κ)) (f : A → B) :
    (M.postprocess f).compressAt k₀ = (M.compressAt k₀).postprocess f :=
  (M.mapEffects_postprocess (sliceEffects k₀) _ _ f).symm

end MIPStarRE.Quantum.Measurement

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

namespace Measurement

/-- Compressing the completed one-measurement Naimark dilation at its
distinguished `none` coordinate recovers the original POVM. -/
theorem compressAt_dilatedMeasurement
    {A I : Type} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I]
    (a₀ : A) (M : MIPStarRE.Quantum.Measurement A I) :
    (dilatedMeasurement a₀ M).compressAt none = M := by
  apply MIPStarRE.Quantum.Measurement.ext
  intro a
  ext i j
  exact dilatedMeasurement_compression a₀ a M i j

end Measurement

/-- Ground-slice compression preserves exactly the off-diagonal consistency
defect when the bipartite state is padded at the same two ancillary
coordinates. This is an equality of POVM correlations and does not assert that
the compressed measurements are projective. -/
theorem consistencyDefect_padState_compressAt
    {X Outcome I J κA κB : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (μ : Distribution X)
    (MA : X → MIPStarRE.Quantum.Measurement Outcome (I × κA))
    (MB : X → MIPStarRE.Quantum.Measurement Outcome (J × κB))
    (a₀ : κA) (b₀ : κB) (ψ : EuclideanSpace ℂ (I × J)) :
    bipartiteDefect μ
        MA
        MB
        (padState a₀ b₀ ψ) =
      bipartiteDefect μ
        (fun x => (MA x).compressAt a₀)
        (fun x => (MB x).compressAt b₀)
        ψ := by
  unfold bipartiteDefect consistencyDefect
  apply avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    change vectorQForm (padState a₀ b₀ ψ)
        (heteroKron ((MA x).effect a) 1 * heteroKron 1 ((MB x).effect b)) =
      vectorQForm ψ
        (heteroKron (((MA x).compressAt a₀).effect a) 1 *
          heteroKron 1 (((MB x).compressAt b₀).effect b))
    simpa only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul] using
      stateQForm_padState a₀ b₀ ψ
        (((MA x).compressAt a₀).effect a)
        (((MB x).compressAt b₀).effect b)
        ((MA x).effect a) ((MB x).effect b)
        (fun i j => rfl) (fun i j => rfl)

end MIPStarRE.QPBT
