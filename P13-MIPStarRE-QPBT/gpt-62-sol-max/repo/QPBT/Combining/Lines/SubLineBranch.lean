module

public import QPBT.Combining.Lines.SubLineTransport

/-!
# The branch data of the sub-line sampling procedure

The sampling procedure of the sub-line lemma draws a line kind, a stored
extended coordinate, and an unrestricted extended direction, and forms from
them the direction of the extended line: the elementary direction at the
stored coordinate in the axis branch, and the extended direction with the
coordinates preceding the stored coordinate replaced by zero in the diagonal
branch.  The two source lines are then read off the two coordinate blocks.
This module fixes the coordinate index that each source line must carry: the
stored coordinate itself when it belongs to that block, the first coordinate
otherwise.  With that choice the source block of the extended direction always
lies in the line spanned by the corresponding source direction, which is the
incidence hypothesis of the two projection lemmas.  The module also records
that moving an extended point to its canonical representative does not change
the canonical representative of either of its source blocks.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989; the prefix truncation is that of
blueprint `def:ld-question-distribution`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## Linearity of the identification of the two scalar fields -/

/-- The identification of the two scalar fields is additive on extended
points.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_add (P : AdmissibleParams)
    (u v : DirectPoint P.extendedDirectLd) :
    directPointToPauli P (u + v) =
      directPointToPauli P u + directPointToPauli P v := rfl

/-- The identification of the two scalar fields carries a scalar multiple of
an extended point to the multiple by the identified scalar.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_smul (P : AdmissibleParams)
    (t : DirectScalarQ P.extendedDirectLd)
    (u : DirectPoint P.extendedDirectLd) :
    directPointToPauli P (t • u) =
      extendedDirectScalarEquiv P t • directPointToPauli P u := rfl

/-- The starting coordinate of a Pauli block in the extended space. -/
def blockOffset (m : ℕ) : PauliKind → ℕ
  | .X => 0
  | .Z => m

def blockEmbed (m : ℕ) : PauliKind → Fin m → Fin (2 * m + 2)
  | .X => embX m
  | .Z => embZ m

private theorem blockEmbed_val {m : ℕ} (W : PauliKind) (j : Fin m) :
    (blockEmbed m W j).val = blockOffset m W + j.val := by cases W <;> simp [blockEmbed, blockOffset, embX, embZ, finCombineEquiv, Nat.add_comm]

section

variable (P : AdmissibleParams)
include P

/-- Project to one block, transporting the scalars to the source field. -/
def subLineProject (W : PauliKind)
    (u : DirectPoint P.extendedDirectLd) : PauliPoint P :=
  fun j => directPointToPauli P u (blockEmbed P.m W j)

theorem subLineProject_affine (W : PauliKind)
    (b v : DirectPoint P.extendedDirectLd)
    (t : DirectScalarQ P.extendedDirectLd) :
    subLineProject P W (b + t • v) = subLineProject P W b +
      extendedDirectScalarEquiv P t • subLineProject P W v := rfl

/-- A source line uses the stored index when it lies in the block, or the first coordinate. -/
def subLineIndex (W : PauliKind) (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : blockOffset P.m W ≤ k.val ∧ k.val < blockOffset P.m W + P.m then
    ⟨k.val - blockOffset P.m W, by omega⟩
  else ⟨0, P.one_le_m⟩

abbrev subLineXIndex := subLineIndex P .X
abbrev subLineZIndex := subLineIndex P .Z

end

/-! ## The two directions of a branch -/

/-- The direction of the extended line of a branch: the elementary direction
at the stored coordinate in the axis branch, and the extended direction with
the coordinates preceding the stored coordinate replaced by zero in the
diagonal branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineExtDirection (P : AdmissibleParams) (kind : LineKind)
    (k : Fin (2 * P.m + 2))
    (w : DirectPoint P.extendedDirectLd) :
    DirectPoint P.extendedDirectLd :=
  match kind with
  | .axis => coordinateDirection k
  | .diagonal => directPrefixProjection (D := P.extendedDirectLd) k w

/-- The direction of a source line of a branch: the elementary direction at
its coordinate index in the axis branch, and the given source block with the
coordinates preceding that index replaced by zero in the diagonal branch.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineSourceDirection (P : AdmissibleParams) (kind : LineKind)
    (i : Fin P.m) (v : PauliPoint P) : PauliPoint P :=
  match kind with
  | .axis => coordinateDirection i
  | .diagonal => prefixProjection (P := P.toLdParams) i v

section

variable (P : AdmissibleParams) (W : PauliKind)
    (kind : LineKind) (k : Fin (2 * P.m + 2))
include P W kind k

/-- The projected direction is either the source direction or zero. The only
relevant comparisons are with the lower and upper endpoints of the block. -/
theorem subLineProject_direction_mem_span
    (v : DirectPoint P.extendedDirectLd) :
    subLineProject P W (subLineExtDirection P kind k v) ∈ Submodule.span (PauliScalar P)
      {subLineSourceDirection P kind (subLineIndex P W k) (subLineProject P W v)} := by
  by_cases h : blockOffset P.m W ≤ k.val ∧ k.val < blockOffset P.m W + P.m
  · suffices e : subLineProject P W (subLineExtDirection P kind k v) =
        subLineSourceDirection P kind (subLineIndex P W k) (subLineProject P W v) by simp_all
    funext j
    cases kind <;>
      simp only [subLineExtDirection, subLineSourceDirection, subLineIndex, dif_pos h,
        subLineProject, directPointToPauli, coordinateDirection, Pi.single_apply, Fin.ext_iff,
        directPrefixProjection, prefixProjection, blockEmbed_val] <;>
      split_ifs <;> simp_all <;> omega
  · cases kind with
    | axis =>
        suffices e : subLineProject P W (subLineExtDirection P .axis k v) = 0 by simp_all
        funext j
        have hn : blockEmbed P.m W j ≠ k := by
          rw [Ne, Fin.ext_iff, blockEmbed_val]
          have := j.isLt
          omega
        simp [subLineProject, subLineExtDirection, directPointToPauli, coordinateDirection,
          Pi.single_eq_of_ne hn]
    | diagonal =>
        by_cases hk : k.val < blockOffset P.m W
        · suffices e : subLineProject P W (subLineExtDirection P .diagonal k v) =
              subLineSourceDirection P .diagonal (subLineIndex P W k) (subLineProject P W v) by simp_all
          funext j
          have hj : ¬ (blockEmbed P.m W j).val < k.val := by rw [blockEmbed_val]; omega
          simp [subLineProject, subLineExtDirection, subLineSourceDirection, subLineIndex,
            directPointToPauli, directPrefixProjection, prefixProjection, hj, h]
        · suffices e : subLineProject P W (subLineExtDirection P .diagonal k v) = 0 by simp_all
          funext j
          have hj : (blockEmbed P.m W j).val < k.val := by
            rw [blockEmbed_val]
            have := j.isLt
            omega
          simp [subLineProject, subLineExtDirection, directPointToPauli, directPrefixProjection, hj]

/-- Resampling along an extended line preserves the canonical representative of a source block. -/
theorem subLineProject_representative
    (x v : DirectPoint P.extendedDirectLd)
    (t : DirectScalarQ P.extendedDirectLd) :
    let V := subLineExtDirection P kind k v
    let d := subLineSourceDirection P kind (subLineIndex P W k) (subLineProject P W v)
    lineRepMap d (subLineProject P W (lineRepMap V x + t • V)) =
      lineRepMap d (subLineProject P W x) := by
  dsimp only
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (subLineProject_direction_mem_span P W kind k v)
  grind only [subLineProject_affine, smul_smul, lineRepMap_add_smul, directLineRepParameter_spec (subLineExtDirection P kind k v) x]

end

end

end MIPStarRE.QPBT
