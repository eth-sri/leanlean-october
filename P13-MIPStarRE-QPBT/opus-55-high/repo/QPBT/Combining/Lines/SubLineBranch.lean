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

/-! ## The three ranges of extended coordinates -/

/-- Every extended coordinate is an `X`-block coordinate, a `Z`-block
coordinate, or one of the two scalar coordinates.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem extendedCoordinate_cases (m : ℕ) (k : Fin (2 * m + 2)) :
    (∃ i : Fin m, k = embX m i) ∨ (∃ j : Fin m, k = embZ m j) ∨
      k = alphaVar m ∨ k = betaVar m := by
  rcases lt_or_ge k.val m with hk | hk
  · exact Or.inl ⟨⟨k, hk⟩, Fin.ext rfl⟩
  rcases lt_or_ge k.val (2 * m) with hk2 | hk2
  · exact Or.inr (Or.inl ⟨⟨k - m, by omega⟩, Fin.ext (Nat.add_sub_cancel' hk).symm⟩)
  right; right
  rw [Fin.ext_iff, Fin.ext_iff, alphaVar_val, betaVar_val]
  omega

/-! ## Linearity of the identification of the two scalar fields -/

variable (P : AdmissibleParams)

/-- The identification of the two scalar fields is additive on extended
points.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_add (u v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointToPauli P (u + v) =
      directPointToPauli P u + directPointToPauli P v := by
  funext i
  change extendedDirectScalarEquiv P (u i + v i) =
    extendedDirectScalarEquiv P (u i) + extendedDirectScalarEquiv P (v i)
  rw [map_add]

/-- The identification of the two scalar fields carries a scalar multiple of
an extended point to the multiple by the identified scalar.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_smul (t : DirectScalarQ P.extendedDirectLd)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointToPauli P (t • u) =
      extendedDirectScalarEquiv P t • directPointToPauli P u := by
  funext i
  change extendedDirectScalarEquiv P (t * u i) =
    extendedDirectScalarEquiv P t * extendedDirectScalarEquiv P (u i)
  rw [map_mul]

/-! ## The coordinate index carried by each source line -/

/-- The first coordinate of the source space.  Blueprint
`eq:chi-func`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
def subLineFirstIndex : Fin P.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one P.one_le_m⟩

/-- The coordinate index carried by the source `X` line of a branch: the
stored extended coordinate when it is an `X`-block coordinate, and the first
coordinate otherwise.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineXIndex (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : k.val < P.m then ⟨k.val, h⟩ else subLineFirstIndex P

/-- The coordinate index carried by the source `Z` line of a branch: the
stored extended coordinate when it is a `Z`-block coordinate, and the first
coordinate otherwise.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineZIndex (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : P.m ≤ k.val ∧ k.val < 2 * P.m then ⟨k.val - P.m, by omega⟩
  else subLineFirstIndex P

/-- At an `X`-block coordinate the source `X` line carries that coordinate. -/
theorem subLineXIndex_embX (i : Fin P.m) :
    subLineXIndex P (embX P.m i) = i := by
  simp [subLineXIndex, embX_val]

/-- At an `X`-block coordinate the source `Z` line carries the first
coordinate. -/
theorem subLineZIndex_embX (i : Fin P.m) :
    subLineZIndex P (embX P.m i) = subLineFirstIndex P := by
  rw [subLineZIndex, dif_neg (by rw [embX_val]; omega)]

/-- At a `Z`-block coordinate the source `Z` line carries that coordinate. -/
theorem subLineZIndex_embZ (j : Fin P.m) :
    subLineZIndex P (embZ P.m j) = j := by
  rw [subLineZIndex, dif_pos (by rw [embZ_val]; omega)]
  exact Fin.ext (by simp [embZ_val])

/-! ## The two directions of a branch -/

/-- The direction of the extended line of a branch: the elementary direction
at the stored coordinate in the axis branch, and the extended direction with
the coordinates preceding the stored coordinate replaced by zero in the
diagonal branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineExtDirection (kind : LineKind)
    (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd :=
  match kind with
  | .axis => coordinateDirection k
  | .diagonal => directPrefixProjection (D := P.extendedDirectLd) k w

/-- The direction of a source line of a branch: the elementary direction at
its coordinate index in the axis branch, and the given source block with the
coordinates preceding that index replaced by zero in the diagonal branch.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineSourceDirection (kind : LineKind)
    (i : Fin P.m) (v : Fin P.m → PauliScalar P) : Fin P.m → PauliScalar P :=
  match kind with
  | .axis => coordinateDirection i
  | .diagonal => prefixProjection (P := P.toLdParams) i v

/-! ## Incidence of the two source blocks of a branch direction -/

/-- The `X` block of the direction of the extended line of a branch lies in
the line spanned by the direction of its source `X` line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_subLineExtDirection_mem_span (kind : LineKind) (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projX (directPointToPauli P (subLineExtDirection P kind k w)) ∈
      Submodule.span (PauliScalar P)
        (Set.singleton (subLineSourceDirection P kind (subLineXIndex P k)
          (projX (directPointToPauli P w)))) := by
  rcases extendedCoordinate_cases P.m k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind <;>
    simp only [subLineExtDirection, subLineSourceDirection, directPointToPauli_coordinateDirection,
      subLineXIndex_embX, projX_coordinateDirection_embX, projX_coordinateDirection_embZ, projX_coordinateDirection_alphaVar, projX_coordinateDirection_betaVar, projX_directPrefixProjection_embX, projX_directPrefixProjection_embZ, projX_directPrefixProjection_alphaVar, projX_directPrefixProjection_betaVar] <;>
    first | exact Submodule.mem_span_singleton_self _ | exact Submodule.zero_mem _

/-- The `Z` block of the direction of the extended line of a branch lies in
the line spanned by the direction of its source `Z` line.  In the diagonal
branch at an `X`-block coordinate the `Z` block is untruncated, which is why
the source `Z` line carries the first coordinate there.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_subLineExtDirection_mem_span (kind : LineKind) (k : Fin (2 * P.m + 2))
    (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    projZ (directPointToPauli P (subLineExtDirection P kind k w)) ∈
      Submodule.span (PauliScalar P)
        (Set.singleton (subLineSourceDirection P kind (subLineZIndex P k)
          (projZ (directPointToPauli P w)))) := by
  rcases extendedCoordinate_cases P.m k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind <;>
    simp only [subLineExtDirection, subLineSourceDirection, directPointToPauli_coordinateDirection,
      subLineZIndex_embX, subLineZIndex_embZ, projZ_coordinateDirection_embX, projZ_coordinateDirection_embZ, projZ_coordinateDirection_alphaVar, projZ_coordinateDirection_betaVar, projZ_directPrefixProjection_embX, projZ_directPrefixProjection_embZ, projZ_directPrefixProjection_alphaVar, projZ_directPrefixProjection_betaVar] <;>
    first | exact Submodule.mem_span_singleton_self _ | exact Submodule.zero_mem _

/-! ## Canonical representatives of the two source blocks -/

/-- Replacing an extended point by its canonical representative in the
direction of the extended line does not change the canonical representative
of a source block in the direction of the source line, as soon as that block
of the extended direction lies in the line spanned by the source direction.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineRepMap_proj_directPointToPauli_lineRepMap
    (proj : (Fin (2 * P.m + 2) → PauliScalar P) → Fin P.m → PauliScalar P)
    (hadd : ∀ a b, proj (a + b) = proj a + proj b)
    (hsmul : ∀ (s : PauliScalar P) a, proj (s • a) = s • proj a)
    (v x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (d : Fin P.m → PauliScalar P)
    (hdir : proj (directPointToPauli P v) ∈
      Submodule.span (PauliScalar P) ({d} : Set (Fin P.m → PauliScalar P))) :
    lineRepMap d (proj (directPointToPauli P (lineRepMap v x))) =
      lineRepMap d (proj (directPointToPauli P x)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hx : x = lineRepMap v x + t • v := by
    rw [ht]
    abel
  conv_rhs => rw [hx, directPointToPauli_add, directPointToPauli_smul, hadd, hsmul, ← hc,
    smul_smul, lineRepMap_add_smul]

/-- Moving along the extended line does not change the canonical
representative of a source block in the direction of the source line. -/
theorem lineRepMap_proj_lineRepMap_add_smul
    (proj : (Fin (2 * P.m + 2) → PauliScalar P) → Fin P.m → PauliScalar P)
    (hadd : ∀ a b, proj (a + b) = proj a + proj b)
    (hsmul : ∀ (s : PauliScalar P) a, proj (s • a) = s • proj a)
    (v x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (t : DirectScalarQ P.extendedDirectLd) (d : Fin P.m → PauliScalar P)
    (hdir : proj (directPointToPauli P v) ∈
      Submodule.span (PauliScalar P) ({d} : Set (Fin P.m → PauliScalar P))) :
    lineRepMap d (proj (directPointToPauli P (lineRepMap v x + t • v))) =
      lineRepMap d (proj (directPointToPauli P x)) := by
  rw [← lineRepMap_proj_directPointToPauli_lineRepMap P proj hadd hsmul v _ d hdir,
    lineRepMap_add_smul, lineRepMap_apply_self,
    lineRepMap_proj_directPointToPauli_lineRepMap P proj hadd hsmul v x d hdir]

end

end MIPStarRE.QPBT
