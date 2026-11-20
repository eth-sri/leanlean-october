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
theorem extendedCoordinate_cases {m : ℕ} (k : Fin (2 * m + 2)) :
    (∃ i : Fin m, k = embX m i) ∨ (∃ j : Fin m, k = embZ m j) ∨
      k = alphaVar m ∨ k = betaVar m := by
  rcases lt_or_ge k.val m with hk | hk
  · exact Or.inl ⟨⟨k.val, hk⟩, Fin.ext (embX_val m ⟨k.val, hk⟩).symm⟩
  · rcases lt_or_ge k.val (2 * m) with hk2 | hk2
    · refine Or.inr (Or.inl ⟨⟨k.val - m, by omega⟩, Fin.ext ?_⟩)
      change k.val = m + (k.val - m)
      omega
    · rcases Nat.lt_or_ge k.val (2 * m + 1) with hk4 | hk4
      · refine Or.inr (Or.inr (Or.inl (Fin.ext ?_)))
        rw [alphaVar_val]
        omega
      · refine Or.inr (Or.inr (Or.inr (Fin.ext ?_)))
        rw [betaVar_val]
        omega

/-! ## Linearity of the identification of the two scalar fields -/

variable (P : AdmissibleParams)

/-- The identification of the two scalar fields is additive on extended
points.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_add
    (u v : DirectPoint P.extendedDirectLd) :
    directPointToPauli (u + v) =
      directPointToPauli u + directPointToPauli v := by
  funext i
  change extendedDirectScalarEquiv P (u i + v i) =
    extendedDirectScalarEquiv P _ + extendedDirectScalarEquiv P (v i)
  simp

/-- The identification of the two scalar fields carries a scalar multiple of
an extended point to the multiple by the identified scalar.  Blueprint
`def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem directPointToPauli_smul
    (t : DirectScalarQ P.extendedDirectLd)
    (u : DirectPoint P.extendedDirectLd) :
    directPointToPauli (t • u) =
      extendedDirectScalarEquiv P t • directPointToPauli u := by
  funext i
  change extendedDirectScalarEquiv P (t * u i) =
    extendedDirectScalarEquiv P t * extendedDirectScalarEquiv P _
  simp

/-! ## The coordinate index carried by each source line -/

/-- The first coordinate of the source space.  Blueprint
`eq:chi-func`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:958-961`.
-/
def subLineFirstIndex : Fin P.m :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one P.one_le_m⟩

variable {P} in
/-- The coordinate index carried by the source `X` line of a branch: the
stored extended coordinate when it is an `X`-block coordinate, and the first
coordinate otherwise.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineXIndex (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : k.val < P.m then ⟨k.val, h⟩ else subLineFirstIndex P

variable {P} in
/-- The coordinate index carried by the source `Z` line of a branch: the
stored extended coordinate when it is a `Z`-block coordinate, and the first
coordinate otherwise.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineZIndex (k : Fin (2 * P.m + 2)) : Fin P.m :=
  if h : P.m ≤ k.val ∧ k.val < 2 * P.m then ⟨k.val - P.m, by omega⟩
  else subLineFirstIndex P

/-- At an `X`-block coordinate the source `X` line carries that coordinate. -/
theorem subLineXIndex_embX (i : Fin P.m) :
    subLineXIndex (embX P.m i) = i := by
  have h : (embX P.m i).val < P.m := by
    exact i.isLt
  rw [subLineXIndex, dif_pos h]
  solve_by_elim [Fin.ext]

/-- At an `X`-block coordinate the source `Z` line carries the first
coordinate. -/
theorem subLineZIndex_embX (i : Fin P.m) :
    subLineZIndex (embX P.m i) = subLineFirstIndex P := by
  simp [embX_val, subLineZIndex]

/-- At a `Z`-block coordinate the source `Z` line carries that coordinate. -/
theorem subLineZIndex_embZ (j : Fin P.m) :
    subLineZIndex (embZ P.m j) = j := by
  have h : P.m ≤ (embZ P.m j).val ∧ (embZ P.m j).val < 2 * P.m := by
    rw [embZ_val]
    omega
  rw [subLineZIndex, dif_pos h]
  simp [embZ_val]

/-! ## The two directions of a branch -/

variable {P} in
/-- The direction of the extended line of a branch: the elementary direction
at the stored coordinate in the axis branch, and the extended direction with
the coordinates preceding the stored coordinate replaced by zero in the
diagonal branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineExtDirection (kind : LineKind)
    (k : Fin (2 * P.m + 2))
    (w : DirectPoint P.extendedDirectLd) :
    DirectPoint P.extendedDirectLd :=
  match kind with
  | .axis => coordinateDirection k
  | .diagonal => directPrefixProjection (D := P.extendedDirectLd) k w

variable {P} in
/-- The direction of a source line of a branch: the elementary direction at
its coordinate index in the axis branch, and the given source block with the
coordinates preceding that index replaced by zero in the diagonal branch.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
def subLineSourceDirection (kind : LineKind)
    (i : Fin P.m) (v : PauliPoint P) : PauliPoint P :=
  match kind with
  | .axis => coordinateDirection i
  | .diagonal => prefixProjection (P := P.toLdParams) i v

/-! ## Incidence of the two source blocks of a branch direction -/

section

variable (kind : LineKind) (k : Fin (2 * P.m + 2))
  (w : DirectPoint P.extendedDirectLd)

/-- The `X` block of the direction of the extended line of a branch lies in
the line spanned by the direction of its source `X` line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_subLineExtDirection_mem_span :
    projX (directPointToPauli (subLineExtDirection kind k w)) ∈
      Submodule.span (PauliScalar P)
        (Set.singleton (subLineSourceDirection kind (subLineXIndex k)
          (projX (directPointToPauli w)))) := by
  rcases extendedCoordinate_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind
  · rw [subLineXIndex_embX]
    change projX (directPointToPauli
      (coordinateDirection (embX P.m i))) ∈ _
    rw [((congrArg projX
      (directPointToPauli_coordinateDirection P (embX P.m i))).trans
      (projX_coordinateDirection_embX i))]
    exact Submodule.mem_span_singleton_self _
  · rw [subLineXIndex_embX]
    exact Submodule.mem_span_singleton_self _
  · change projX (directPointToPauli
      (coordinateDirection (embZ P.m j))) ∈ _
    rw [((congrArg projX
      (directPointToPauli_coordinateDirection P (embZ P.m j))).trans
      (projX_coordinateDirection_embZ j))]
    exact Submodule.zero_mem _
  · change projX (directPointToPauli
      (directPrefixProjection (embZ P.m j) w)) ∈ _
    simp [projX_directPrefixProjection_embZ]
  · change projX (directPointToPauli
      (coordinateDirection (alphaVar P.m))) ∈ _
    rw [((congrArg projX
      (directPointToPauli_coordinateDirection P (alphaVar P.m))).trans
      projX_coordinateDirection_alphaVar)]
    exact Submodule.zero_mem _
  · change projX (directPointToPauli
      (directPrefixProjection (alphaVar P.m) w)) ∈ _
    simp [projX_directPrefixProjection_alphaVar]
  · change projX (directPointToPauli
      (coordinateDirection (betaVar P.m))) ∈ _
    rw [((congrArg projX
      (directPointToPauli_coordinateDirection P (betaVar P.m))).trans
      projX_coordinateDirection_betaVar)]
    exact Submodule.zero_mem _
  · change projX (directPointToPauli
      (directPrefixProjection (betaVar P.m) w)) ∈ _
    simp [projX_directPrefixProjection_betaVar]

/-- The `Z` block of the direction of the extended line of a branch lies in
the line spanned by the direction of its source `Z` line.  In the diagonal
branch at an `X`-block coordinate the `Z` block is untruncated, which is why
the source `Z` line carries the first coordinate there.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_subLineExtDirection_mem_span :
    projZ (directPointToPauli (subLineExtDirection kind k w)) ∈
      Submodule.span (PauliScalar P)
        (Set.singleton (subLineSourceDirection kind (subLineZIndex k)
          (projZ (directPointToPauli w)))) := by
  rcases extendedCoordinate_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;>
    cases kind
  · change projZ (directPointToPauli
      (coordinateDirection (embX P.m i))) ∈ _
    rw [((congrArg projZ
      (directPointToPauli_coordinateDirection P (embX P.m i))).trans
      (projZ_coordinateDirection_embX i))]
    exact Submodule.zero_mem _
  · rw [subLineZIndex_embX]
    change projZ (directPointToPauli
      (directPrefixProjection (embX P.m i) w)) ∈ _
    rw [projZ_directPrefixProjection_embX]
    exact Submodule.mem_span_singleton_self _
  · rw [subLineZIndex_embZ]
    change projZ (directPointToPauli
      (coordinateDirection (embZ P.m j))) ∈ _
    rw [((congrArg projZ
      (directPointToPauli_coordinateDirection P (embZ P.m j))).trans
      (projZ_coordinateDirection_embZ j))]
    exact Submodule.mem_span_singleton_self _
  · rw [subLineZIndex_embZ]
    change projZ (directPointToPauli
      (directPrefixProjection (embZ P.m j) w)) ∈ _
    rw [projZ_directPrefixProjection_embZ]
    exact Submodule.mem_span_singleton_self _
  · change projZ (directPointToPauli
      (coordinateDirection (alphaVar P.m))) ∈ _
    rw [((congrArg projZ
      (directPointToPauli_coordinateDirection P (alphaVar P.m))).trans
      projZ_coordinateDirection_alphaVar)]
    exact Submodule.zero_mem _
  · change projZ (directPointToPauli
      (directPrefixProjection (alphaVar P.m) w)) ∈ _
    simp [projZ_directPrefixProjection_alphaVar]
  · change projZ (directPointToPauli
      (coordinateDirection (betaVar P.m))) ∈ _
    rw [((congrArg projZ
      (directPointToPauli_coordinateDirection P (betaVar P.m))).trans
      projZ_coordinateDirection_betaVar)]
    exact Submodule.zero_mem _
  · change projZ (directPointToPauli
      (directPrefixProjection (betaVar P.m) w)) ∈ _
    simp [projZ_directPrefixProjection_betaVar]

end

/-! ## Canonical representatives of the two source blocks -/

/-- Replacing an extended point by its canonical representative in the
direction of the extended line does not change the canonical representative
of its `X` block in the direction of the source `X` line, as soon as the `X`
block of the extended direction lies in the line spanned by the source
direction.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineRepMap_projX_directPointToPauli_lineRepMap
    {v : DirectPoint P.extendedDirectLd} (x : DirectPoint P.extendedDirectLd)
    {dX : PauliPoint P}
    (hdir : projX (directPointToPauli v) ∈
      Submodule.span (PauliScalar P) ({dX} : Set (PauliPoint P))) :
    lineRepMap dX (projX (directPointToPauli (lineRepMap v x))) =
      lineRepMap dX (projX (directPointToPauli x)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hx : x = lineRepMap v x + t • v := by
    rw [ht]
    abel
  have hstep : projX (directPointToPauli x) =
      projX (directPointToPauli (lineRepMap v x)) +
        (extendedDirectScalarEquiv P t * c) • dX := by
    conv_lhs => rw [hx]
    rw [directPointToPauli_add, directPointToPauli_smul, projX_add, projX_smul,
      ← hc]
    module
  rw [hstep, lineRepMap_add_smul]

/-- Replacing an extended point by its canonical representative in the
direction of the extended line does not change the canonical representative
of its `Z` block in the direction of the source `Z` line, as soon as the `Z`
block of the extended direction lies in the line spanned by the source
direction.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineRepMap_projZ_directPointToPauli_lineRepMap
    {v : DirectPoint P.extendedDirectLd} (x : DirectPoint P.extendedDirectLd)
    {dZ : PauliPoint P}
    (hdir : projZ (directPointToPauli v) ∈
      Submodule.span (PauliScalar P) ({dZ} : Set (PauliPoint P))) :
    lineRepMap dZ (projZ (directPointToPauli (lineRepMap v x))) =
      lineRepMap dZ (projZ (directPointToPauli x)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
  have hx : x = lineRepMap v x + t • v := by
    rw [ht]
    abel
  have hstep : projZ (directPointToPauli x) =
      projZ (directPointToPauli (lineRepMap v x)) +
        (extendedDirectScalarEquiv P t * c) • dZ := by
    conv_lhs => rw [hx]
    rw [directPointToPauli_add, directPointToPauli_smul, projZ_add, projZ_smul,
      ← hc]
    module
  rw [hstep, lineRepMap_add_smul]

end

end MIPStarRE.QPBT
