module

public import QPBT.Types

public import Mathlib
public import QPBT.Algebra.RowEchelon
public import QPBT.Algebra.Subspaces

open scoped Classical

/-!
# Lines and canonical representatives

The classical and Pauli question distributions use affine lines in a finite
coordinate space.  This module keeps the zero-direction case explicit and
provides the canonical projection used for line representatives.

## References

The source-facing nodes are blueprint `def:line`, `prop:line-equiv`, and
`def:line-representative`; the formalization support nodes are blueprint
`lem:line-rep-kernel` and `lem:line-rep-incidence`.
The paper origin is `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:102-174`.

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators

variable {K : Type*} [Field K]

variable {m : ℕ}

/--
The affine line through `u` in direction `v`, including the singleton case
`v = 0`.  Blueprint `def:line`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def linePoints
    (u v : MIPStarRE.QPBT.Coordinates m K) : Set (MIPStarRE.QPBT.Coordinates m K) :=
  {x | ∃ t : K, x = u + t • v}

/-- The elementary coordinate direction used in the axis-parallel predicate of
blueprint `def:line`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def coordinateDirection
    (i : Fin m) : MIPStarRE.QPBT.Coordinates m K :=
  Pi.single i 1

/--
Changing the base point to another point on a line leaves the line unchanged.
This is blueprint `prop:line-equiv`,
with paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:128-132`.
-/
theorem linePoints_eq_of_mem
    (u v u' : MIPStarRE.QPBT.Coordinates m K) (h : u' ∈ linePoints u v) :
    linePoints u v = linePoints u' v := by
  obtain ⟨t, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s - t, by module⟩
  · rintro ⟨s, rfl⟩
    exact ⟨t + s, by module⟩

/--
The canonical linear representative map of a line direction.  It projects onto
the coordinate complement of the span of `v`; for `v = 0` the span is bottom,
so the resulting map is the identity.  Blueprint `def:line-representative`;
paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
noncomputable def lineRepMap
    (v : MIPStarRE.QPBT.Coordinates m K) :  MIPStarRE.QPBT.Coordinates m K  →ₗ[K]  MIPStarRE.QPBT.Coordinates m K  :=
  canonicalProjOfKernel (Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K)))

/-- The least coordinate at which a nonzero line direction is nonzero. This is
Lean-only support for the elementary formula for the canonical representative;
coordinates use the same left-to-right order as paper `def:cl-canonical`. -/
noncomputable def linePivotIndex  (v : MIPStarRE.QPBT.Coordinates m K) (hv : v ≠ 0) : Fin m := by
  let support := Finset.univ.filter fun j => v j ≠ 0
  have hsupport : support.Nonempty := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    apply h
    refine ⟨j, ?_⟩
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hj
  exact support.min' hsupport

/-- The pivot coordinate of a nonzero direction is nonzero. -/
theorem linePivotIndex_ne_zero  (v : MIPStarRE.QPBT.Coordinates m K) (hv : v ≠ 0) :
    v (linePivotIndex v hv) ≠ 0 := by
  have hmem :
      linePivotIndex v hv ∈ Finset.univ.filter fun j => v j ≠ 0 := by
    unfold linePivotIndex
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

/-- Every coordinate before the pivot coordinate of a nonzero direction vanishes. -/
theorem linePivotIndex_zero_before  (v : MIPStarRE.QPBT.Coordinates m K) (hv : v ≠ 0)
    (i : Fin m) (hi : i < linePivotIndex v hv) : v i = 0 := by
  by_contra hvi
  unfold linePivotIndex at hi
  exact (not_le_of_gt hi) (Finset.min'_le _ i (by simp [hvi]))

/--
The elementary canonical representative of the line through `u` in direction
`v`. The zero direction returns `u`. Otherwise it subtracts the unique multiple
of `v` that makes the least nonzero coordinate of `v` vanish. This Lean-only
formula is used to replace the general canonical-complement construction in the
compact Palomar statement while preserving paper `def:line-representative`.
-/
noncomputable def explicitLineRep
    (u v : MIPStarRE.QPBT.Coordinates m K) : MIPStarRE.QPBT.Coordinates m K :=
  open Classical in
    if hv : v = 0 then u
    else
      let j := linePivotIndex v hv
      u - (u j / v j) • v

/- The point-valued companion to `lineRepMap`; Lean-only notation for the
canonical representative in `def:line-representative`. -/

/--
Formalization support node blueprint `lem:line-rep-kernel` for
`def:line-representative` (paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`).
The canonical representative map is a projection whose kernel is the line
`K v`, so a point and its canonical representative differ by a scalar multiple
of the direction.
-/
theorem sub_lineRepMap_mem_span  (v u : MIPStarRE.QPBT.Coordinates m K) :
    u - lineRepMap v u ∈ Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K)) := by
  have hc  :=
    (isCompl_registerSubmodule_canonicalComplement
      (Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K)))).symm
  have hrep : lineRepMap v u =
      (registerSubmodule K
        (canonicalComplement (Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K))))).projection
        (Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K))) hc u := rfl
  rw [hrep, ← Submodule.projection_eq_self_sub_projection hc u]
  exact Submodule.projection_apply_mem hc.symm u

/--
The canonical line representative is exactly the elementary least-pivot
formula `explicitLineRep`, for every point and direction, including `v = 0`.
This is a Lean-only representation theorem for the compact Palomar statement;
it proves an exact identity and does not alter paper `def:line-representative`.
-/
theorem lineRepMap_apply_eq_explicitLineRep  (v u : MIPStarRE.QPBT.Coordinates m K) :
    lineRepMap v u = explicitLineRep u v := by
  by_cases hv : v = 0
  · subst v
    have hspan : Submodule.span K ({0} : Set (MIPStarRE.QPBT.Coordinates m K)) = ⊥ := by simp
    have h := sub_lineRepMap_mem_span (0 : MIPStarRE.QPBT.Coordinates m K) u
    rw [hspan, Submodule.mem_bot, sub_eq_zero] at h
    simpa [explicitLineRep] using h.symm
  · let j := linePivotIndex v hv
    have hjv : v j ≠ 0 := linePivotIndex_ne_zero v hv
    let w  := (v j)⁻¹ • v
    let B  := Matrix.replicateRow (Fin 1) w
    let pivot  :=
      ({j} : Finset (Fin m)).orderEmbOfFin (Finset.card_singleton j)
    have hpivot (i : Fin 1) : pivot i = j := by
      simp [pivot]
    have hB : IsReducedRowEchelon B pivot := by
      constructor
      · intro i k
        have hik : i = k := Subsingleton.elim _ _
        subst k
        simp [B, w, hpivot, hjv]
      · intro i k hki
        have hkj  := by simpa [hpivot] using hki
        have hvk  := linePivotIndex_zero_before v hv k hkj
        simp [B, w, hvk]
    have hrange : Set.range B.row = {w} := by aesop
    have hspan :
        Submodule.span K (Set.range B.row) =
          Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K)) := by
      rw [hrange, Submodule.span_singleton_eq_span_singleton]
      refine ⟨Units.mk0 (v j) hjv, ?_⟩
      funext k
      simp [w, hjv]
    have hcomplement :
        canonicalComplement (Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K))) =
          ({j} : Finset (Fin m))ᶜ := by
      rw [← hspan, hB.canonicalComplement_eq_nonpivot_indices]
      simp [pivot]
    have hrep_mem :
        lineRepMap v u ∈
          registerSubmodule K
            (canonicalComplement (Submodule.span K ({v} : Set (MIPStarRE.QPBT.Coordinates m K)))) := by
      simp [lineRepMap, canonicalProjOfKernel]
    rw [hcomplement, registerSubmodule_eq_spanSubset] at hrep_mem
    have hrep_zero  :=
      Pi.mem_spanSubset_iff.mp hrep_mem j (by simp)
    obtain ⟨t, ht⟩ :=
      Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v u)
    have htj : t = u j / v j := by
      apply (eq_div_iff hjv).2
      have := congrFun ht j
      simpa [hrep_zero] using this
    have hrep : lineRepMap v u = u - t • v := by
      rw [ht]
      abel
    rw [explicitLineRep, dif_neg hv, hrep, htj]

/--
Formalization support node blueprint `lem:line-rep-incidence` for
`def:line-representative` (paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:166-174`).
Every point lies on the line through its own canonical representative in the
same direction; this is the incidence property used by the line-versus-point
samplers.
-/
theorem mem_linePoints_lineRepMap  (v u : MIPStarRE.QPBT.Coordinates m K) :
    u ∈ linePoints (lineRepMap v u) v := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v u)
  exact ⟨t, by rw [ht]; abel⟩

end MIPStarRE.QPBT
