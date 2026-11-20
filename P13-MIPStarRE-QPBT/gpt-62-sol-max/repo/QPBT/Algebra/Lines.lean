module

public import Mathlib

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

section

variable {m : ℕ}
include m

/--
The affine line through `u` in direction `v`, including the singleton case
`v = 0`.  Blueprint `def:line`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def linePoints
    (u v : Fin m → K) : Set (Fin m → K) :=
  {x | ∃ t : K, x = u + t • v}

/-- The elementary coordinate direction used in the axis-parallel predicate of
blueprint `def:line`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`.
-/
def coordinateDirection
    (i : Fin m) : Fin m → K :=
  Pi.single i 1

section

variable (v : Fin m → K) (hv : v ≠ 0)
include v hv

/-- The least coordinate at which a nonzero line direction is nonzero. This is
Lean-only support for the elementary formula for the canonical representative;
coordinates use the same left-to-right order as paper `def:cl-canonical`. -/
noncomputable def linePivotIndex : Fin m := by
  classical
  let support := Finset.univ.filter fun j => v j ≠ 0
  have hsupport : support.Nonempty := by
    simpa [support, Finset.filter_nonempty_iff, funext_iff] using hv
  exact support.min' hsupport

/-- The pivot coordinate of a nonzero direction is nonzero. -/
theorem linePivotIndex_ne_zero :
    v (linePivotIndex v hv) ≠ 0 := by
  classical
  have hmem :
      linePivotIndex v hv ∈ Finset.univ.filter fun j => v j ≠ 0 := by
    unfold linePivotIndex
    exact Finset.min'_mem _ _
  simp_all

/-- The pivot is the first nonzero coordinate. -/
theorem linePivotIndex_le (i : Fin m) (hi : v i ≠ 0) : linePivotIndex v hv ≤ i := by
  classical
  unfold linePivotIndex
  exact Finset.min'_le _ _ (by simp [hi])

end

/-- The affine coordinate read at the first nonzero entry of the direction.
For the singleton line it is set to zero. -/
noncomputable def directLineRepParameter (v : Fin m → K) : (Fin m → K) →ₗ[K] K :=
  open Classical in
  if hv : v = 0 then 0 else (v (linePivotIndex v hv))⁻¹ • LinearMap.proj (linePivotIndex v hv)

/-- Project onto the coordinate complement of the direction by subtracting
its affine coordinate. This is the least-pivot form of `def:line-representative`. -/
noncomputable def lineRepMap (v : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  LinearMap.id - (directLineRepParameter v).smulRight v

section

variable (v u : Fin m → K)
include v u

/-- Reconstruction from the representative and its affine coordinate. -/
theorem directLineRepParameter_spec : u = lineRepMap v u + directLineRepParameter v u • v :=
  (sub_add_cancel _ _).symm

omit v u in
/-- The affine coordinate is determined uniquely for a nonzero direction. -/
theorem directLineRepParameter_eq_of_nonzero {v u : Fin m → K} (hv : v ≠ 0) {t : K}
    (ht : u = lineRepMap v u + t • v) : directLineRepParameter v u = t :=
  smul_left_injective K hv (add_left_cancel ((directLineRepParameter_spec v u).symm.trans ht))

omit u in
private theorem directLineRepParameter_self (hv : v ≠ 0) : directLineRepParameter v v = 1 := by
  classical
  simp [directLineRepParameter, hv, linePivotIndex_ne_zero]

omit v u in
/-- Translating the point by a multiple of its direction adds that parameter. -/
theorem directLineRepParameter_add_smul {v u : Fin m → K} (hv : v ≠ 0) (t : K) :
    directLineRepParameter v (u + t • v) = directLineRepParameter v u + t := by
  simp [directLineRepParameter_self v hv]

/-- Translation along the direction does not change the representative. -/
theorem lineRepMap_add_smul (t : K) : lineRepMap v (u + t • v) = lineRepMap v u := by
  suffices lineRepMap v v = 0 by simp [this]
  by_cases hv : v = 0
  · simp [hv]
  · change v - directLineRepParameter v v • v = 0
    simp [directLineRepParameter_self v hv]

/-- A canonical representative is fixed by the projection. -/
theorem lineRepMap_apply_self : lineRepMap v (lineRepMap v u) = lineRepMap v u := by
  change lineRepMap v (u - directLineRepParameter v u • v) = _
  rw [sub_eq_add_neg, ← neg_smul, lineRepMap_add_smul]

theorem lineRepMap_apply : lineRepMap v u = u - directLineRepParameter v u • v := rfl

/-- The representative lies on the same affine line. -/
theorem mem_linePoints_lineRepMap : u ∈ linePoints (lineRepMap v u) v :=
  ⟨_, directLineRepParameter_spec v u⟩

end

end

end MIPStarRE.QPBT
