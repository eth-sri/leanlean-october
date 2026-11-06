module

public import Mathlib

/-!
# Lines and canonical representatives
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators

variable {K : Type*} [Field K]

def linePoints {m : ℕ}
    (u v : Fin m → K) : Set (Fin m → K) :=
  {x | ∃ t : K, x = u + t • v}

def coordinateDirection {m : ℕ}
    (i : Fin m) : Fin m → K :=
  Pi.single i 1

noncomputable def linePivotIndex {m : ℕ} (v : Fin m → K) (hv : v ≠ 0) : Fin m := by
  classical
  let support := Finset.univ.filter fun j => v j ≠ 0
  have hsupport : support.Nonempty := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    exact h ⟨j, by simpa [support] using hj⟩
  exact support.min' hsupport

theorem linePivotIndex_ne_zero {m : ℕ} (v : Fin m → K) (hv : v ≠ 0) :
    v (linePivotIndex v hv) ≠ 0 := by
  classical
  have hmem : linePivotIndex v hv ∈ Finset.univ.filter fun j => v j ≠ 0 := by
    unfold linePivotIndex
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

theorem linePivotIndex_zero_before {m : ℕ} (v : Fin m → K) (hv : v ≠ 0)
    (i : Fin m) (hi : i < linePivotIndex v hv) : v i = 0 := by
  classical
  by_contra hvi
  unfold linePivotIndex at hi
  exact (not_le_of_gt hi) (Finset.min'_le _ i (by simp [hvi]))

noncomputable def explicitLineRep {m : ℕ}
    (u v : Fin m → K) : Fin m → K :=
  open Classical in
    if hv : v = 0 then u
    else
      let j := linePivotIndex v hv
      u - (u j / v j) • v

noncomputable def lineRepMap {m : ℕ}
    (v : Fin m → K) : (Fin m → K) →ₗ[K] (Fin m → K) where
  toFun u := explicitLineRep u v
  map_add' x y := by
    by_cases hv : v = 0 <;> simp [explicitLineRep, hv, add_div, add_smul, sub_add_sub_comm]
  map_smul' c x := by
    by_cases hv : v = 0 <;> simp [explicitLineRep, hv, mul_div_assoc, mul_smul, smul_sub]

theorem sub_lineRepMap_mem_span {m : ℕ} (v u : Fin m → K) :
    u - lineRepMap v u ∈ Submodule.span K ({v} : Set (Fin m → K)) := by
  by_cases hv : v = 0
  · simp [lineRepMap, explicitLineRep, hv]
  · exact Submodule.mem_span_singleton.mpr ⟨u (linePivotIndex v hv) / v (linePivotIndex v hv),
      by simp [lineRepMap, explicitLineRep, hv]⟩

theorem lineRepMap_apply_eq_explicitLineRep {m : ℕ} (v u : Fin m → K) :
    lineRepMap v u = explicitLineRep u v := rfl

theorem mem_linePoints_lineRepMap {m : ℕ} (v u : Fin m → K) :
    u ∈ linePoints (lineRepMap v u) v := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v u)
  exact ⟨t, by rw [ht]; abel⟩

end MIPStarRE.QPBT
