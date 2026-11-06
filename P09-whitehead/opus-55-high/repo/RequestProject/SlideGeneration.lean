module

public import RequestProject.CoverChainComplex
public import RequestProject.PresentationDictionary
public import RequestProject.ExponentCorrection
public import RequestProject.Cockcroft

@[expose] public section

/-!
# Rule 2 of Section 3.4 does not change `π₂`

Rule 2 of the operation `T` replaces an extra relator `r*` by

  `r⁰ = r* ∏_j r_j^{c_j}`,

a product of `r*` with core relators (`RequestProject/ExponentCorrection.lean` produces the
exponents `c`).  The paper justifies the generation property for this rule by

> Rule 2 is a finite sequence of slides of each extra relator disk over retained core disks.
> The inverse slides undo it.  It is a homotopy equivalence relative to `D`.

This file proves the corresponding statement in the combinatorial model.  The slide does not
change the normal closure of the relators (`FiniteChains.relSub_slideRel`), so both
presentations have the same fundamental group, and their second homotopy groups are the
modules of two-cycles of the same complex of `RequestProject/CoverChainComplex.lean`, taken
over `N = ⟪relators⟫`.  In that vocabulary the slide multiplies the Fox matrix by an
invertible unitriangular matrix:

* `FiniteChains.foxVec_mem_range_bdry2` — the Fox vector of an element of the normal closure
  of a family of words is a `ℤ[Q]`-combination of the Fox vectors of that family;
* `FiniteChains.exists_slideCoeff` — hence the coefficient vector `λ` of the slide exists,
  with `λ` vanishing at the slid index;
* `FiniteChains.bdry2_slideRel` — the boundary of the slid presentation expressed through the
  old one;
* `FiniteChains.slideCycle_image` and `FiniteChains.slideCycle_image_isCycle` — **rule 2 has
  the generation property**: the two-cycles of the slid presentation are exactly the images
  of the two-cycles of the old one under the `ℤ[Q]`-linear isomorphism `y ↦ y - y_{j₀} λ`;
* `FiniteChains.slide_cockcroft` — consequently rule 2 preserves the Cockcroft property.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

section Slide

variable {J : Type*} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α) (j₀ : J)
  (u : FreeGroup α)

/-- **The slide**: the relator with index `j₀` is multiplied by a word `u` in the retained
core relators. -/
def slideRel : J → FreeGroup α := Function.update ρ j₀ (ρ j₀ * u)

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideRel_self : slideRel ρ j₀ u j₀ = ρ j₀ * u := by
  simp [slideRel]

omit [Fintype α] [DecidableEq α] [Fintype J] in
@[simp] theorem slideRel_of_ne {j : J} (h : j ≠ j₀) : slideRel ρ j₀ u j = ρ j := by
  simp [slideRel, h]

/-- The words available for the correction: the relators other than the one being slid. -/
abbrev coreRel : {j : J // j ≠ j₀} → FreeGroup α := fun j => ρ j

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- **The slide does not change the presented group**: the normal closure of the relators is
unchanged, so rule 2 is a Tietze transformation. -/
theorem relSub_slideRel (hu : u ∈ Subgroup.normalClosure (Set.range (coreRel ρ j₀))) :
    relSub (slideRel ρ j₀ u) = relSub ρ := by
  have hcore : Subgroup.normalClosure (Set.range (coreRel ρ j₀)) ≤ relSub ρ := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_normalClosure ⟨(j : J), rfl⟩
  have hcore' : Subgroup.normalClosure (Set.range (coreRel ρ j₀)) ≤ relSub (slideRel ρ j₀ u) := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_normalClosure ⟨(j : J), slideRel_of_ne ρ j₀ u j.2⟩
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : j = j₀
    · subst h
      rw [slideRel_self]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨j, rfl⟩) (hcore hu)
    · rw [slideRel_of_ne ρ j₀ u h]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : j = j₀
    · subst h
      have hj : ρ j = (slideRel ρ j u j) * u⁻¹ := by
        rw [slideRel_self, mul_assoc, mul_inv_cancel, mul_one]
      rw [hj]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        (Subgroup.inv_mem _ (hcore' hu))
    · rw [← slideRel_of_ne ρ j₀ u h]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩

variable {ρ j₀ u}

end Slide

/-! ### In the vocabulary of the presentation complex

For `N = ⟪r_1, …, r_m⟫` the complex used above is the cellular chain complex of the
universal cover, so its two-cycles are the Fox cycles of `RequestProject/Cockcroft.lean` and
its augmentation is the Hurewicz map.  In these terms rule 2 preserves the Cockcroft
property. -/

section Presentation

variable {J : Type*} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α) (j₀ : J)
  (u : FreeGroup α)

end Presentation

end FiniteChains
