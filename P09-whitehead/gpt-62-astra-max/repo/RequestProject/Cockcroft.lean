module

public import RequestProject.PresentationDictionary
public import RequestProject.CoverChainComplex

@[expose] public section

/-!
# The Cockcroft property of a presentation complex

For the two-complex `K` of a finite presentation `⟨x_i (i ∈ α) | r_j (j ∈ J)⟩` the module
`π₂(K)` is the module of Fox cycles

  `{v ∈ ℤ[G]^J : ∑_j v_j · ∂r_j/∂x_i = 0 for every i}`,   `G = π₁(K)`,

(see `RequestProject/UniversalCoverPi2.lean`), and the Hurewicz map `π₂(K) → H₂(K)` is
induced by the augmentation `ℤ[G] → ℤ`, since `H₂(K)` is the kernel of the exponent-sum
matrix `M` acting on `ℤ^J`.  Hence *Cockcroft* — "the Hurewicz map of `K` is zero" — reads,
in the combinatorial model:

  every Fox cycle has zero augmentation   (`FiniteChains.IsCockcroft`).

This file sets up that definition and proves the first instance of it used in Section 3:
an **acyclic** presentation complex is Cockcroft (`FiniteChains.isCockcroft_of_expInjective`),
because the augmentation of a Fox cycle is a vector killed by the exponent-sum matrix.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The augmentation `ℤ[G] → ℤ` of the group ring of the presented group. -/
noncomputable abbrev augPres : MonoidAlgebra ℤ (PresGroup ρ) →+* ℤ := augQ (relSub ρ)

/-- The entries `M_{ij}` of the exponent-sum matrix of the presentation: the exponent sum of
`x_i` in the relator `r_j`. -/
noncomputable def expEntry (i : α) (j : J) : ℤ := Multiplicative.toAdd (expSum i (ρ j))

omit [Fintype α] [Fintype J] in
/-- Augmenting the Fox matrix gives the exponent-sum matrix. -/
theorem augPres_foxMatrixPres (i : α) (j : J) :
    augPres ρ (foxMatrixPres ρ i j) = expEntry ρ i j := by
  have h : foxMatrixPres ρ i j = proj (relSub ρ) (fox i (ρ j)) := rfl
  rw [h, augQ_proj, aug_fox, expEntry]

/-- A **Fox cycle**: an element of `π₂` of the presentation complex, in the coordinates of
`RequestProject/UniversalCoverPi2.lean`. -/
def IsFoxCycle (v : J → MonoidAlgebra ℤ (PresGroup ρ)) : Prop :=
  ∀ i : α, ∑ j, v j * foxMatrixPres ρ i j = 0

/-- **The Cockcroft property.**  The Hurewicz map of the presentation complex is zero: every
Fox cycle (i.e. every element of `π₂`) has zero augmentation in every coordinate. -/
def IsCockcroft : Prop :=
  ∀ v : J → MonoidAlgebra ℤ (PresGroup ρ), IsFoxCycle ρ v → ∀ j, augPres ρ (v j) = 0

end FiniteChains
