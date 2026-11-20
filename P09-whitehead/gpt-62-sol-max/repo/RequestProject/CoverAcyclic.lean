module

public import RequestProject.CoverChainComplex
public import RequestProject.FoxCommutator

@[expose] public section

/-!
# From the requirements (2.2) to an acyclic cover

Section 2 of the paper produces a perfect normal subgroup `N ≤ G = π₁(K)` satisfying all
the requirements (2.2) and concludes that the corresponding cover `K_N` is acyclic:
`H₁(K_N) = N/[N, N] = 0` and `H₂(K_N) = ker ∂_{2,N} = 0`.

This file proves that implication algebraically, for the chain complex of the cover built
in `RequestProject/CoverChainComplex.lean`.  Requirements are the ones of
`RequestProject/FoxRequirement.lean`, applied to the Fox matrix `b i j = ∂r_j/∂x_i` of a
finite presentation, and perfectness of `N = Ñ / ⟪r_1, …, r_m⟫` is expressed as
`Ñ ≤ ⟪r_1, …, r_m⟫ ⊔ [Ñ, Ñ]`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal] (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] in
theorem proj_eq_quotRingHom : proj Nsub = quotRingHom ℤ Nsub := rfl

end FiniteChains
