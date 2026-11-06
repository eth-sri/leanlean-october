import RequestProject.SubgroupCompactness


/-!
# The requirements of Section 2 are finitely determined

Section 2 uses that each requirement (2.2)

  `∂_{2,M}(v_M) = 0  ⟹  v_M = 0`

"depends on finitely many decisions `g ∈ M`: reduction merely adds coefficients
within cosets, whose equalities are membership tests".  This file makes that
statement precise and proves it, so that the compactness step
`exists_normal_subgroup_forall` may be applied to the Fox requirements.

A coefficient vector is an element of the group ring `ℤ[G]`, and the reduction
of `x ∈ ℤ[G]` to `ℤ[G/N]` vanishes exactly when, for every `g`, the
coefficients of `x` inside the coset `Ng` add up to zero; this is
`VanishesMod`.  The requirement attached to a finitely supported vector `v` and
a boundary matrix `b` is `FoxSat`.
-/

namespace FiniteChains


variable {G : Type*} [Group G]

open scoped Classical
/-- The reduction of `x ∈ ℤ[G]` to `ℤ[G/N]` is zero: inside every coset of `N` the
coefficients of `x` add up to zero. -/
def VanishesMod (N : Subgroup G) (x : G →₀ ℤ) :=
  ∀ g, ∑ h ∈ x.support.filter (· * g⁻¹ ∈ N), x h = 0


variable {I J : Type*}

/-- The `i`-th coordinate of the Fox boundary of the coefficient vector `v`, with respect
to the boundary data `b i j = ∂r_j/∂x_i` read in the group ring. -/
noncomputable def foxBoundary (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) :=
  ∑ j ∈ v.support, v j * b i j

/-- The requirement (2.2) attached to the coefficient vector `v`: if the reduced boundary
of `v` vanishes, then the reduced `v` vanishes. -/
def FoxSat (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) :=
  (∀ i, VanishesMod N (foxBoundary b v i).coeff) → ∀ j, VanishesMod N (v j).coeff
