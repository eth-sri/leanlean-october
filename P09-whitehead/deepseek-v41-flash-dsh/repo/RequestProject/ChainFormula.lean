module

public import RequestProject.FoxCommutator

@[expose] public section

/-!
# Formula (2.3): a chain of two-complexes produces normal subgroups of `G = π₁(K)`

Section 2 of the paper argues as follows.  Let `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` be a chain of
two-complexes in which every inclusion induces the zero map on `π₂`, put
`G = π₁(K)` and `M_r = ker (G → π₁(X_r))`.  Then

  `∂_{2,M_r}(v_{M_r}) = 0  ⟹  v_{M_{r+1}} = 0`   (0 ≤ r < n),

because a coefficient vector `v` whose reduced boundary vanishes at stage `r`
becomes, after extension by zero over the cells of `X_r` that do not come from
`K`, a cycle of the chain complex of the universal cover of `X_r` — that is, an
element of `π₂(X_r)` — and the inclusion `X_r ⊂ X_{r+1}` kills it.

This file proves that implication.  The topological input is packaged in the
structure `ChainInput`, which records exactly the *cell-level* data of such a
chain:

* the groups `π₁(X_r)`, the maps `G → π₁(X_r)` induced by `K ⊂ X_r` and the
  maps `π₁(X_r) → π₁(X_{r+1})` induced by `X_r ⊂ X_{r+1}`, compatibly;
* the one- and two-cells of `X_r`, with the cells of `K` among the cells of
  `X_r` and the two-cells of `X_r` among those of `X_{r+1}`;
* the Fox boundary matrix of `X_r`, which on the old cells is the matrix of `K`
  read in `ℤ[π₁(X_r)]` (`bdry_old`) and which vanishes on the pairs formed by a
  new one-cell and an old two-cell (`bdry_new`), since a relator of `K` is a
  word in the generators of `K`;
* the hypothesis that the inclusion is zero on `π₂ = ker ∂₂`, at chain level
  (`zero_pi2`).

Everything else — the passage from a vanishing reduced boundary to a genuine
cycle, and the conclusion at the next stage — is proved here.  The resulting
statement `chainInput_foxSat_of_not_foxSat` is precisely the hypothesis
`chain_subgroups` of `FiniteChains.NecessityInputs`, so for the Fox
requirements that hypothesis is now a theorem about the cell-level data of the
chain.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-! ### Reduction of coefficients along a group homomorphism -/

/-- Reduction of coefficients is functorial. -/
theorem mapDomainRingHom_comp_apply {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (x : MonoidAlgebra ℤ A) :
    MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) x := by
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ x.coeff) = Finsupp.mapDomain _ x.coeff
  rw [← Finsupp.mapDomain_comp]
  rfl

/-! ### The cell-level data of a chain of two-complexes -/

variable (b : I → J → MonoidAlgebra ℤ G)

/-- The cell-level data of a chain `K = X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes, all of whose
inclusions induce the zero map on `π₂`.  Here `I` indexes the one-cells and `J` the
two-cells of `K`, and `b i j = ∂r_j/∂x_i` is its Fox boundary matrix over `ℤ[G]`,
`G = π₁(K)`. -/
structure ChainInput (n : ℕ) (Fund : ℕ → Type u) [∀ r, Group (Fund r)]
    (Gen Cell : ℕ → Type u) where
  /-- The map `π₁(K) → π₁(X_r)` induced by the inclusion. -/
  phi : ∀ r, G →* Fund r
  /-- The map `π₁(X_r) → π₁(X_{r+1})` induced by the inclusion. -/
  psi : ∀ r, Fund r →* Fund (r + 1)
  /-- The inclusions are compatible. -/
  phi_succ : ∀ r, (psi r).comp (phi r) = phi (r + 1)
  /-- The one-cells of `K` are one-cells of `X_r`. -/
  genIncl : ∀ r, I → Gen r
  /-- The two-cells of `K` are two-cells of `X_r`. -/
  cellIncl : ∀ r, J → Cell r
  cellIncl_injective : ∀ r, Function.Injective (cellIncl r)
  /-- The two-cells of `X_r` are two-cells of `X_{r+1}`. -/
  cellStep : ∀ r, Cell r → Cell (r + 1)
  cellStep_injective : ∀ r, Function.Injective (cellStep r)
  /-- The Fox boundary matrix of `X_r`, over `ℤ[π₁(X_r)]`. -/
  bdry : ∀ r, Gen r → Cell r → MonoidAlgebra ℤ (Fund r)
  /-- On the cells of `K` the boundary matrix of `X_r` is the one of `K`, read in
  `ℤ[π₁(X_r)]`. -/
  bdry_old : ∀ r i j, bdry r (genIncl r i) (cellIncl r j)
      = MonoidAlgebra.mapDomainRingHom ℤ (phi r) (b i j)
  /-- A two-cell of `K` is attached along a word in the one-cells of `K`, so its boundary
  has no component along a new one-cell. -/
  bdry_new : ∀ r (a : Gen r), (∀ i, a ≠ genIncl r i) → ∀ j, bdry r a (cellIncl r j) = 0
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`**, at the level of chains: a cycle of
  the chain complex of the universal cover of `X_r` has zero image in the chain module of
  `X_{r+1}`. -/
  zero_pi2 : ∀ r, r < n → ∀ u : Cell r →₀ MonoidAlgebra ℤ (Fund r),
      (∀ a : Gen r, ∑ c ∈ u.support, u c * bdry r a c = 0) →
      Finsupp.mapDomain (cellStep r)
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (psi r)) (map_zero _) u) = 0

variable {b} {n : ℕ} {Fund : ℕ → Type u} [∀ r, Group (Fund r)] {Gen Cell : ℕ → Type u}

namespace ChainInput

variable (h : ChainInput b n Fund Gen Cell)

/-- A coefficient vector of `K`, pushed to `ℤ[π₁(X_r)]` and extended by zero over the
two-cells of `X_r` that do not come from `K`. -/
noncomputable def oldVec (r : ℕ) (v : J →₀ MonoidAlgebra ℤ G) :
    Cell r →₀ MonoidAlgebra ℤ (Fund r) :=
  Finsupp.mapDomain (h.cellIncl r)
    (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.phi r)) (map_zero _) v)

theorem oldVec_apply_cellIncl (r : ℕ) (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    h.oldVec r v (h.cellIncl r j) = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (v j) :=
  Finsupp.mapDomain_apply_of_injective (h.cellIncl_injective r) _ j

theorem oldVec_support_subset (r : ℕ) [DecidableEq (Cell r)] (v : J →₀ MonoidAlgebra ℤ G) :
    (h.oldVec r v).support ⊆ v.support.image (h.cellIncl r) := by
  classical
  refine Finsupp.mapDomain_support.trans ?_
  exact Finset.image_subset_image (Finsupp.support_mapRange)

end ChainInput

end FiniteChains
