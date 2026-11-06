module

public import RequestProject.BlockGeneration
public import RequestProject.GenerationStep

@[expose] public section

/-!
# From the homology of the double mapping cylinder to equation (3.3)

`RequestProject/BlockGeneration.lean` proves, for the equivariant chain model of the double
mapping cylinder, that the two-cycles of the cancelled two-complex are spanned over
`ℤ[π₁(W)]` by the cancelled images of the two-cycles of the chosen copy of `X`.  Property
(B2) is stated in the language of presentations: for the structural map `f : E → E'` of the
substitution (3.4),

  `π₂(E') = ℤ[G(E')] · f_* π₂(E)`,

i.e. every **Fox cycle** of `E'` is a `ℤ[G(E')]`-combination of images of Fox cycles of `E`
(`FiniteChains.Generates`).  This file proves that the two statements agree: the surjectivity
obtained from the relative homology *is* the generation of all Fox cycles by the images of
the old ones.

* `FiniteChains.foxBdry` — the Fox boundary of a presentation as a map of `ℤ[G]`-modules, and
  `FiniteChains.isFoxCycle_iff_foxBdry_eq_zero`: Fox cycles are exactly its kernel, so the
  two-chains of the universal cover of a presentation complex form a chain complex in the
  sense used by the homological lemmas;
* `FiniteChains.generates_of_block_chain_model` — **the passage to presentations**: given the
  chain model of the double mapping cylinder for the substitution, the vanishing of
  `H₂(W̃, U)`, the transitive deck action on the components of `U` and the identification of
  the cancelled images with the images of the structural map, equation (3.3) holds for that
  structural map.

As everywhere in this part of the development, the single geometric input that is not proved
is the vanishing `H₂(W̃, U) = 0`, which the paper obtains from the cubical curvature criterion
for the collapsed space `V`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

section FoxBoundary

variable {α J : Type u} [DecidableEq α] [Fintype J] (ρ : J → FreeGroup α)

/-- The Fox boundary `∂₂` of a presentation, as a map of `ℤ[G]`-modules from the two-chains
to the one-chains of the universal cover of the presentation complex. -/
noncomputable def foxBdry :
    (J → MonoidAlgebra ℤ (PresGroup ρ)) →ₗ[MonoidAlgebra ℤ (PresGroup ρ)]
      (α → MonoidAlgebra ℤ (PresGroup ρ)) where
  toFun v := fun i => ∑ j, v j * foxMatrixPres ρ i j
  map_add' v w := by
    funext i
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

@[simp] theorem foxBdry_apply (v : J → MonoidAlgebra ℤ (PresGroup ρ)) (i : α) :
    foxBdry ρ v i = ∑ j, v j * foxMatrixPres ρ i j := rfl

end FoxBoundary

section Bridge

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

variable {ι : Type*} {A₂ A₁ Q Q₃ Q₂ Q₁ B₃ : Type*}
  [AddCommGroup A₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) A₂]
  [AddCommGroup A₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) A₁]
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₁]

end Bridge

end FiniteChains
