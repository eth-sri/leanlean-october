module

public import RequestProject.BlockGenerates
public import RequestProject.BaseChangeCycles

@[expose] public section

/-!
# The chain model of the block substitution, built over the Fox complex

This is the (B2) half of the last link of the block argument.  `RequestProject/BlockGenerates.lean`
derives equation (3.3) — property (B2) — from the equivariant chain model of the double
mapping cylinder `W`, but through two hypotheses of dictionary type: that the boundary of the
cancelled two-complex *is* the Fox boundary of the substituted presentation (`hbdry`), and
that the cycles of the chosen copy of `X` *are* the images of the Fox cycles of `ρ`
(`himage`).

Here those two are built in instead of assumed.

* the two-chains of `W̃` are `(J' → ℤ[G']) × Q`, the first factor being the two-chains of the
  universal cover of the presentation complex of `ρ'` in the Fox coordinates, and the
  boundary is by construction the Fox boundary of `ρ'` on that factor
  (`FiniteChains.BlockFox.bdry₂`);
* the chains of the full preimage `U` of `X` are the free `ℤ[G']`-module on the two-cells of
  `X`, that is the base change `ℤ[G'] ⊗_{ℤ[G]} C₂(X̃)`, and its boundary is the base-changed
  Fox boundary of `ρ` (`FiniteChains.BlockFox.foxBdryPush`); the inclusion of the chosen copy
  of `X̃` is the base change `FiniteChains.PresMor.cellsBase` of the chain map of the
  structural map, which restricts to that map on the image of `C₂(X̃)`
  (`FiniteChains.PresMor.cellsBase_pushChain`);
* the chosen component is the `ℤ[G']`-span of the images of the Fox cycles of `ρ`, and the
  hypothesis "every cycle of `U` decomposes over the components" is a theorem
  (`FiniteChains.BlockFox.cycle_mem_span_pushCycles`): when the structural map is injective on
  fundamental groups — which is the `π₁`-injectivity of the substitution — the base-changed
  Fox matrix has its entries in the subring `ℤ[f(G)]`, so
  `FiniteChains.cycle_mem_span_subgroup_cycles` applies.

The result is `FiniteChains.BlockFox.generates_of_fox_chain_model`: **property (B2) with the
dictionary discharged**, its remaining hypotheses being the geometric ones — the exactness of
the pair `(W̃, U)` in the degrees used, and the vanishing `H₂(W̃, U) = 0` which the paper gets
from the curvature criterion.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

namespace PresMor

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [DecidableEq J] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- The coefficient homomorphism `ℤ[G] → ℤ[G']` of a structural map. -/
noncomputable def pushRing (f : PresMor ρ ρ') :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup ρ') :=
  MonoidAlgebra.mapDomainRingHom ℤ f.hom

/-- **The base change of the chain map of a structural map**: the `ℤ[G']`-linear map on the
chains of the preimage of `X` determined by the images of the two-cells. -/
noncomputable def cellsBase (f : PresMor ρ ρ') (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    J' → MonoidAlgebra ℤ (PresGroup ρ') :=
  ∑ j, y j • f.cells (Pi.single j 1)

theorem cellsBase_add (f : PresMor ρ ρ') (y z : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    f.cellsBase (y + z) = f.cellsBase y + f.cellsBase z := by
  simp only [cellsBase, Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib]

theorem cellsBase_smul (f : PresMor ρ ρ') (c : MonoidAlgebra ℤ (PresGroup ρ'))
    (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    f.cellsBase (c • y) = c • f.cellsBase y := by
  simp only [cellsBase, Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [Finset.smul_sum]

/-- The base-changed chain map, as a map of `ℤ[G']`-modules. -/
noncomputable def cellsBaseL (f : PresMor ρ ρ') :
    (J → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (J' → MonoidAlgebra ℤ (PresGroup ρ')) where
  toFun := f.cellsBase
  map_add' := f.cellsBase_add
  map_smul' := f.cellsBase_smul

@[simp] theorem cellsBaseL_apply (f : PresMor ρ ρ') (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    f.cellsBaseL y = f.cellsBase y := rfl

end PresMor

namespace BlockFox

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [DecidableEq J] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- The boundary of the chains of the preimage of `X`: the base change of the Fox boundary of
`ρ`. -/
noncomputable def foxBdryPush (f : PresMor ρ ρ') :
    (J → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α → MonoidAlgebra ℤ (PresGroup ρ')) where
  toFun y := fun i => ∑ j, y j * f.pushRing (foxMatrixPres ρ i j)
  map_add' y z := by
    funext i
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c y := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

omit [DecidableEq J] in
@[simp] theorem foxBdryPush_apply (f : PresMor ρ ρ')
    (y : J → MonoidAlgebra ℤ (PresGroup ρ')) (i : α) :
    foxBdryPush f y i = ∑ j, y j * f.pushRing (foxMatrixPres ρ i j) := rfl

/-! ### Every cycle of the preimage comes from the chosen copy -/

section BaseChange

variable (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)

end BaseChange

/-! ### Property (B2) from the constructed chain model -/

section Model

variable (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)

variable {Q B₃ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₁]

/-- The boundary of the two-chains of the universal cover of the double mapping cylinder:
on the two-cells of the substituted presentation complex it is, by construction, the Fox
boundary of `ρ'`; on the replaced two-cell it is given by `bq`. -/
noncomputable def bdry₂model
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ'))) :
    ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')) :=
  (foxBdry ρ').comp (LinearMap.fst _ _ _) + bq.comp (LinearMap.snd _ _ _)

@[simp] theorem bdry₂model_inl
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (p : J' → MonoidAlgebra ℤ (PresGroup ρ')) :
    bdry₂model (Q := Q) bq (p, 0) = foxBdry ρ' p := by
  simp [bdry₂model]

/-- The inclusion of the chains of the preimage of `X` into the two-chains of the universal
cover of the double mapping cylinder: the base change of the chain map of the structural
map, with zero coefficient on the replaced two-cell. -/
noncomputable def inclModel :
    (J → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) :=
  (f.cellsBaseL).prod 0

@[simp] theorem inclModel_apply (y : J → MonoidAlgebra ℤ (PresGroup ρ')) :
    inclModel (Q := Q) f y = (f.cellsBase y, 0) := rfl

end Model

end BlockFox

end FiniteChains
