module

public import Mathlib.SetTheory.Cardinal.Finite
public import GaloisCohomology.Cyclic.GaloisCohomology
public import GaloisCohomology.Cyclic.NormKernelVanishing
public import GaloisCohomology.Cyclic.TateH0.NormImage
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace LocalClassFieldTheory

open CyclicCohomology

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The norm in the actual unit representation is the multiplicative Herbrand
norm after passing from `Additive Lˣ` back to `Lˣ`. -/
theorem unitsNormLinearMap_toMul_eq_tateNorm
    [Fintype (Gal(L / K))] (x : Lˣ) :
    Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) =
      tateNorm (Gal(L / K)) Lˣ x := by
  solve_by_elim [unitsNormLinearMap, LinearMap.sum_apply]

/-- Multiplicative fixed units and the invariant submodule of the actual unit
representation are the same additive group. -/
def additiveFixedUnitsEquivInvariants :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) ≃+
      unitsInvariantSubmodule K L where
  toFun x := ⟨Additive.ofMul ((Additive.toMul x : fixedSubgroup (Gal(L / K)) Lˣ) : Lˣ), by
    intro σ
    exact congrArg Additive.ofMul ((Additive.toMul x).property σ)⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    intro σ
    exact Additive.ofMul.injective (x.property σ)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- Compose an additive equivalence with a submodule quotient map.

Keeping this construction polymorphic prevents typeclass search from unfolding
the concrete Galois representation while it looks for the quotient's additive
structure. -/
 def additiveEquivToQuotientHom
    {A M : Type} [AddCommGroup A] [AddCommGroup M]
    (e : A ≃+ M) (N : Submodule ℤ M) : A →+ M ⧸ N :=
  N.mkQ.toAddMonoidHom.comp e.toAddMonoidHom

/-- Multiplicative form of an additive homomorphism, kept polymorphic for the
same elaboration reason as `additiveEquivToQuotientHom`. -/
 def additiveHomToMultiplicativeHom
    {G B : Type} [Group G] [AddCommGroup B]
    (f : Additive G →+ B) : G →* Multiplicative B :=
  AddMonoidHom.toMultiplicativeRight f

/-- The multiplicative group structure on an additive submodule quotient.
This is passed explicitly at concrete call sites to avoid rediscovering it by
unfolding the coefficient representation. -/
@[implicit_reducible]
 def multiplicativeQuotientGroup
    {M : Type} [AddCommGroup M] (N : Submodule ℤ M) :
    Group (Multiplicative (M ⧸ N)) :=
  Multiplicative.group

/-- Kernel of a homomorphism into a multiplicative additive quotient, with the
codomain structure supplied directly. -/
 def kernelOfAdditiveQuotientHom
    {G M : Type} [Group G] [AddCommGroup M]
    (N : Submodule ℤ M) (f : G →* Multiplicative (M ⧸ N)) : Subgroup G :=
  @MonoidHom.ker G inferInstance (Multiplicative (M ⧸ N))
    (multiplicativeQuotientGroup N).toMulOneClass f

/-- First-isomorphism-theorem comparison for a surjection onto a
multiplicative additive quotient. -/
 def quotientMulEquivOfSurjectiveAdditiveQuotient
    {G M : Type} [CommGroup G] [AddCommGroup M]
    (N : Submodule ℤ M) (S : Subgroup G)
    (f : G →* Multiplicative (M ⧸ N))
    (hker : kernelOfAdditiveQuotientHom N f = S)
    (hsurj : Function.Surjective f) :
    G ⧸ S ≃* Multiplicative (M ⧸ N) := by
  letI : Group (Multiplicative (M ⧸ N)) := multiplicativeQuotientGroup N
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)

/-- Forget the type tags in an equivalence whose codomain is the
multiplicative form of an additive group. -/
 def mulEquivMultiplicativeToEquiv
    {G B : Type} [Group G] [AddCommGroup B]
    (e : G ≃* Multiplicative B) : G ≃ B where
  toFun q := Multiplicative.toAdd (e q)
  invFun q := e.symm (Multiplicative.ofAdd q)
  left_inv q := e.left_inv q
  right_inv q := e.right_inv (Multiplicative.ofAdd q)

section

variable [Fintype (Gal(L / K))]

/-- Additive quotient map from fixed units to invariant units modulo norms. -/
def additiveFixedUnitToInvariantsNormQuotientHom :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) →+
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveEquivToQuotientHom (additiveFixedUnitsEquivInvariants K L)
    (unitsTateH0NormSubmodule K L)

/-- Send a fixed unit to its invariant-unit class modulo norms. -/
def fixedUnitToInvariantsNormQuotientMonoidHom :
    fixedSubgroup (Gal(L / K)) Lˣ →*
      Multiplicative
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveHomToMultiplicativeHom
    (additiveFixedUnitToInvariantsNormQuotientHom K L)

/-- A fixed unit maps to its canonical invariant-unit class modulo norms. -/
@[simp]
theorem fixedUnitToInvariantsNormQuotientMonoidHom_apply (x : fixedSubgroup (Gal(L / K)) Lˣ) :
    Multiplicative.toAdd
        (fixedUnitToInvariantsNormQuotientMonoidHom K L x) =
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) :=
  rfl

/-- The kernel of the fixed-unit quotient map is exactly
the Herbrand norm subgroup inside the fixed subgroup. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_ker :
    kernelOfAdditiveQuotientHom (unitsTateH0NormSubmodule K L)
        (fixedUnitToInvariantsNormQuotientMonoidHom K L) =
      (tateNormSubgroup (Gal(L / K)) Lˣ).subgroupOf
        (fixedSubgroup (Gal(L / K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0 at hx0
    rcases ((Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).1 hx0) with ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : unitsInvariantSubmodule K L =>
        Additive.toMul (z : Additive Lˣ)) hy
    rw [tateNormHom_apply,
      ← unitsNormLinearMap_toMul_eq_tateNorm K L (Additive.toMul y)]
    exact hy'
  · intro hx
    change (x : Lˣ) ∈ tateNormSubgroup (Gal(L / K)) Lˣ at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) = 0
    apply (Submodule.Quotient.mk_eq_zero (unitsTateH0NormSubmodule K L)).2
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    change Additive.toMul
      (unitsNormLinearMap K L (Additive.ofMul y)) = (x : Lˣ)
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L y]
    exact hy

/-- Every invariant-unit class modulo norms has a multiplicatively fixed representative. -/
theorem fixedUnitToInvariantsNormQuotientMonoidHom_surjective :
    Function.Surjective (fixedUnitToInvariantsNormQuotientMonoidHom K L) := by
  solve_by_elim [Submodule.mkQ_surjective, Additive.toMul]

/-- The multiplicative Herbrand quotient is the invariant-unit quotient by norms. -/
def herbrandH0MulEquivInvariantsNormQuotient :=
  quotientMulEquivOfSurjectiveAdditiveQuotient
    (unitsTateH0NormSubmodule K L)
    ((tateNormSubgroup (Gal(L / K)) Lˣ).subgroupOf
      (fixedSubgroup (Gal(L / K)) Lˣ))
    (fixedUnitToInvariantsNormQuotientMonoidHom K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_ker K L)
    (fixedUnitToInvariantsNormQuotientMonoidHom_surjective K L)

/-- The multiplicative Herbrand quotient of field units is mathlib's
degree-zero Tate cohomology. -/
def herbrandH0EquivTateCohomologyZero :
    HerbrandH0 (Gal(L / K)) Lˣ ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 :=
  (mulEquivMultiplicativeToEquiv
      (herbrandH0MulEquivInvariantsNormQuotient K L)).trans
    (tateUnitsH0IsoInvariantsQuotient K L).symm.toLinearEquiv.toEquiv

end

/-- Subtraction by the identity in the actual unit representation is the
multiplicative coboundary `x ↦ g•x/x`. -/
theorem unitsRhoSub_toMul_eq_sigmaMinusOne
    (g : Gal(L / K)) (x : Lˣ) :
    (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul x)) : Lˣ) * x⁻¹ =
      sigmaMinusOne (Gal(L / K)) Lˣ g x := rfl

/-- Multiplicative norm-one units and the kernel of the norm on the actual
unit representation are the same additive group. -/
def additiveNormKernelEquivUnitsNormKer [Fintype (Gal(L / K))] :
    Additive (normKernelSubgroup (Gal(L / K)) Lˣ) ≃+
      LinearMap.ker (unitsNormLinearMap K L) where
  toFun x := ⟨Additive.ofMul
      ((Additive.toMul x : normKernelSubgroup (Gal(L / K)) Lˣ) : Lˣ), by
    apply Additive.toMul.injective
    rw [unitsNormLinearMap_toMul_eq_tateNorm K L
      ((Additive.toMul x : normKernelSubgroup (Gal(L / K)) Lˣ) : Lˣ)]
    exact (Additive.toMul x).property⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    change tateNorm (Gal(L / K)) Lˣ (Additive.toMul x) = 1
    rw [← unitsNormLinearMap_toMul_eq_tateNorm K L
      (Additive.toMul (x : Additive Lˣ))]
    exact congrArg Additive.toMul x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

section

variable [Fintype (Gal(L / K))] (g : Gal(L / K))

/-- The actual additive differential `ρ(g)-1`, with codomain restricted to
the kernel of the norm. -/
def unitsRhoSubToNormKerLinearMap :
    Additive Lˣ →ₗ[ℤ] LinearMap.ker (unitsNormLinearMap K L) :=
  ((Rep.ofAlgebraAutOnUnits K L).ρ g - LinearMap.id).codRestrict
    (LinearMap.ker (unitsNormLinearMap K L)) (by
      intro x
      change (Rep.ofAlgebraAutOnUnits K L).norm.hom
        ((Rep.ofAlgebraAutOnUnits K L).ρ g x - x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact Representation.norm_self_apply (Rep.ofAlgebraAutOnUnits K L).ρ g x)

/-- Additive quotient map from the multiplicative norm kernel to the
standard boundary presentation of degree-minus-one Tate cohomology. -/
def additiveNormKernelToUnitsBoundaryQuotientHom :
    Additive (normKernelSubgroup (Gal(L / K)) Lˣ) →+
      LinearMap.ker (unitsNormLinearMap K L) ⧸
        LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
  additiveEquivToQuotientHom
    (additiveNormKernelEquivUnitsNormKer K L)
    (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))

/-- Multiplicative form of the standard boundary quotient map. -/
def normKernelToUnitsBoundaryQuotientMonoidHom :
    normKernelSubgroup (Gal(L / K)) Lˣ →*
      Multiplicative
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) :=
  additiveHomToMultiplicativeHom
    (additiveNormKernelToUnitsBoundaryQuotientHom K L g)

/-- The kernel of the standard boundary quotient map is the augmentation
subgroup generated by `ρ(g)-1`. -/
theorem normKernelToUnitsBoundaryQuotientMonoidHom_ker :
    kernelOfAdditiveQuotientHom
        (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
        (normKernelToUnitsBoundaryQuotientMonoidHom K L g) =
      (augmentationSubgroup (Gal(L / K)) Lˣ g).subgroupOf
        (normKernelSubgroup (Gal(L / K)) Lˣ) := by
  ext x
  constructor
  · intro hx
    have hx0 := congrArg Multiplicative.toAdd hx
    change
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
          (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        0 at hx0
    rcases ((Submodule.Quotient.mk_eq_zero
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))).1 hx0) with ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    have hy' := congrArg
      (fun z : LinearMap.ker (unitsNormLinearMap K L) =>
        Additive.toMul (z : Additive Lˣ)) hy
    simp only [unitsRhoSubToNormKerLinearMap,
      additiveNormKernelEquivUnitsNormKer] at hy'
    exact hy'
  · intro hx
    change (x : Lˣ) ∈ augmentationSubgroup (Gal(L / K)) Lˣ g at hx
    rcases hx with ⟨y, hy⟩
    apply Multiplicative.toAdd.injective
    change
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)).mkQ
          (additiveNormKernelEquivUnitsNormKer K L (Additive.ofMul x)) =
        0
    apply (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))).2
    refine ⟨Additive.ofMul y, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    simp only [unitsRhoSubToNormKerLinearMap,
      additiveNormKernelEquivUnitsNormKer]
    exact hy

end

/-- Every class of the standard boundary quotient has a representative in
the multiplicative norm kernel. -/
theorem normKernelToUnitsBoundaryQuotientMonoidHom_surjective
    [Fintype (Gal(L / K))] (g : Gal(L / K)) :
    Function.Surjective
      (normKernelToUnitsBoundaryQuotientMonoidHom K L g) := by
  intro q
  rcases Submodule.mkQ_surjective
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
      (Multiplicative.toAdd q) with ⟨z, hz⟩
  let x :=
    Additive.toMul ((additiveNormKernelEquivUnitsNormKer K L).symm z)
  refine ⟨x, ?_⟩
  apply Multiplicative.toAdd.injective
  exact hz

section

variable [Fintype (Gal(L / K))] (g : Gal(L / K))

/-- The multiplicative Herbrand quotient is the standard additive boundary
quotient used by mathlib's finite-cyclic Tate complex. -/
def herbrandHminusOneMulEquivUnitsBoundaryQuotient :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃*
      Multiplicative
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) :=
  (HerbrandHMinusOne.equiv (G := Gal(L / K)) (A := Lˣ) g).trans
    (quotientMulEquivOfSurjectiveAdditiveQuotient
      (LinearMap.range (unitsRhoSubToNormKerLinearMap K L g))
      ((augmentationSubgroup (Gal(L / K)) Lˣ g).subgroupOf
        (normKernelSubgroup (Gal(L / K)) Lˣ))
      (normKernelToUnitsBoundaryQuotientMonoidHom K L g)
      (normKernelToUnitsBoundaryQuotientMonoidHom_ker K L g)
      (normKernelToUnitsBoundaryQuotientMonoidHom_surjective K L g))

/-- Type-level comparison with the standard boundary quotient. -/
def herbrandHminusOneEquivUnitsBoundaryQuotient :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃
      LinearMap.ker (unitsNormLinearMap K L) ⧸
        LinearMap.range (unitsRhoSubToNormKerLinearMap K L g) :=
  mulEquivMultiplicativeToEquiv
    (herbrandHminusOneMulEquivUnitsBoundaryQuotient K L g)

end

variable [FiniteDimensional K L] (g : Gal(L / K)) (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g)

/-- Mathlib's degree-minus-one Tate object is its standard finite-cyclic
boundary quotient `ker N / im(ρ(g)-1)`. -/
noncomputable def unitsTateHminusOneIsoBoundaryQuotient :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) ≅
      ModuleCat.of ℤ
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range (unitsRhoSubToNormKerLinearMap K L g)) := by
  letI : IsCyclic (Gal(L / K)) :=
    CyclicCohomology.isCyclic_of_generator g hg
  letI : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  let T :=
    Rep.FiniteCyclicGroup.subCompNormHom (Rep.ofAlgebraAutOnUnits K L) g
  have hmap :
      T.moduleCatToCycles =
          unitsRhoSubToNormKerLinearMap K L g := by
    ext x
    rfl
  have e := T.moduleCatHomologyIso
  change
    T.homology ≅
      ModuleCat.of ℤ
        (LinearMap.ker (unitsNormLinearMap K L) ⧸
          LinearMap.range
            T.moduleCatToCycles) at e
  rw [hmap] at e
  exact TateCohomology.isoFiniteCyclicNegOne (Rep.ofAlgebraAutOnUnits K L) g hg ≪≫
    e

/-- Genuine comparison of the multiplicative `H⁻¹` quotient
for field units with Mathlib's actual Tate `H⁻¹` object. -/
noncomputable def herbrandHminusOneEquivUnitsTateHminusOne :
    HerbrandHMinusOne (Gal(L / K)) Lˣ g ≃
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) :=
  (herbrandHminusOneEquivUnitsBoundaryQuotient K L g).trans
    (unitsTateHminusOneIsoBoundaryQuotient K L g hg).symm.toLinearEquiv.toEquiv

end
end LocalClassFieldTheory
