module

public import Mathlib

public import GaloisCohomology.Kummer.Abstract.KummerCyclicOperator

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: descending the global operator

This file constructs, rather than assumes, the endomorphism of `A_L` induced
by a global equivariant endomorphism `wp : A ⟶ A`.  It also embeds a
`G_K`-fixed global kernel element into the invariant subtype defining `A_L`
and supplies these constructions to the finite cyclic single-radical theorem.

The result remains only the finite cyclic step of the finite abelian Kummer decomposition, not the
full abelian Kummer correspondence.
-/

noncomputable section

open CategoryTheory

/-- The endomorphism of `A_L` induced functorially by a global equivariant
endomorphism `wp : A ⟶ A`: first restrict to `G_K`, then pass to the
`G_L`-invariants and the quotient action. -/
noncomputable def extensionFixedEndomorphism
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A)  :=
  (Rep.quotientToInvariantsFunctor (k := ℤ) (extensionSubgroup K L hLK)).map
    ((Rep.resFunctor K.toSubgroup.subtype).map wp)

/-- A global element fixed by `G_K`, viewed in the invariant subtype which
is the carrier of `A_L`. -/
noncomputable def extensionFixedKernelElement
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    (extensionFixedRepresentation A K L hLK hnormal).V :=
  ⟨xi, by
    intro s
    change A.ρ s.1.1 xi = xi
    apply hxi_fixed⟩

/-- The underlying value of the fixed kernel element is the selected global kernel element. -/
@[simp]
theorem extensionFixedKernelElement_val
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    (extensionFixedKernelElement A K L hLK xi hxi_fixed).1 = xi := rfl

/-- The extension-fixed endomorphism acts on underlying values by the global operator. -/
@[simp]
theorem extensionFixedEndomorphism_apply_val
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A) (x : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedEndomorphism A K L hLK wp).hom x).1 = wp.hom x.1 := rfl




















































































end
end KummerTheory
