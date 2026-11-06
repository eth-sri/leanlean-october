module

public import GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors
public import GaloisCohomology.Cyclic.IntegralRepUniverse
public import GaloisCohomology.Cyclic.NormKernelVanishing

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: assembling cyclic radicals

This file connects elements produced in the invariant subtype `A_M` to the
ambient representation `A`.  A cyclic radical with trivial stabilizer in
`G_K / G_M` is fixed in the ambient module by exactly `G_M`.  Consequently,
a family of such radicals whose subgroups intersect in `G_L` generates the
abstract field `L` over `K`.
-/


variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Membership in `G_L`, regarded as a subgroup of `G_K`, is the same as
ambient membership in the closed subgroup `G_L`. -/
@[simp]
theorem mem_extensionSubgroup_iff
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (k : K.toSubgroup) :
    k ∈ extensionSubgroup (G := G) K L hLK ↔ (k : G) ∈ L :=
  Iff.rfl

/-- The quotient action on an invariant subtype is the original ambient
action after choosing a representative in `G_K`. -/
@[simp]
theorem extensionFixedRepresentation_quotient_mk_apply_val
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K M hMK).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (k : K.toSubgroup) :
    ((extensionFixedRepresentation A K M hMK hnormal).ρ
      ((QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k) a).1 =
      A.ρ k.1 a.1 := rfl
