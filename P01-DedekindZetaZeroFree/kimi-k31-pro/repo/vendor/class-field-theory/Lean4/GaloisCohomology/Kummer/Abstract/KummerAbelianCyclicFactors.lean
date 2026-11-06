module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import GaloisCohomology.Kummer.Abstract.KummerGlobalOperator

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
# finite abelian Kummer theory, the finite abelian Kummer decomposition: cyclic factors of a finite abelian extension

The proof of the finite abelian Kummer decomposition reduces a finite abelian extension to cyclic
subextensions.  This file supplies the group-theoretic source for that step.
A finite commutative group is written as a finite product of cyclic `ZMod`
groups.  The kernels of its coordinate maps have trivial intersection.
Pulling those kernels back along a quotient map produces intermediate
subgroups whose quotients are finite cyclic and whose intersection is the
original normal subgroup.

No radical generators or field-lattice endpoint are asserted here.
-/

noncomputable section

section FiniteAbelianCyclicFactors

/-- Coordinate characters obtained from the structure theorem separate the
elements of a finite commutative group. -/
theorem finiteCommGroup_exists_jointlyFaithful_cyclic_factors
    (Q : Type*) [CommGroup Q] [Finite Q] :
    ∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let f : ∀ i, Q →* Multiplicative (ZMod (m i)) := fun i =>
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (m j))) i).comp e
  refine ⟨ι, hι, m, hm, f, ?_, ?_⟩
  · intro i
    exact (Function.surjective_eval i).comp e.surjective
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply e.injective
      ext i
      have hxi : x ∈ MonoidHom.ker (f i) :=
        (Subgroup.mem_iInf.mp hx) i
      simpa [f] using MonoidHom.mem_ker.mp hxi
    · exact bot_le

section Pullback

variable {P C : Type*} [Group P] [Group C]
  (H : Subgroup P) [H.Normal]

/-- Pull a quotient-factor kernel back to the original group. -/
def cyclicFactorSubgroup (f : (P ⧸ H) →* C) : Subgroup P :=
  MonoidHom.ker (f.comp (QuotientGroup.mk' H))

/-- The kernel subgroup attached to a cyclic quotient factor is normal. -/
instance cyclicFactorSubgroup_normal (f : (P ⧸ H) →* C) :
    (cyclicFactorSubgroup H f).Normal :=
  MonoidHom.normal_ker _







variable {ι : Type*} {Cι : ι → Type*} [∀ i, Group (Cι i)]



end Pullback

end FiniteAbelianCyclicFactors

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A closed abstract field subgroup `G_L` remains closed when regarded as
a subgroup of the larger abstract field subgroup `G_K`. -/
theorem extensionSubgroup_isClosed
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup) := by
  change IsClosed ((fun x : K.toSubgroup => (x : G)) ⁻¹' (L : Set G))
  exact L.isClosed'.preimage continuous_subtype_val

variable [IsTopologicalGroup G]

/-- A pulled-back cyclic factor kernel is closed inside `G_K`: the finite
quotient by `G_L` is discrete, and the factor kernel is pulled back along the
continuous quotient map. -/
theorem cyclicFactorSubgroup_isClosed
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    IsClosed
      (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
        Set K.toSubgroup) := by
  let H := extensionSubgroup (G := G) K L hLK
  let : IsClosed (H : Set K.toSubgroup) := extensionSubgroup_isClosed K L hLK
  change IsClosed
    ((QuotientGroup.mk' H) ⁻¹' (MonoidHom.ker f : Set (K.toSubgroup ⧸ H)))
  exact (isClosed_discrete _).preimage QuotientGroup.continuous_mk

/-- The closed abstract intermediate field attached to one cyclic coordinate
factor of `G_K/G_L`. -/
def closedCyclicFactorSubgroup
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    ClosedSubgroup G where
  toSubgroup :=
    (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f).map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
          Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (cyclicFactorSubgroup_isClosed K L hLK f)

/-- The cyclic-factor intermediate subgroup lies below the base subgroup
`G_K`. -/
theorem closedCyclicFactorSubgroup_le_base
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    (closedCyclicFactorSubgroup K L hLK f).toSubgroup ≤ K.toSubgroup := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property



/-- Viewed inside `G_K`, the closed cyclic-factor subgroup has exactly the
pulled-back coordinate kernel as its extension subgroup. -/
theorem extensionSubgroup_closedCyclicFactorSubgroup_eq
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
        (closedCyclicFactorSubgroup_le_base K L hLK f) =
      cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f := by
  ext x
  simp [extensionSubgroup, closedCyclicFactorSubgroup]
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The extension subgroup of a closed cyclic factor is normal in `G_K`. -/
instance extensionSubgroup_closedCyclicFactorSubgroup_normal
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    (extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
      (closedCyclicFactorSubgroup_le_base K L hLK f)).Normal := by
  rw [extensionSubgroup_closedCyclicFactorSubgroup_eq K L hLK f]
  infer_instance







end ClosedCyclicSubextensions

end
end KummerTheory
