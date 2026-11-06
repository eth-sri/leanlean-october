module

public import Mathlib

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
      have hxi  :=
        (Subgroup.mem_iInf.mp hx) i
      simpa [f] using MonoidHom.mem_ker.mp hxi
    · exact bot_le

section Pullback

variable {P C : Type*} [Group P] [Group C]
  (H : Subgroup P) [H.Normal]












































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








































































































































































end ClosedCyclicSubextensions

end
end KummerTheory
