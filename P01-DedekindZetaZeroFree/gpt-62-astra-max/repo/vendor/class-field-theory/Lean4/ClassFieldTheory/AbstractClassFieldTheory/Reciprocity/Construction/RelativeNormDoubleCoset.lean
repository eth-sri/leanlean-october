module

public import ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm
public import GaloisCohomology.Cyclic.IntegralRepUniverse
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

/-!
# The abstract reciprocity construction: the double-coset decomposition of a relative norm

The norm calculation in the proof of transfer--norm naturality partitions
the left cosets for an extension by the orbits of an intermediate subgroup.
This file constructs that partition from Mathlib's class-formula equivalence
and reindexes the actual relative norm along it.
-/

noncomputable section

open scoped BigOperators

open CyclicCohomology MulAction

section doubleCosetEquivalences

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Membership in the stabilizer of a left coset is the literal conjugate
intersection condition.  For the representative `t⁻¹` this reads
`k' ∈ K' ∩ t⁻¹ S t`, the subgroup occurring in the classical
double-coset norm calculation. -/
theorem mem_relativeNormDoubleCoset_stabilizer_iff
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (t : K.toSubgroup)
    (k' : extensionSubgroup K K' hK'K) :
    k' ∈ MulAction.stabilizer (extensionSubgroup K K' hK'K)
        (QuotientGroup.mk t :
          K.toSubgroup ⧸ extensionSubgroup K S hSK) ↔
      t.1⁻¹ * k'.1.1 * t.1 ∈ S.toSubgroup := by
  simp
  change QuotientGroup.mk (k'.1 * t) = QuotientGroup.mk t ↔ _
  rw [QuotientGroup.eq]
  change (k'.1 * t).1⁻¹ * t.1 ∈ S.toSubgroup ↔ _
  constructor
  · intro h
    simpa [mul_assoc] using S.toSubgroup.inv_mem h
  · intro h
    simpa [mul_assoc] using S.toSubgroup.inv_mem h

end doubleCosetEquivalences

section relativeNormFormulas

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

end relativeNormFormulas

end
end ClassFormation
