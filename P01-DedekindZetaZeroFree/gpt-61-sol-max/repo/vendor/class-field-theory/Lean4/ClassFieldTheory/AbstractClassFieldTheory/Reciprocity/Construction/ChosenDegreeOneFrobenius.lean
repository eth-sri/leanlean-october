module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.Universal

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

universe u

namespace ClassFormation

open CyclicCohomology

/-!
# The chosen degree-one Frobenius element

Surjectivity of the normalized degree supplies a Frobenius-semigroup element
of exponent one.  The chosen object and its specification are kept together
here so the multiplicativity proof can consume a named choice boundary.
-/

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

section
variable (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
include D K L hLK hLnormal
/-- A chosen degree-one element of `G(\widetilde L/K)`, packaged as an
element of the Frobenius semigroup. -/
noncomputable def chosenDegreeOneFrobeniusElement   :
    D.FrobeniusElements K L hLK := by
  let hsurj := D.extensionNormalizedDegreeContinuous_surjective K L hLK
    (Multiplicative.ofAdd (1))
  refine ⟨Classical.choose hsurj, 1, Nat.one_pos, ?_⟩
  rw [pow_one, ← D.extensionNormalizedDegreeContinuous_apply]
  exact Classical.choose_spec hsurj

/--
Establishes the identity `D.frobeniusExponent K L hLK (D.chosenDegreeOneFrobeniusElement K L hLK)
= 1`.
-/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusElement   :
    D.frobeniusExponent K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK) = 1 := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1)) ^
        D.frobeniusExponent K L hLK
          (D.chosenDegreeOneFrobeniusElement K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK)).symm
    _ = Multiplicative.ofAdd (1) := by
      rw [← D.extensionNormalizedDegreeContinuous_apply]
      change D.extensionNormalizedDegreeContinuous K L hLK
        (Classical.choose
          (D.extensionNormalizedDegreeContinuous_surjective K L hLK
            (Multiplicative.ofAdd (1)))) =
          Multiplicative.ofAdd (1)
      exact Classical.choose_spec
        (D.extensionNormalizedDegreeContinuous_surjective K L hLK
          (Multiplicative.ofAdd (1)))
    _ = (Multiplicative.ofAdd (1)) ^ (1) := by simp
end


end DegreeData

end

end ClassFormation
