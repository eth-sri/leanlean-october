module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Rational prime classes in rational ray class groups

For a prime `q` away from a rational modulus `(m)`, the normalized
one-place prime idèle represents the direct residue unit `q` in
`(ZMod m)ˣ`.  This is the ideal-theoretic arithmetic input needed to
compare rational ray reciprocity with the cyclotomic character.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

/-- The canonical rational ray-class identification, with the native
quotient topology on the idèle-class quotient and the finite discrete
topology on `(ZMod m)ˣ`.  Thus this is the topological form of the
rational ray-class computation, not only an abstract finite-group
isomorphism. -/
noncomputable def rationalRayClassGroupContinuousMulEquivZModUnits
    (m : ℕ) (hm : m ≠ 0) :
    RayClass.RayClassGroup (RayClass.rationalModulus m) ≃ₜ*
      (ZMod m)ˣ := by
  letI : DiscreteTopology
      (RayClass.RayClassGroup
        (RayClass.rationalModulus m)) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup
        (RayClass.rationalModulus m))
  exact
    { RayClass.rationalRayClassGroupEquivZModUnits m hm with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Forgetting topology from the canonical rational ray-class
identification recovers the standard residue-class equivalence
literally. -/
@[simp]
theorem rationalRayClassGroupContinuousMulEquivZModUnits_apply
    (m : ℕ) (hm : m ≠ 0)
    (c : RayClass.RayClassGroup
      (RayClass.rationalModulus m)) :
    rationalRayClassGroupContinuousMulEquivZModUnits m hm c =
      RayClass.rationalRayClassGroupEquivZModUnits m hm c := by
  rfl





















































































































































































































end GlobalClassFields
end GlobalClassFieldTheory

end
