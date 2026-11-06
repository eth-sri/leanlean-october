module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Lattice operations on narrow finite conductors

Increasing a modulus decreases its ray congruence subgroup.  This
contravariance makes the narrow finite conductor of an intersection of
norm subgroups the pointwise maximum of their narrow finite conductors.
Under class-field correspondence, this is the finite-part lcm formula
for a compositum.  For a generated subgroup one obtains the
complementary divisibility by the pointwise minimum.
-/

open scoped NumberField Classical


namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Finite idèle congruence subgroups are contravariant in the modulus. -/
theorem rayClassFiniteCongruenceSubgroup_antitone
    {m n : RayClass.FiniteModulus K} (hmn : m ≤ n) :
    RayClass.finiteCongruenceSubgroup n ≤
      RayClass.finiteCongruenceSubgroup m := by apply RayClass.finiteCongruenceSubgroup_antitone <;> assumption

/-- Infinite idèle congruence subgroups are contravariant in the full
modulus: selecting more real places imposes more positivity conditions. -/
theorem rayClassInfiniteCongruenceSubgroup_antitone
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    n.infiniteCongruenceSubgroup ≤
      m.infiniteCongruenceSubgroup := by apply RayClass.Modulus.infiniteCongruenceSubgroup_antitone <;> assumption

/-- Idèle congruence subgroups are contravariant in the modulus. -/
theorem rayClassIdeleCongruenceSubgroup_antitone
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    n.ideleCongruenceSubgroup ≤
      m.ideleCongruenceSubgroup := by apply RayClass.Modulus.ideleCongruenceSubgroup_antitone <;> assumption

/-- Ray congruence subgroups in the idèle class group are
contravariant in the modulus. -/
theorem rayClassCongruenceSubgroup_antitone
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    n.congruenceSubgroup ≤
      m.congruenceSubgroup := by apply RayClass.Modulus.congruenceSubgroup_antitone <;> assumption

/-- Once a modulus defines a subgroup, every larger modulus also
defines it. -/
theorem isDefiningModulus_mono
    (H : Subgroup (IdeleClassGroup K))
    {m n : RayClass.Modulus K}
    (hm : IsDefiningModulus H m)
    (hmn : m ≤ n) :
    IsDefiningModulus H n :=
  (rayClassCongruenceSubgroup_antitone
    (K := K) hmn).trans hm

namespace ConductorialSubgroup

/-- The exact narrow finite conductor, interpreted as a full modulus with
positivity at every real place, is a defining modulus. -/
theorem narrowFiniteConductor_isDefiningModulus
    (H : ConductorialSubgroup K) :
    IsDefiningModulus H.1
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) := by
  obtain ⟨m, hm, hfinite⟩ :=
    H.exists_definingModulus_finitePart_eq_narrowFiniteConductor
  apply isDefiningModulus_mono H.1 hm
  exact ⟨hfinite.le, Finset.subset_univ _⟩
