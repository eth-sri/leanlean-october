module

public import Mathlib

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

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

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Finite idèle congruence subgroups are contravariant in the modulus. -/
alias rayClassFiniteCongruenceSubgroup_antitone := _root_.RayClass.finiteCongruenceSubgroup_antitone

section
variable {m n : RayClass.Modulus K} (hmn : m ≤ n)
include m n hmn
/-- Infinite idèle congruence subgroups are contravariant in the full
modulus: selecting more real places imposes more positivity conditions. -/
theorem rayClassInfiniteCongruenceSubgroup_antitone
      :
    n.infiniteCongruenceSubgroup ≤
      m.infiniteCongruenceSubgroup := by
  intro a ha
  rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff] at ha ⊢
  intro v hv
  exact ha v (hmn.2 hv)

/-- Idèle congruence subgroups are contravariant in the modulus. -/
theorem rayClassIdeleCongruenceSubgroup_antitone
      :
    n.ideleCongruenceSubgroup ≤
      m.ideleCongruenceSubgroup := by
  rintro a ⟨haInfinite, haFinite⟩
  exact
    ⟨rayClassInfiniteCongruenceSubgroup_antitone
        (K := K) hmn haInfinite,
      rayClassFiniteCongruenceSubgroup_antitone
        (K := K) hmn.1 haFinite⟩

/-- Ray congruence subgroups in the idèle class group are
contravariant in the modulus. -/
theorem rayClassCongruenceSubgroup_antitone
      :
    n.congruenceSubgroup ≤
      m.congruenceSubgroup := by
  unfold RayClass.Modulus.congruenceSubgroup
  apply Subgroup.map_mono
  exact
    sup_le
      ((rayClassIdeleCongruenceSubgroup_antitone
        (K := K) hmn).trans le_sup_left)
      le_sup_right
end


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















































































end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory

end
