module

public import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Frobenius lifts on completed p-adic Lubin--Tate levels

Arithmetic Frobenius on the completed maximal-unramified p-adic field fixes
the standard primitive Lubin--Tate polynomial, since that polynomial descends
to `ℚ_[p]`.  Using the completed primitive power basis, it therefore extends
to a semilinear automorphism of every completed level.  A finite unit
parameter prescribes the image of the primitive root.

The construction is an actual field automorphism.  Surjectivity follows from
the theorem that every completed unit-parameter root generates the completed
level.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

section
variable (p : ℕ) [Fact p.Prime] (n : ℕ)
include p n
/-- The ordinary completed-base algebra structure on a completed level,
named so it can coexist with the Frobenius-twisted structure. -/
@[reducible]
noncomputable def padicCompletedLevelOriginalAlgebra
      :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  inferInstance

/-- The codomain algebra structure whose scalar map is arithmetic
Frobenius followed by the ordinary scalar inclusion. -/
@[reducible]
noncomputable def padicCompletedLevelFrobeniusAlgebra
      :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  RingHom.toAlgebra
    ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
      (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)















/-- Arithmetic Frobenius fixes the completed primitive polynomial because
its coefficients descend to `ℚ_[p]`. -/
theorem padicCompletedPrimitivePolynomial_frobenius
      :
    (padicCompletedPrimitivePolynomial p n).map
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom =
      padicCompletedPrimitivePolynomial p n := by
  unfold padicCompletedPrimitivePolynomial
  have hcomp :
      ((padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom).comp
          (algebraMap ℚ_[p] (padicCompletedUnramifiedField p)) =
        algebraMap ℚ_[p] (padicCompletedUnramifiedField p) := by
    apply RingHom.ext
    intro a
    exact (padicCompletedUnramifiedFrobenius p).commutes a
  rw [Polynomial.map_map, hcomp]
end


















































































































































































































section
variable (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
include p n u
/-- The direct completed standard unit action annihilates the primitive
minimal polynomial for the Frobenius-twisted codomain structure. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
      :
    @Polynomial.aeval
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelFrobeniusAlgebra p n)
        (((padicCompletedStandardPrimitivePointUnitAction p n u :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n))
        (minpoly (padicCompletedUnramifiedField p)
          (padicCompletedPrimitiveRoot p n)) =
      0 := by
  rw [padicCompletedPrimitiveRoot_minpoly]
  change Polynomial.eval₂
      ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
      (padicCompletedPrimitivePolynomial p n) = 0
  rw [← Polynomial.eval₂_map,
    padicCompletedPrimitivePolynomial_frobenius]
  rw [← Polynomial.eval_map]
  exact
    padicCompletedStandardPrimitivePointUnitAction_isRoot p n u

/-- The semilinear algebra homomorphism extending arithmetic Frobenius and
sending the primitive root to its actual completed standard unit action. -/
noncomputable def padicCompletedUnitFrobeniusLiftAlgHom
      :
    @AlgHom
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      (padicCompletedLevelField p n)
      _ _ _
      (padicCompletedLevelOriginalAlgebra p n)
      (padicCompletedLevelFrobeniusAlgebra p n) :=
  @PowerBasis.lift
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n)) (by
      rw [padicCompletedPrimitivePowerBasis_gen]
      exact
        padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
          p n u)

/-- The direct unit-indexed semilinear homomorphism sends the primitive
root to the actual completed standard unit action. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot
      :
    padicCompletedUnitFrobeniusLiftAlgHom p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) := by
  change padicCompletedUnitFrobeniusLiftAlgHom p n u
      (padicCompletedPrimitivePowerBasis p n).gen = _
  exact @PowerBasis.lift_gen
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n))
    (padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
      p n u)

/-- The underlying field homomorphism of the unit-indexed completed
Frobenius lift. -/
noncomputable def padicCompletedUnitFrobeniusLift
      :
    padicCompletedLevelField p n →+*
      padicCompletedLevelField p n :=
  @AlgHom.toRingHom
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedUnitFrobeniusLiftAlgHom p n u)

/-- The direct unit-indexed completed Frobenius lift acts on base scalars
by arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLift_algebraMap
     
    (b : padicCompletedUnramifiedField p) :
    padicCompletedUnitFrobeniusLift p n u
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) := by
  change padicCompletedUnitFrobeniusLiftAlgHom p n u
      (@algebraMap
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelOriginalAlgebra p n) b) =
    @algebraMap
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      _ _ (padicCompletedLevelFrobeniusAlgebra p n) b
  exact @AlgHom.commutes
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedUnitFrobeniusLiftAlgHom p n u) b

/-- The direct unit-indexed completed Frobenius lift has its prescribed
action on the primitive root. -/
@[simp]
theorem padicCompletedUnitFrobeniusLift_primitiveRoot
      :
    padicCompletedUnitFrobeniusLift p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) :=
  padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot p n u

/-- The direct unit-indexed completed Frobenius lift is surjective. -/
theorem padicCompletedUnitFrobeniusLift_surjective
      :
    Function.Surjective (padicCompletedUnitFrobeniusLift p n u) := by
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let y : L :=
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) : L)
  let σ : L →+* L := padicCompletedUnitFrobeniusLift p n u
  let R : Subring L := σ.range
  have hbase (b : E) : algebraMap E L b ∈ R := by
    refine
      ⟨algebraMap E L
        ((padicCompletedUnramifiedFrobenius p).symm b), ?_⟩
    change σ
        (algebraMap E L
          ((padicCompletedUnramifiedFrobenius p).symm b)) =
      algebraMap E L b
    rw [show σ = padicCompletedUnitFrobeniusLift p n u by rfl,
      padicCompletedUnitFrobeniusLift_algebraMap,
      (padicCompletedUnramifiedFrobenius p).apply_symm_apply]
  let S : Subalgebra E L :=
    { R with
      algebraMap_mem' := hbase }
  have hy : y ∈ S := by
    refine ⟨padicCompletedPrimitiveRoot p n, ?_⟩
    exact padicCompletedUnitFrobeniusLift_primitiveRoot p n u
  have hle : Algebra.adjoin E ({y} : Set L) ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hy
  rw [show Algebra.adjoin E ({y} : Set L) = ⊤ by
        simpa only [E, L, y] using
          padicCompletedStandardPrimitivePointUnitAction_adjoin_eq_top
            p n u] at hle
  have hS : S = ⊤ := top_unique hle
  intro z
  have hz : z ∈ S := by rw [hS]; trivial
  exact hz

/-- The actual field automorphism extending arithmetic Frobenius and acting
on the primitive root by the direct completed standard unit action. -/
noncomputable def padicCompletedUnitFrobeniusLiftEquiv
      :
    padicCompletedLevelField p n ≃+*
      padicCompletedLevelField p n :=
  RingEquiv.ofBijective (padicCompletedUnitFrobeniusLift p n u)
    ⟨(padicCompletedUnitFrobeniusLift p n u).injective,
      padicCompletedUnitFrobeniusLift_surjective p n u⟩

/-- The unit-indexed Frobenius-lift equivalence acts on completed base
scalars by arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_algebraMap
     
    (b : padicCompletedUnramifiedField p) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) :=
  padicCompletedUnitFrobeniusLift_algebraMap p n u b

/-- The unit-indexed Frobenius-lift equivalence acts on the primitive root
by the direct completed standard unit action. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot
      :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) :=
  padicCompletedUnitFrobeniusLift_primitiveRoot p n u
end


end LubinTate

end
