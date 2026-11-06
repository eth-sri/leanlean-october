module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayPrimeGeneration
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Rigidity of Frobenius-normalized ray reciprocity

An isomorphism from a ray class group to the Galois group of a finite abelian
extension which sends every prime class to its genuine arithmetic Artin
symbol forces the ray modulus to be defining for that extension.  The proof
compares the given map and genuine global reciprocity at a common multiple
of the given modulus and the extension's full conductor.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

theorem rayRigidity_ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] rayRigidity_ideleClassGroupIsMulCommutative

/-- Frobenius normalization on all primes away from a modulus forces that
modulus to define the genuine norm subgroup of a finite abelian extension. -/
theorem rayModulus_isDefining_of_arithmeticPrimeArtinEquiv
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (m : RayClass.Modulus K)
    (e : RayClass.RayClassGroup m ≃* (L ≃ₐ[K] L))
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (_ : v ∉ m.finitePart.support),
        e (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v))) =
          arithmeticFinitePlacePrimeArtin (K := K) (L := L) v) :
    m.congruenceSubgroup ≤ (_root_.ideleClassNorm K L).range := by
  let H := ideleClassNormConductorialSubgroup (K := K) (L := L)
  let c := H.fullConductor
  let n := c ⊔ m
  have hcn : c ≤ n := le_sup_left
  have hmn : m ≤ n := le_sup_right
  have hnNorm : n.congruenceSubgroup ≤
      (_root_.ideleClassNorm K L).range :=
    (RayClass.Modulus.congruenceSubgroup_antitone hcn).trans
      H.fullConductor_isDefiningModulus
  have hnm : n.congruenceSubgroup ≤ m.congruenceSubgroup :=
    RayClass.Modulus.congruenceSubgroup_antitone hmn
  let qNorm : RayClass.RayClassGroup n →*
      IdeleClassGroup K ⧸ (_root_.ideleClassNorm K L).range :=
    QuotientGroup.map n.congruenceSubgroup
      ((_root_.ideleClassNorm K L).range)
      (MonoidHom.id (IdeleClassGroup K))
      (fun _ hx => hnNorm hx)
  let qRay : RayClass.RayClassGroup n →* RayClass.RayClassGroup m :=
    QuotientGroup.map n.congruenceSubgroup m.congruenceSubgroup
      (MonoidHom.id (IdeleClassGroup K))
      (fun _ hx => hnm hx)
  let genuine : RayClass.RayClassGroup n →* (L ≃ₐ[K] L) :=
    (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L).toMulEquiv.toMonoidHom.comp
      qNorm
  let proposed : RayClass.RayClassGroup n →* (L ≃ₐ[K] L) :=
    e.toMonoidHom.comp qRay
  have hEq : genuine = proposed := by
    apply rayClassGroup_hom_ext_finitePrime n
    intro v hvn
    have hvm : v ∉ m.finitePart.support := by
      intro hv
      exact hvn ((Finsupp.support_mono hmn.1) hv)
    change Reciprocity.arithmeticGlobalNormResidueMonoidHom K L
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v)) =
      e (QuotientGroup.mk' m.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v)))
    rw [hprime v hvm]
    exact DFunLike.congr_fun
      (Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
        (K := K) (L := L)) (IdeleGroup.finitePrimeIdele v)
  intro x hx
  have hRay : qRay (QuotientGroup.mk' n.congruenceSubgroup x) = 1 := by
    change QuotientGroup.mk' m.congruenceSubgroup x = 1
    simp_all
  have hArtin : Reciprocity.arithmeticGlobalNormResidueMonoidHom K L x = 1 := by
    have h := DFunLike.congr_fun hEq
      (QuotientGroup.mk' n.congruenceSubgroup x)
    change Reciprocity.arithmeticGlobalNormResidueMonoidHom K L x =
      e (qRay (QuotientGroup.mk' n.congruenceSubgroup x)) at h
    rw [hRay, map_one] at h
    exact h
  rw [← MonoidHom.mem_ker,
    Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker] at hArtin
  exact hArtin

/-- A Frobenius-normalized ray-class *isomorphism* also identifies the
extension's genuine norm subgroup exactly with the ray congruence subgroup.
The reverse inclusion follows because the induced quotient map is a
surjection between finite groups of the same order. -/
theorem rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (m : RayClass.Modulus K)
    (e : RayClass.RayClassGroup m ≃* (L ≃ₐ[K] L))
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (_ : v ∉ m.finitePart.support),
        e (QuotientGroup.mk' m.congruenceSubgroup
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (IdeleGroup.finitePrimeIdele v))) =
          arithmeticFinitePlacePrimeArtin (K := K) (L := L) v) :
    (_root_.ideleClassNorm K L).range = m.congruenceSubgroup := by
  have hle : m.congruenceSubgroup ≤
      (_root_.ideleClassNorm K L).range :=
    rayModulus_isDefining_of_arithmeticPrimeArtinEquiv m e hprime
  let q : RayClass.RayClassGroup m →*
      IdeleClassGroup K ⧸ (_root_.ideleClassNorm K L).range :=
    QuotientGroup.map m.congruenceSubgroup
      ((_root_.ideleClassNorm K L).range)
      (MonoidHom.id (IdeleClassGroup K))
      (fun _ hx => hle hx)
  have hqSurj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective ((_root_.ideleClassNorm K L).range) y
    exact ⟨QuotientGroup.mk' m.congruenceSubgroup x, rfl⟩
  have hcard : Nat.card (RayClass.RayClassGroup m) =
      Nat.card (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K L).range) :=
    (Nat.card_congr e.toEquiv).trans
      (Nat.card_congr
        (Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv K L).toEquiv.symm)
  have hqInj : Function.Injective q :=
    (hqSurj.bijective_of_nat_card_le hcard.le).1
  apply le_antisymm
  · intro x hx
    have hqx : q (QuotientGroup.mk' m.congruenceSubgroup x) = 1 := by
      change QuotientGroup.mk' ((_root_.ideleClassNorm K L).range) x = 1
      simp_all
    have hx' : QuotientGroup.mk' m.congruenceSubgroup x = 1 :=
      hqInj (hqx.trans (map_one q).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  omega
