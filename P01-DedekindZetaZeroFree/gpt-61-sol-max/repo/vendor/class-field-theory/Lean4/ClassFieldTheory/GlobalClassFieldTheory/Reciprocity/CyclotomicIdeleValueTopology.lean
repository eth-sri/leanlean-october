module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValue
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicNormOneCorrection
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Topology of the rational cyclotomic idele value

The rational cyclotomic idele value is constructed multiplicatively in
`CyclotomicIdeleValue`.  For descent to the additive idele class group and
for the valuation package, this file records its genuine continuous additive
form.  Its finite reductions give the open-kernel finite quotients which form
the profinite neighbourhood system used after principal-idèle vanishing has
been proved.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- The rational cyclotomic idele value in continuous additive notation. -/
noncomputable def rationalCyclotomicZHatIdeleValueContinuousAdd :
    Additive (IdeleGroup ℚ) →ₜ+ ZHat where
  __ :=
    rationalCyclotomicZHatIdeleValue.toMonoidHom.toAdditiveLeft
  continuous_toFun :=
    continuous_toAdd.comp
      (rationalCyclotomicZHatIdeleValue.continuous_toFun.comp
        continuous_toMul)

/-- Evaluation of the continuous additive rational cyclotomic value agrees
with the original multiplicative value. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValueContinuousAdd_apply
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValueContinuousAdd
        (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a) :=
  rfl






















































/-- Reduction of the rational cyclotomic idele value modulo a positive
integer, as an actual continuous additive homomorphism. -/
noncomputable def rationalCyclotomicZHatIdeleValueReduction
    (n : ℕ) (hn : 0 < n) :
    Additive (IdeleGroup ℚ) →ₜ+ ZMod n :=
  (zHatReduction n hn).comp
    rationalCyclotomicZHatIdeleValueContinuousAdd

/-- Evaluation of a finite reduction is reduction of the original
cyclotomic value. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValueReduction_apply
    (n : ℕ) (hn : 0 < n) (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValueReduction n hn
        (Additive.ofMul a) =
      zHatReduction n hn
        (Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a)) :=
  rfl


















































variable (K : Type) [Field K] [NumberField K]

/-- The unnormalized cyclotomic norm composite, bundled with its actual
continuity.  Continuity here uses the global idele norm rather than a
quotient-level substitute. -/
noncomputable def cyclotomicZHatNormCompositeContinuous :
    Additive (IdeleGroup K) →ₜ+ ZHat where
  __ := cyclotomicZHatNormComposite K
  continuous_toFun := by
    change
      Continuous
        (fun a : Additive (IdeleGroup K) =>
          Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (IdeleGroup.norm ℚ K (Additive.toMul a))))
    exact
      continuous_toAdd.comp
        (rationalCyclotomicZHatIdeleValue.continuous_toFun.comp
          ((IdeleGroup.norm_continuous ℚ K).comp
            continuous_toMul))

/-- The continuous norm composite agrees pointwise with the underlying
unnormalized cyclotomic norm composite. -/
@[simp]
theorem cyclotomicZHatNormCompositeContinuous_apply
    (a : IdeleGroup K) :
    cyclotomicZHatNormCompositeContinuous K (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K a)) :=
  rfl

/-- The unnormalized composite, continuously restricted to its actual
multiple subgroup `f_K ℤ̂`. -/
noncomputable def cyclotomicZHatNormCompositeInMulNatRangeContinuous :
    Additive (IdeleGroup K) →ₜ+
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range where
  __ := cyclotomicZHatNormCompositeInMulNatRange K
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (cyclotomicZHatNormCompositeContinuous K).continuous_toFun

/-- Coercing the continuous range-restricted norm composite recovers the
underlying cyclotomic norm composite. -/
@[simp]
theorem cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply
    (a : Additive (IdeleGroup K)) :
    (cyclotomicZHatNormCompositeInMulNatRangeContinuous K a :
        ZHat) =
      cyclotomicZHatNormComposite K a :=
  rfl

/-- The normalized cyclotomic value on ideles as a genuine continuous
additive homomorphism. -/
noncomputable def normalizedCyclotomicZHatIdeleValueContinuous :
    Additive (IdeleGroup K) →ₜ+ ZHat :=
  (zHatDivide
      (cyclotomicZHatIntersectionDegree K)
      (cyclotomicZHatIntersectionDegree_pos K)).comp
    (cyclotomicZHatNormCompositeInMulNatRangeContinuous K)

/-- The continuous normalized cyclotomic value agrees pointwise with its
underlying additive homomorphism. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValueContinuous_apply
    (a : Additive (IdeleGroup K)) :
    normalizedCyclotomicZHatIdeleValueContinuous K a =
      normalizedCyclotomicZHatIdeleValue K a :=
  rfl

/-- The normalized cyclotomic value in continuous multiplicative notation.
This is the source homomorphism which descends through the principal-idèle
quotient once the rational principal product formula has been established. -/
noncomputable def normalizedCyclotomicZHatIdeleValueContinuousMul :
    IdeleGroup K →ₜ* Multiplicative ZHat where
  toMonoidHom :=
    AddMonoidHom.toMultiplicativeRight
      (normalizedCyclotomicZHatIdeleValueContinuous K).toAddMonoidHom
  continuous_toFun :=
    continuous_ofAdd.comp
      ((normalizedCyclotomicZHatIdeleValueContinuous K).continuous_toFun.comp
        continuous_toAdd)

/-- The multiplicative continuous normalized value is the multiplicative
form of the underlying additive normalized value. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValueContinuousMul_apply
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleValueContinuousMul K a =
      Multiplicative.ofAdd
        (normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)) :=
  rfl

/-- The actual norm-one ideles already have dense normalized cyclotomic
value.  The source reduction uses the positive archimedean correction,
whose cyclotomic value is trivial. -/
theorem normalizedCyclotomicZHatIdeleValue_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul (b : IdeleGroup K))) := by
  apply (normalizedCyclotomicZHatIdeleValue_denseRange K).mono
  rintro z ⟨a, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue
      K (Additive.toMul a)
  refine ⟨b, ?_⟩
  simpa using hb

end Reciprocity
end GlobalClassFieldTheory

end
