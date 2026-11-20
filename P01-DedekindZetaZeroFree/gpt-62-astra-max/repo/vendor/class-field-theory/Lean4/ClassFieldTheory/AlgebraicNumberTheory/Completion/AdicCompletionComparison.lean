module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
public import Mathlib.NumberTheory.RamificationInertia.Valuation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Comparing the exact-extension and concrete adic-completion maps

The completion map attached to an exact extension of a finite-place
absolute value agrees with the canonical map between the concrete adic
completions at the corresponding finite places.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section

variable (w : HeightOneSpectrum (𝓞 K)) (a : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K w) L)

/-- The concrete homomorphism of adic completions associated with an
exact extension of the normalized absolute value. -/
noncomputable def finitePlaceExtensionAdicCompletionMap :
    w.adicCompletion K →+*
      (finitePlaceExtensionCentre
        (K := K) (L := L) w a).adicCompletion L :=
  (finitePlaceExtensionAdicCompletionRingEquiv
      (K := K) (L := L) w a).toRingHom.comp
    ((AbsoluteValue.completionMap
      (HeightOneSpectrum.adicAbv K w) a.1 a.2).comp
      (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom)

/-- The exact-extension completion map agrees with the field embedding
on elements of the base number field. -/
theorem finitePlaceExtensionAdicCompletionMap_coe
    (x : K) :
    finitePlaceExtensionAdicCompletionMap K L w a
        (x : w.adicCompletion K) =
      (algebraMap K L x :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L) := by
  have hcomparison :
      (relativeFinitePlaceCompletionAlgEquiv w).symm
          x =
        algebraMap K
          (HeightOneSpectrum.adicAbv K w).Completion x := by
    change
      (relativeFinitePlaceCompletionAlgEquiv w).symm
          (algebraMap K (w.adicCompletion K) x) =
        algebraMap K
          (HeightOneSpectrum.adicAbv K w).Completion x
    exact (relativeFinitePlaceCompletionAlgEquiv w).symm.commutes x
  change
    finitePlaceExtensionAdicCompletionRingEquiv
          w a
        (AbsoluteValue.completionMap
          (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm
            x)) =
      _
  rw [hcomparison,
    AbsoluteValue.completionMap_coe,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- The completion map defined using an exact absolute-value extension
is continuous. -/
theorem finitePlaceExtensionAdicCompletionMap_continuous :
    Continuous
      (finitePlaceExtensionAdicCompletionMap K L w a) := by
  exact
    ((relativeFinitePlaceCompletionRingHom_isometry
      (finitePlaceExtensionCentre
          w a)).continuous.comp
      (finitePlaceExtensionCompletionRingEquiv_continuous
          w a)).comp
      ((AbsoluteValue.completionMap_isometry
        (HeightOneSpectrum.adicAbv K w) a.1 a.2).continuous.comp
        (AddMonoidHomClass.isometry_of_norm
          (relativeFinitePlaceCompletionAlgEquiv w).symm
          (relativeFinitePlaceCompletionAlgEquiv_symm_norm w)).continuous)

/-- The exact-extension construction and the canonical completion of the
field embedding agree.  Equality on the dense copy of `K` is extended by
continuity. -/
theorem finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
    (x : w.adicCompletion K) :
    finitePlaceExtensionAdicCompletionMap K L w a x =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a) x := by
  let P := fun y =>
    finitePlaceExtensionAdicCompletionMap K L w a
        (HeightOneSpectrum.adicCompletion.ofCompletion y) =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)
        (HeightOneSpectrum.adicCompletion.ofCompletion y)
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (w.valuation K)) x.toCompletion ?_ ?_
  · change IsClosed
      {y | finitePlaceExtensionAdicCompletionMap K L w a
          (HeightOneSpectrum.adicCompletion.ofCompletion y) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (HeightOneSpectrum.adicCompletion.ofCompletion y)}
    exact isClosed_eq
      ((finitePlaceExtensionAdicCompletionMap_continuous K L w a).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
      ((finitePlaceAdicCompletionMap_continuous K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
  · intro r
    let k : K := WithVal.equiv (w.valuation K) r
    change
      finitePlaceExtensionAdicCompletionMap K L w a
          (HeightOneSpectrum.adicCompletion.ofCompletion
            (r : (w.valuation K).Completion)) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (HeightOneSpectrum.adicCompletion.ofCompletion
            (r : (w.valuation K).Completion))
    change
      finitePlaceExtensionAdicCompletionMap K L w a
          k =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
              w a)
          k
    rw [finitePlaceExtensionAdicCompletionMap_coe,
      finitePlaceAdicCompletionMap_coe]
    change
      (algebraMap K L k :
        (finitePlaceExtensionCentre
            w a).adicCompletion L) =
      (algebraMap K L k :
        (finitePlaceExtensionCentre
            w a).adicCompletion L)
    rfl

end

/-- The concrete completion at a finite place above `w` is finite over the
concrete completion at `w`, for the canonical completion map. -/
theorem finitePlaceAdicCompletionMap_moduleFinite
    [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    letI : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L w W).toAlgebra
    Module.Finite (w.adicCompletion K) (W.1.adicCompletion L) := by
  classical
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
        w).surjective W
  let vK := HeightOneSpectrum.adicAbv K w
  let :=
    (finitePlaceAdicCompletionMap K L w
      (finitePlaceExtensionEquivAbove
          w a)).toAlgebra
  let : Module
      (w.adicCompletion K)
      ((finitePlaceExtensionEquivAbove
          w a).1.adicCompletion L) :=
    Algebra.toModule
  let :=
    (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom.toAlgebra
  let :=
    AbsoluteValue.completionAlgebra vK a.1 a.2
  let :=
    ((algebraMap vK.Completion a.1.Completion).comp
      (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom).toAlgebra
  let : IsScalarTower
      (w.adicCompletion K) vK.Completion a.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :=
    Module.Finite.of_surjective
      (Algebra.linearMap (w.adicCompletion K) vK.Completion)
      (relativeFinitePlaceCompletionAlgEquiv w).symm.surjective
  let :=
    completionModuleFinite vK (RayClass.adicAbv_isNontrivial w) a
  let : Module.Finite (w.adicCompletion K) a.1.Completion :=
    Module.Finite.trans vK.Completion a.1.Completion
  let e :
      a.1.Completion ≃ₐ[w.adicCompletion K]
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a).1.adicCompletion L :=
    { __ :=
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w a
      commutes' := fun x => by
        change
          finitePlaceExtensionAdicCompletionMap K L w a x =
            finitePlaceAdicCompletionMap K L w
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) w a) x
        exact
          finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
            K L w a x }
  exact Module.Finite.equiv e.toLinearEquiv

section

variable (w : HeightOneSpectrum (𝓞 K))

/-- The norm of the image under the concrete adic-completion map is
raised to the exact-extension exponent. -/
theorem finitePlaceExtensionAdicCompletionMap_norm
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    ‖finitePlaceExtensionAdicCompletionMap K L w a x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) w a := by
  change
    ‖finitePlaceExtensionAdicCompletionRingEquiv
          w a
        (AbsoluteValue.completionMap
          (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm x))‖ =
      _
  rw [
    finitePlaceExtensionAdicCompletionRingEquiv_norm,
    (AbsoluteValue.completionMap_isometry
      (HeightOneSpectrum.adicAbv K w) a.1 a.2).norm_map_of_map_zero
        (map_zero
          (AbsoluteValue.completionMap
            (HeightOneSpectrum.adicAbv K w) a.1 a.2)),
    relativeFinitePlaceCompletionAlgEquiv_symm_norm]

/-- The canonical map between concrete adic completions preserves the
valuation ring, expressed by the norm bound defining its unit ball. -/
theorem finitePlaceAdicCompletionMap_norm_le_one_iff
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : w.adicCompletion K) :
    ‖finitePlaceAdicCompletionMap K L w W x‖ ≤ 1 ↔
      ‖x‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
        w).surjective W
  have hnorm :
      ‖finitePlaceExtensionAdicCompletionMap K L w a x‖ =
        ‖finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
              w a) x‖ :=
    congrArg (fun y => ‖y‖)
      (finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
        K L w a x)
  rw [← hnorm,
    finitePlaceExtensionAdicCompletionMap_norm]
  simpa using
    Real.rpow_le_rpow_iff (norm_nonneg x) zero_le_one
      (finitePlaceExtensionExponent_pos
          w a)

end

/-- The valuation of the image under the concrete adic-completion map
is multiplied by the ramification index.  This extends the corresponding
formula for elements of `K` to every element of the completion. -/
theorem finitePlaceExtensionAdicCompletionMap_valued
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    Valued.v (finitePlaceExtensionAdicCompletionMap K L w a x) =
      Valued.v x ^ w.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).asIdeal := by
  let W :=
    finitePlaceExtensionCentre
        w a
  let :=
    finitePlaceExtensionCentre_liesOver
        w a
  by_cases hx : x = 0
  · subst x
    simp only [map_zero]
    exact (zero_pow (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      W.asIdeal w.ne_bot)).symm
  obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x.toCompletion
  let k := WithVal.equiv (w.valuation K) r
  have hkval : w.valuation K k = Valued.v x := by
    rw [← HeightOneSpectrum.adicCompletion.valued_toCompletion]
    exact hr.symm
  have hk : k ≠ 0 := by
    intro hk
    have : Valued.v x = 0 := by
      rw [← hkval, hk, map_zero]
    apply hx
    simpa using this
  let z := x * (k : w.adicCompletion K)⁻¹
  have hzval : Valued.v z = 1 := by
    simp [z, hkval, hx]
  have hznorm : ‖z‖ = 1 := by
    simp [FinitePlace.norm_def, hzval]
  have hmapznorm :
      ‖finitePlaceExtensionAdicCompletionMap K L w a z‖ = 1 := by
    rw [finitePlaceExtensionAdicCompletionMap_norm, hznorm]
    simp
  let v₀ := Valued.v (finitePlaceExtensionAdicCompletionMap K L w a z)
  have hmapzval :
      v₀ = 1 := by
    rw [FinitePlace.norm_def] at hmapznorm
    exact
      (WithZeroMulInt.toNNReal_eq_one_iff
        (v₀)
        (HeightOneSpectrum.absNorm_ne_zero W)
        (HeightOneSpectrum.one_lt_absNorm_nnreal W).ne').mp
        (NNReal.eq hmapznorm)
  have hkcoe :
      (k : w.adicCompletion K) ≠ 0 := by
    change algebraMap K (w.adicCompletion K) k ≠ 0
    exact (map_ne_zero
      (algebraMap K (w.adicCompletion K))).2 hk
  have hx_factor :
      x = z * (k : w.adicCompletion K) := by
    dsimp [z]
    rw [mul_assoc, inv_mul_cancel₀ hkcoe, mul_one]
  calc
    Valued.v
        (finitePlaceExtensionAdicCompletionMap K L w a x) =
        Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (z * (k : w.adicCompletion K))) := by
          rw [← hx_factor]
    _ = v₀ *
        Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (k : w.adicCompletion K)) := by
          rw [map_mul, map_mul]
    _ = Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (k : w.adicCompletion K)) := by
          rw [hmapzval, one_mul]
    _ = W.valuation L (algebraMap K L k) := by
          rw [finitePlaceExtensionAdicCompletionMap_coe,
            HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    _ = (w.valuation K k) ^
          w.asIdeal.ramificationIdx' W.asIdeal := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal W.asIdeal w.ne_bot]
      exact (HeightOneSpectrum.valuation_liesOver L w W k).symm
    _ = Valued.v x ^
          w.asIdeal.ramificationIdx' W.asIdeal := by
      rw [hkval]

/-- Under the canonical map to a place above `w`, the completed
valuation is raised to the ramification index. -/
theorem finitePlaceAdicCompletionMap_valued
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : w.adicCompletion K) :
    Valued.v (finitePlaceAdicCompletionMap K L w W x) =
      Valued.v x ^ w.asIdeal.ramificationIdx' W.1.asIdeal := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
        w).surjective W
  rw [←
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap]
  exact finitePlaceExtensionAdicCompletionMap_valued K L w a x

end
