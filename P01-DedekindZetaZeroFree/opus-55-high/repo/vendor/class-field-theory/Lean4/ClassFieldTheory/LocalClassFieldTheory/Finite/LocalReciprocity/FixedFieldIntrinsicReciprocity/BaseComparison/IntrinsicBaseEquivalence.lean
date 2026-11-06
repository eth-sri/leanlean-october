module

public import Mathlib.FieldTheory.Galois.Basic
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Intrinsic-to-ambient base equivalences

This module compares the intrinsic absolute Galois base of a finite extension with its realization as a fixing subgroup in an ambient separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The fixing subgroup of the image of a finite extension embedded in
`SeparableClosure K` has finite index in the ambient base-field subgroup. -/
theorem ambientEmbeddedAbsoluteQuotientFinite
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F]
    (i : F →ₐ[K] SeparableClosure K) :
    let H₀ :=
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange i)
    Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let G := Gal(SeparableClosure K / K)
  let Bases := { B : ClosedSubgroup G //
    H₀.toSubgroup ≤ B.toSubgroup }
  let Bfix : Bases :=
    ⟨closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)),
      fixingSubgroupLeBase K (SeparableClosure K)
        (AlgHom.fieldRange i)⟩
  let Bbase : Bases :=
    ⟨baseField G, le_baseField H₀⟩
  let Q : Bases → Type := fun B =>
    B.1.toSubgroup ⧸ extensionSubgroup B.1 H₀ B.2
  have hBase : Bfix = Bbase := by
    apply Subtype.ext
    exact closedFixingSubgroup_bot_eq_baseField
      K (SeparableClosure K)
  let : Finite (Q Bfix) := by
    change Finite
      ((closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K)))
          H₀
          (fixingSubgroupLeBase K (SeparableClosure K)
            (AlgHom.fieldRange i)))
    infer_instance
  change Finite (Q Bbase)
  exact Finite.of_equiv (Q Bfix)
    (Equiv.cast (congrArg Q hBase))

/-- On the intrinsic base, the normalized degree from the local residue datum
agrees with the local residue degree of the underlying automorphism. -/
theorem intrinsicBase_normalizedDegree_eq_localResidueDegree
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (τ : (intrinsicAbstractBase F).toSubgroup) :
    (localResidueDatum F).normalizedDegree
        ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
          (localResidueDatum F)) τ =
      localResidueDegree F τ.1 := by
  apply Multiplicative.ext
  have h :=
    (localResidueDatum F).residueDegree_nsmul_normalizedDegree
      ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)) τ
  rw [show
      (((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)).residueDegree : ℕ) = 1 by
    exact intrinsicFiniteAbstractBase_residueDegree_eq_one F] at h
  simpa [localResidueDatum] using h

/-- A separable-closure equivalence identifies the intrinsic base subgroup of a
finite fixed field with its defining subgroup in the ambient Galois group. -/
def intrinsicBaseEquivAmbientFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃*
        H.field.toSubgroup := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
  let φ :
      Gal(SeparableClosure F / F) ≃*
        H.field.toSubgroup :=
    (AlgEquiv.autCongr e).trans
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).symm
  exact (intrinsicAbstractBaseEquivAbsolute F).trans φ

/-- For an embedded finite separable extension, transport through a
separable-closure equivalence identifies its intrinsic base subgroup with the
ambient subgroup fixing the embedding's field range. -/
def
    intrinsicBaseEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := 
    ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  letI : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  letI : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  letI : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  letI : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  let theta :
      Gal(SeparableClosure F / F) ≃*
        Gal(SeparableClosure F₀ / F₀) := {
    toFun := fun sigma =>
      { c.symm.trans (sigma.toRingEquiv.trans c) with
        commutes' := fun x => by
          change c (sigma (c.symm
            (algebraMap F₀ (SeparableClosure F₀) x))) =
              algebraMap F₀ (SeparableClosure F₀) x
          have hpre :
              c.symm
                  (algebraMap F₀ (SeparableClosure F₀) x) =
                algebraMap F (SeparableClosure F) (phi.symm x) := by
            apply c.injective
            simp_all
          simp_all }
    invFun := fun tau =>
      { c.trans (tau.toRingEquiv.trans c.symm) with
        commutes' := fun x => by
          change c.symm (tau (c
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          rw [hc, tau.commutes]
          apply c.injective
          rw [c.apply_symm_apply, hc] }
    left_inv := fun sigma => by
      apply AlgEquiv.ext
      intro x
      simp
    right_inv := fun tau => by
      apply AlgEquiv.ext
      intro x
      simp
    map_mul' := fun sigma tau => by
      apply AlgEquiv.ext
      intro x
      simp }
  let psi₀ :=
    intrinsicBaseEquivAmbientFixedField K H e₀
  exact
    (intrinsicAbstractBaseEquivAbsolute F).trans
      (theta.trans
        ((intrinsicAbstractBaseEquivAbsolute F₀).symm.trans psi₀))

/-- The intrinsic-to-ambient equivalence is the fixed-field subgroup element
obtained by conjugating the intrinsic automorphism through the chosen
separable-closure equivalence. -/
theorem
    intrinsicBaseEquivAmbientEmbeddedField_apply
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      letI hHabsolute : Finite
          ((baseField
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := 
        ambientEmbeddedAbsoluteQuotientFinite K F i
      let _H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let F₀ :=
        abstractFixedField K (SeparableClosure K) H₀
      let hfixed :
          F₀ = AlgHom.fieldRange i :=
        InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)
      let phi : F ≃+* F₀ :=
        ((i.equivFieldRange).trans
          (IntermediateField.equivOfEq hfixed.symm)).toRingEquiv
      let rho : Gal(SeparableClosure K / F₀) :=
        { e.symm.toRingEquiv.trans
            (tau.1.toRingEquiv.trans e.toRingEquiv) with
          commutes' := fun x => by
            change e (tau.1 (e.symm
              (algebraMap F₀ (SeparableClosure K) x))) =
                algebraMap F₀ (SeparableClosure K) x
            have hpre :
                e.symm
                    (algebraMap F₀ (SeparableClosure K) x) =
                  algebraMap F (SeparableClosure F) (phi.symm x) := by
              apply e.injective
              rw [e.apply_symm_apply, e.commutes]
              change (x : SeparableClosure K) =
                i (phi.symm x)
              rw [← show
                ((phi (phi.symm x) : F₀) :
                    SeparableClosure K) =
                  i (phi.symm x) by rfl,
                phi.apply_symm_apply]
            rw [hpre, tau.1.commutes, e.commutes]
            change i (phi.symm x) = (x : SeparableClosure K)
            rw [← show
              ((phi (phi.symm x) : F₀) :
                  SeparableClosure K) =
                i (phi.symm x) by rfl,
              phi.apply_symm_apply] }
      intrinsicBaseEquivAmbientEmbeddedField K F i e tau =
        (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H₀).symm rho := by
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  dsimp only
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := 
    ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  let : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  let : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  let thetaTau : Gal(SeparableClosure F₀ / F₀) :=
    { c.symm.trans (tau.1.toRingEquiv.trans c) with
      commutes' := fun x => by
        change c (tau.1 (c.symm
          (algebraMap F₀ (SeparableClosure F₀) x))) =
            algebraMap F₀ (SeparableClosure F₀) x
        have hpre :
            c.symm
                (algebraMap F₀ (SeparableClosure F₀) x) =
              algebraMap F (SeparableClosure F) (phi.symm x) := by
          apply c.injective
          simp_all
        simp_all }
  let rho : Gal(SeparableClosure K / F₀) :=
    { e.symm.toRingEquiv.trans
        (tau.1.toRingEquiv.trans e.toRingEquiv) with
      commutes' := fun x => by
        change e (tau.1 (e.symm
          (algebraMap F₀ (SeparableClosure K) x))) =
            algebraMap F₀ (SeparableClosure K) x
        have hpre :
            e.symm
                (algebraMap F₀ (SeparableClosure K) x) =
              algebraMap F (SeparableClosure F) (phi.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, e.commutes]
          change (x : SeparableClosure K) =
            i (phi.symm x)
          rw [← show
            ((phi (phi.symm x) : F₀) :
                SeparableClosure K) =
              i (phi.symm x) by rfl,
            phi.apply_symm_apply]
        rw [hpre, tau.1.commutes, e.commutes]
        change i (phi.symm x) = (x : SeparableClosure K)
        rw [← show
          ((phi (phi.symm x) : F₀) :
              SeparableClosure K) =
            i (phi.symm x) by rfl,
          phi.apply_symm_apply] }
  have hrho :
      AlgEquiv.autCongr e₀ thetaTau = rho := by
    apply AlgEquiv.ext
    intro x
    simp only [AlgEquiv.autCongr_apply]
    change
      e₀
          (c (tau.1 (c.symm (e₀.symm x)))) =
        e (tau.1 (e.symm x))
    rw [show c.symm (e₀.symm x) = e.symm x by
      simp [c]]
    change e₀ (e₀.symm (e (tau.1 (e.symm x)))) =
      e (tau.1 (e.symm x))
    simp
  change
    intrinsicBaseEquivAmbientFixedField K H e₀
        ⟨thetaTau, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          trivial⟩ =
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H₀).symm rho
  change
    (abstractSubgroupEquivGaloisGroup
      K (SeparableClosure K) H₀).symm
        (AlgEquiv.autCongr e₀ thetaTau) =
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H₀).symm rho
  rw [hrho]

/-- The embedded-field base equivalence acts on the ambient separable closure
by conjugating the intrinsic automorphism through the chosen equivalence. -/
theorem
    intrinsicBaseEquivAmbientEmbeddedField_apply_val
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup)
      (x : SeparableClosure K),
      (intrinsicBaseEquivAmbientEmbeddedField
        K F i e tau).1.1 x =
        e (tau.1 (e.symm x)) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau x
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := 
    ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phi : F ≃+* F₀ :=
    ((i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)).toRingEquiv
  let rho : Gal(SeparableClosure K / F₀) :=
    { e.symm.toRingEquiv.trans
        (tau.1.toRingEquiv.trans e.toRingEquiv) with
      commutes' := fun y => by
        change e (tau.1 (e.symm
          (algebraMap F₀ (SeparableClosure K) y))) =
            algebraMap F₀ (SeparableClosure K) y
        have hpre :
            e.symm
                (algebraMap F₀ (SeparableClosure K) y) =
              algebraMap F (SeparableClosure F) (phi.symm y) := by
          apply e.injective
          rw [e.apply_symm_apply, e.commutes]
          change (y : SeparableClosure K) =
            i (phi.symm y)
          rw [← show
            ((phi (phi.symm y) : F₀) :
                SeparableClosure K) =
              i (phi.symm y) by rfl,
            phi.apply_symm_apply]
        rw [hpre, tau.1.commutes, e.commutes]
        change i (phi.symm y) = (y : SeparableClosure K)
        rw [← show
          ((phi (phi.symm y) : F₀) :
              SeparableClosure K) =
            i (phi.symm y) by rfl,
          phi.apply_symm_apply] }
  have happly :=
    intrinsicBaseEquivAmbientEmbeddedField_apply
      K F i e tau
  dsimp only at happly
  rw [happly]
  rfl

/-- The embedded-field base equivalence preserves normalized degree between
the intrinsic local residue datum and the ambient finite abstract field. -/
theorem
    intrinsicBase_normalizedDegree_eq_ambientEmbeddedField
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      letI hHabsolute : Finite
          ((baseField
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := 
        ambientEmbeddedAbsoluteQuotientFinite K F i
      let H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      (localResidueDatum F).normalizedDegree
          ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
            (localResidueDatum F)) tau =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          (intrinsicBaseEquivAmbientEmbeddedField K F i e tau) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  dsimp only
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := 
    ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  rw [intrinsicBase_normalizedDegree_eq_localResidueDegree F tau]
  have hdegree :=
    localResidueDegree_eq_normalizedDegree_finiteExtensionEquiv
      K F i e tau.1
  have hpsi :=
    intrinsicBaseEquivAmbientEmbeddedField_apply
      K F i e tau
  simp_all
