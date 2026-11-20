module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceLocalGlobal
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Finite-place Kummer root-character comparison

The comparison is compiled through an S-valued map from the chosen global
Kummer extension to the Kummer extension chosen over the completion.  The
localized completion and its instance tower occur only in the provider body
which proves compatibility with the two Artin actions.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

private theorem nthRootsSubgroupMap_comp_eq_unitsMap
    {F C L S : Type} [Field F] [Field C] [Field L] [Field S]
    [Algebra F C] [Algebra F L] [Algebra C S]
    (m : ℕ) (x : nthRootsSubgroup F m) (f : L →+* S)
    (hmap : ∀ y : F,
      algebraMap C S (algebraMap F C y) = f (algebraMap F L y)) :
    (nthRootsSubgroupMap C S m
        (nthRootsSubgroupMap F C m x)).1 =
      Units.map f.toMonoidHom
        (Units.map (algebraMap F L).toMonoidHom x.1) := by
  apply Units.ext
  exact hmap (x.1 : F)

private theorem rootQuotient_map_ringHom_of_action
    {F G L S : Type} [Field F] [Field G] [Field L] [Field S]
    [Algebra F L] [Algebra G S]
    (f : L →+* S) (u : Lˣ) (sigmaL : Gal(L/F)) (sigmaS : Gal(S/G))
    (haction : sigmaS (f (u : L)) = f (sigmaL (u : L))) :
    Units.map f.toMonoidHom
        (rootQuotient (K := F) (L := L) u sigmaL) =
      rootQuotient (K := G) (L := S)
        (Units.map f.toMonoidHom u) sigmaS := by
  apply Units.ext
  simp only [rootQuotient, Units.val_div_eq_div_val, Units.coe_map]
  change f (sigmaL (u : L) / (u : L)) =
    sigmaS (f (u : L)) / f (u : L)
  rw [map_div₀, haction]

/-- The normalized finite-place Artin action commutes with algebraic
localization.  This generic boundary is compiled before the Kummer-specific
comparison, so the latter never re-elaborates the localization tower. -/
private theorem finitePlaceArtin_apply_localized
    {L : Type} [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) (z : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (@abelianLocalArtinMonoidHom vK.Completion E
      (inferInstance : Field vK.Completion) (inferInstance : Field E)
      (finitePlaceLocalArtinLocalizedAlgebra v w)
      (finitePlaceLocalArtinCompletionValuativeRel v)
      (inferInstance : TopologicalSpace vK.Completion)
      (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
      (finitePlaceLocalArtinFiniteDimensional v w)
      (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
      (finitePlaceLocalArtinInput v x))
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 z) =
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
        ((finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v w x) z) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let sigmaE := @abelianLocalArtinMonoidHom vK.Completion E
    inferInstance inferInstance
    (finitePlaceLocalArtinLocalizedAlgebra v w)
    (finitePlaceLocalArtinCompletionValuativeRel v)
    inferInstance
    (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
    (finitePlaceLocalArtinFiniteDimensional v w)
    (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
    (finitePlaceLocalArtinInput v x)
  let sigmaG := finitePlaceArtinMonoidHomOfExtension
      v w x
  have hfactor :=
    finitePlaceArtinMonoidHomOfExtension_apply_normalized
        v w x
  let hvK := RayClass.adicAbv_isNontrivial v
  let eD :=
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let delta := eD.symm sigmaE
  have hdelta := eD.apply_symm_apply sigmaE
  change sigmaE (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 z) =
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (sigmaG z)
  dsimp only [sigmaG]
  rw [hfactor]
  rw [← hdelta]
  exact localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    vK hvK w delta z

 section

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))

noncomputable def finitePlaceKummerGlobalArtinAutomorphism (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    Gal((chosenSimpleKummerExtension K n hnK b)/K) := by
  let L := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  exact finitePlaceArtinMonoidHomOfExtension
      v w (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)

 noncomputable def finitePlaceKummerLocalArtinAutomorphism (a b : Kˣ) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    Gal(S/C) := by
  let C := finitePlaceKummerBaseCompletion K v
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
      C n (finitePlaceHilbert_natCast_ne_zero K n hnK v) (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v) (finitePlaceHilbert_completionUnit K v b) (finitePlaceHilbert_completionUnit K v a)

/-- The canonical map from the chosen global Kummer extension to the
intrinsic Kummer extension over the finite-place completion. -/
 noncomputable def finitePlaceKummerGlobalToLocalRingHom (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    chosenSimpleKummerExtension K n hnK b →+*
      finitePlaceKummerLocalExtension K n hnK v b := by
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  letI : Algebra (finitePlaceKummerBaseCompletion K v) E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  exact (finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w).symm.toRingHom.comp (AbsoluteValue.toAlgebraicLocalization (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2)

/-- The global-to-local Kummer map extends the canonical scalar map from
the number field through its finite-place completion. -/
private theorem finitePlaceKummerGlobalToLocalRingHom_commutes (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b))
    (y : K) :
    let C := finitePlaceKummerBaseCompletion K v
    let L := chosenSimpleKummerExtension K n hnK b
    let S := finitePlaceKummerLocalExtension K n hnK v b
    algebraMap C S (algebraMap K C y) =
      finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
        (algebraMap K L y) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  apply e.injective
  calc
    _ =
        algebraMap C E (algebraMap K C y) := e.commutes _
    _ = toE (algebraMap K L y) :=
      (AbsoluteValue.toAlgebraicLocalization_algebraMap
        vK w.1 w.2 y).symm
    _ = e (e.symm (toE (algebraMap K L y))) :=
      (e.apply_symm_apply _).symm

 noncomputable def
    finitePlaceKummerTransportedLocalizedArtinAutomorphism (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    Gal(S/C) := by
  let C := finitePlaceKummerBaseCompletion K v
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  letI : FiniteDimensional K
      (chosenSimpleKummerExtension K n hnK b) :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K
      (chosenSimpleKummerExtension K n hnK b) :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  letI : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  letI : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
        v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  exact (AlgEquiv.autCongr (finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w)).symm (abelianLocalArtinMonoidHom C E (finitePlaceHilbert_completionUnit K v a))

private theorem finitePlaceKummerLocalArtin_eq_transported (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerLocalArtinAutomorphism
        K n hnK hmu v a b =
      finitePlaceKummerTransportedLocalizedArtinAutomorphism
        K n hnK hmu v a b w := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let aC := finitePlaceHilbert_completionUnit K v a
  let :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let :=
    finitePlaceKummerLocalFiniteDimensional K n hnK v b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois C n (finitePlaceHilbert_natCast_ne_zero K n hnK v) (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v) (finitePlaceHilbert_completionUnit K v b)
  let :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let :=
    finitePlaceLocalArtinIsAbelianGalois
        v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let sigmaS := abelianLocalArtinMonoidHom C S aC
  let sigmaE := abelianLocalArtinMonoidHom C E aC
  let tauS := (AlgEquiv.autCongr e).symm sigmaE
  have hArtinEquiv :
      (AlgEquiv.autCongr e).toMonoidHom sigmaS = sigmaE := by
    simpa using (DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_autCongr
        C S E e) aC)
  have hsigma : sigmaS = tauS := by
    apply (AlgEquiv.autCongr e).injective
    calc
      _ = sigmaE := hArtinEquiv
      _ = (AlgEquiv.autCongr e) tauS := ((AlgEquiv.autCongr e).apply_symm_apply sigmaE).symm
  exact hsigma

end

 noncomputable def localizedDirectActionValue
    {L : Type} [Field L] [Algebra K L]
    [hfin : FiniteDimensional K L] [hab : IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (y : (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ)
    (t : AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w) :
    AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w := by
  let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (NumberField.HeightOneSpectrum.adicAbv K v) w
  let _ := finitePlaceLocalArtinCompletionValuativeRel v
  let _ :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let _ := finitePlaceLocalArtinLocalizedAlgebra v w
  let _ := finitePlaceLocalArtinFiniteDimensional v w
  let _ : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois v w hfin
  exact abelianLocalArtinMonoidHom C E y t

 section

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv K v) (chosenSimpleKummerExtension K n hnK b))

noncomputable def finitePlaceKummerCommonRootAction :
    finitePlaceKummerLocalExtension K n hnK v b := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  letI : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Algebra C E :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  letI : FiniteDimensional C E :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  letI : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
        v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  exact (finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w).symm (localizedDirectActionValue K v w (finitePlaceHilbert_completionUnit K v a) ((AbsoluteValue.toAlgebraicLocalization (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2) ((chosenSimpleKummerRootUnit K n hnK b) : L)))

private theorem finitePlaceKummerTransportedArtinRoot_eq_common :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerTransportedLocalizedArtinAutomorphism
        K n hnK hmu v a b w (f uL) =
      finitePlaceKummerCommonRootAction
        K n hnK hmu v a b w := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let aC := finitePlaceHilbert_completionUnit K v a
  let :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let :=
    finitePlaceLocalArtinIsAbelianGalois
        v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
  let f := e.symm.toRingHom.comp toE
  let uL := chosenSimpleKummerRootUnit K n hnK b
  let sigmaE := abelianLocalArtinMonoidHom C E aC
  let directE := localizedDirectActionValue K v w aC (toE (uL : L))
  let tauS := (AlgEquiv.autCongr e).symm sigmaE
  have hlocalNaturality (y : S) :
      e (tauS y) = sigmaE (e y) := by
    calc
      _ =
          ((AlgEquiv.autCongr e).toMonoidHom tauS) (e y) := by
        exact
          (congrArg (fun t : S => e (tauS t))
            (e.symm_apply_apply y)).symm
      _ = sigmaE (e y) :=
        congrArg (fun tau : Gal(E/C) => tau (e y)) ((AlgEquiv.autCongr e).apply_symm_apply sigmaE)
  apply e.injective
  calc
    _ = sigmaE (e (f (uL : L))) :=
      hlocalNaturality (f (uL : L))
    _ = sigmaE (toE (uL : L)) :=
      congrArg (fun t : E => sigmaE t) (by
        exact e.apply_symm_apply _)
    _ = directE := rfl.symm
    _ = e (e.symm directE) := (e.apply_symm_apply _).symm

end

 section

variable {L : Type} [Field L] [Algebra K L] [hfin : FiniteDimensional K L] [hab : IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) (z : L)

noncomputable def localizedInputActionValue :
    AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w :=
  localizedDirectActionValue K v w (finitePlaceLocalArtinInput v x)
    (AbsoluteValue.toAlgebraicLocalization
      (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2 z)

 noncomputable def localizedGlobalActionValue :
    AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w :=
  AbsoluteValue.toAlgebraicLocalization
    (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
    (finitePlaceArtinMonoidHomOfExtension
      (K := K) (L := L) v w x z)

private theorem localizedActionValue_eq :
    localizedInputActionValue K v w x z =
      localizedGlobalActionValue K v w x z := by apply @finitePlaceArtin_apply_localized <;> assumption

end

 section

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv K v) (chosenSimpleKummerExtension K n hnK b))

noncomputable def finitePlaceKummerLocalizedInputValue :
    finitePlaceKummerLocalizedCompletion K n hnK v b w :=
  localizedInputActionValue (K := K)
    (hfin := chosenSimpleKummerExtension_finiteDimensional K n hnK b)
    (hab := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b)
    v w
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (chosenSimpleKummerRootUnit K n hnK b :
      chosenSimpleKummerExtension K n hnK b)

 noncomputable def finitePlaceKummerLocalizedGlobalValue :
    finitePlaceKummerLocalizedCompletion K n hnK v b w :=
  localizedGlobalActionValue (K := K)
    (hfin := chosenSimpleKummerExtension_finiteDimensional K n hnK b)
    (hab := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b)
    v w
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (chosenSimpleKummerRootUnit K n hnK b :
      chosenSimpleKummerExtension K n hnK b)

private theorem finitePlaceKummerLocalizedValue_eq :
    finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w =
      finitePlaceKummerLocalizedGlobalValue K n hnK hmu v a b w := localizedActionValue_eq
    (K := K) (L := chosenSimpleKummerExtension K n hnK b)
    (hfin := chosenSimpleKummerExtension_finiteDimensional K n hnK b)
    (hab := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b)
    v w
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (chosenSimpleKummerRootUnit K n hnK b :
      chosenSimpleKummerExtension K n hnK b)

private theorem finitePlaceKummerCommonImage_eq_localizedInputValue :
    finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
        (finitePlaceKummerCommonRootAction K n hnK hmu v a b w) =
      finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w := by
  let L := chosenSimpleKummerExtension K n hnK b
  let C := finitePlaceKummerBaseCompletion K v
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let _ :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let _ :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let _ := finitePlaceLocalArtinCompletionValuativeRel v
  let _ :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let _ := finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let _ :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let _ :=
    finitePlaceLocalArtinIsAbelianGalois
        v w
        (chosenSimpleKummerExtension_finiteDimensional K n hnK b)
  let x :=
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  let aC := finitePlaceHilbert_completionUnit K v a
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let directFor (y : Cˣ) : E :=
    localizedDirectActionValue K v w y ((AbsoluteValue.toAlgebraicLocalization (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2) (chosenSimpleKummerRootUnit K n hnK b))
  calc
    _ =
        directFor aC := by
      exact e.apply_symm_apply _
    _ = directFor (finitePlaceLocalArtinInput v x) :=
      congrArg directFor (finitePlaceLocalArtinInput_globalUnit K v a).symm
    _ = finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w := by
      unfold finitePlaceKummerLocalizedInputValue localizedInputActionValue
      rfl

private theorem finitePlaceKummerGlobalArtin_localized_action :
    finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
        (finitePlaceKummerCommonRootAction K n hnK hmu v a b w) =
      AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
        (finitePlaceKummerGlobalArtinAutomorphism
          K n hnK hmu v a b w
          (chosenSimpleKummerRootUnit K n hnK b)) := by
  calc
    _ =
        finitePlaceKummerLocalizedInputValue K n hnK hmu v a b w :=
      finitePlaceKummerCommonImage_eq_localizedInputValue
        K n hnK hmu v a b w
    _ = finitePlaceKummerLocalizedGlobalValue K n hnK hmu v a b w :=
      finitePlaceKummerLocalizedValue_eq K n hnK hmu v a b w
    _ = AbsoluteValue.toAlgebraicLocalization
        (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
        (finitePlaceKummerGlobalArtinAutomorphism
          K n hnK hmu v a b w
          (chosenSimpleKummerRootUnit K n hnK b)) := rfl

private theorem finitePlaceKummerCommonRootAction_eq_global :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerCommonRootAction
        K n hnK hmu v a b w =
      f (finitePlaceKummerGlobalArtinAutomorphism
        K n hnK hmu v a b w uL) := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let E := finitePlaceKummerLocalizedCompletion K n hnK v b w
  let x :=
    Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a
  let hKLfinite :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let hKLgalois :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let :=
    finitePlaceKummerLocalizedAlgebra K n hnK v b w
  let :=
    finitePlaceKummerLocalizedFiniteDimensional K n hnK v b w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois
      (K := K) (L := L) v w hKLfinite
  let e := finitePlaceKummerLocalGlobalAlgEquiv K n hnK hmu v b w
  let toE :=
    AbsoluteValue.toAlgebraicLocalization (NumberField.HeightOneSpectrum.adicAbv K v) w.1 w.2
  let f := e.symm.toRingHom.comp toE
  let uL := chosenSimpleKummerRootUnit K n hnK b
  let sigmaG : Gal(L/K) :=
    finitePlaceArtinMonoidHomOfExtension
      (K := K) (L := L) v w x
  have himage := finitePlaceKummerGlobalArtin_localized_action
    K n hnK hmu v a b w
  apply e.injective
  calc
    e (finitePlaceKummerCommonRootAction
        K n hnK hmu v a b w) =
        toE (sigmaG (uL : L)) := himage
    _ = e (f (sigmaG (uL : L))) := by
      exact (e.apply_symm_apply _).symm

end

/-- The global-to-local Kummer map intertwines the two Artin actions on the
chosen Kummer root. -/
private theorem finitePlaceKummerGlobalToLocalRingHom_artin_action
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    finitePlaceKummerLocalArtinAutomorphism
        K n hnK hmu v a b (f uL) =
      f (finitePlaceKummerGlobalArtinAutomorphism
        K n hnK hmu v a b w uL) := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let f :=
    finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
  let uL := chosenSimpleKummerRootUnit K n hnK b
  calc
    _ = (finitePlaceKummerTransportedLocalizedArtinAutomorphism
      K n hnK hmu v a b w) (f (uL : L)) :=
      congrArg (fun tau : Gal(S/C) => tau (f (uL : L)))
        (finitePlaceKummerLocalArtin_eq_transported
          K n hnK hmu v a b w)
    _ = f ((finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w) (uL : L)) :=
      ((finitePlaceKummerTransportedArtinRoot_eq_common
    K n hnK hmu v a b w).trans
      (finitePlaceKummerCommonRootAction_eq_global
        K n hnK hmu v a b w))

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : HeightOneSpectrum (𝓞 K))

/-- The image of the chosen global Kummer root has the same prescribed
power as the root chosen intrinsically over the completion. -/
private theorem finitePlaceKummerGlobalToLocalRingHom_root_pow (b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    let bC := finitePlaceHilbert_completionUnit K v b
    Units.map f.toMonoidHom uL ^ (n : ℕ) =
      Units.map (algebraMap C S).toMonoidHom bC := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let f := finitePlaceKummerGlobalToLocalRingHom
    K n hnK hmu v b w
  let uL := chosenSimpleKummerRootUnit K n hnK b
  calc
    _ =
        Units.map f.toMonoidHom (uL ^ (n : ℕ)) :=
      (map_pow (Units.map f.toMonoidHom) uL (n : ℕ)).symm
    _ = Units.map f.toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom b) := by rw [(chosenSimpleKummerRootUnit_pow K n hnK b)]
    _ = Units.map (algebraMap C S).toMonoidHom (finitePlaceHilbert_completionUnit K v b) := by
      apply Units.ext
      exact
        (finitePlaceKummerGlobalToLocalRingHom_commutes
          K n hnK hmu v b w (b : K)).symm

private theorem finitePlaceKummerMappedGlobalCharacter_units (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let L := chosenSimpleKummerExtension K n hnK b
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    let sigmaG := finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
    let globalValue :=
      finitePlaceKummerRootCharacterOfExtension
        K n hnK hmu v a b w
    Units.map f.toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom globalValue.1) =
      Units.map f.toMonoidHom
        (rootQuotient (K := K) (L := L) uL sigmaG) := by
  let L := chosenSimpleKummerExtension K n hnK b
  let sigmaG :=
    finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
  let globalValue :=
    finitePlaceKummerRootCharacterOfExtension
      K n hnK hmu v a b w
  have hglobalMap :
      nthRootsSubgroupMap K L (n : ℕ) globalValue =
        chosenSimpleKummerRootCharacter K n hnK hmu b sigmaG := by
    unfold globalValue sigmaG
    unfold finitePlaceKummerRootCharacterOfExtension
      finitePlaceKummerGlobalArtinAutomorphism
    exact
      (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).apply_symm_apply _
  refine congrArg (Units.map (finitePlaceKummerGlobalToLocalRingHom
    K n hnK hmu v b w).toMonoidHom) ?_
  have h := congrArg Subtype.val hglobalMap
  rw [chosenSimpleKummerRootCharacter_apply] at h
  exact h

private theorem finitePlaceKummerRootQuotient_eq_local (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    let C := finitePlaceKummerBaseCompletion K v
    let L := chosenSimpleKummerExtension K n hnK b
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let f := finitePlaceKummerGlobalToLocalRingHom
      K n hnK hmu v b w
    let uL := chosenSimpleKummerRootUnit K n hnK b
    let uS := chosenSimpleKummerRootUnit C
      n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
        (finitePlaceHilbert_completionUnit K v b)
    let sigmaG := finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
    let sigmaS := finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
    Units.map f.toMonoidHom
        (rootQuotient (K := K) (L := L) uL sigmaG) =
      rootQuotient (K := C) (L := S) uS sigmaS := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let bC := finitePlaceHilbert_completionUnit K v b
  let f :=
    finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
  let uL := chosenSimpleKummerRootUnit K n hnK b
  let uS := chosenSimpleKummerRootUnit C n hnC bC
  let sigmaG :=
    finitePlaceKummerGlobalArtinAutomorphism
      K n hnK hmu v a b w
  let sigmaS :=
    finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
  exact (rootQuotient_map_ringHom_of_action
    f uL sigmaG sigmaS (finitePlaceKummerGlobalToLocalRingHom_artin_action
      K n hnK hmu v a b w)).trans (rootQuotient_eq_of_same_pow_of_primitiveRoots
    C n (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v) bC (Units.map f.toMonoidHom uL) uS
      (finitePlaceKummerGlobalToLocalRingHom_root_pow
        K n hnK hmu v b w) (chosenSimpleKummerRootUnit_pow C n hnC bC) sigmaS)

private theorem finitePlaceKummerLocalHilbert_units (a b : Kˣ) :
    let C := finitePlaceKummerBaseCompletion K v
    let S := finitePlaceKummerLocalExtension K n hnK v b
    let uS := chosenSimpleKummerRootUnit C
      n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
        (finitePlaceHilbert_completionUnit K v b)
    let sigmaS := finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
    Units.map (algebraMap C S).toMonoidHom
        (finitePlaceLocalHilbertSymbol K n hnK hmu v a b).1 =
      rootQuotient (K := C) (L := S) uS sigmaS := by
  let C := finitePlaceKummerBaseCompletion K v
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let hnC := finitePlaceHilbert_natCast_ne_zero K n hnK v
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu v
  let aC := finitePlaceHilbert_completionUnit K v a
  let bC := finitePlaceHilbert_completionUnit K v b
  let :=
    finitePlaceLocalArtinCompletionValuativeRel v
  let :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let :=
    finitePlaceKummerLocalFiniteDimensional K n hnK v b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois C n hnC hmuC bC
  let uS := chosenSimpleKummerRootUnit C n hnC bC
  let sigmaS :=
    finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b
  let localValue :=
    LocalClassFieldTheory.Kummer.localHilbertSymbol
      C n hnC hmuC aC bC
  have hroot :
      Units.map (algebraMap C S).toMonoidHom localValue.1 =
        rootQuotient uS sigmaS := by
    have h := congrArg Subtype.val (LocalClassFieldTheory.Kummer.localHilbertSymbol_map_eq_rootQuotient
      C n hnC hmuC aC bC)
    change
      Units.map (algebraMap C S).toMonoidHom localValue.1 =
        rootQuotient uS sigmaS at h
    exact h
  have hvalue :
      finitePlaceLocalHilbertSymbol K n hnK hmu v a b = localValue := by
    unfold finitePlaceLocalHilbertSymbol localValue
    rfl
  rw [hvalue]
  exact hroot

/-- For every extension of a finite place, the global Kummer root character
equals the finite-place Hilbert symbol. -/
theorem finitePlaceKummerRootCharacterOfExtension_localGlobal (a b : Kˣ)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (chosenSimpleKummerExtension K n hnK b)) :
    finitePlaceKummerRootCharacterOfExtension
        K n hnK hmu v a b w =
      finitePlaceHilbertSymbol K n hnK hmu v a b := by
  let C := finitePlaceKummerBaseCompletion K v
  let L := chosenSimpleKummerExtension K n hnK b
  let S := finitePlaceKummerLocalExtension K n hnK v b
  let f :=
    finitePlaceKummerGlobalToLocalRingHom K n hnK hmu v b w
  let globalValue :=
    finitePlaceKummerRootCharacterOfExtension K n hnK hmu v a b w
  let localValue :=
    finitePlaceLocalHilbertSymbol K n hnK hmu v a b
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  apply nthRootsSubgroupMap_injective C S (n : ℕ)
  apply Subtype.ext
  change
    (nthRootsSubgroupMap C S (n : ℕ)
      (nthRootsSubgroupMap K C (n : ℕ) globalValue)).1 =
        (nthRootsSubgroupMap C S (n : ℕ) localValue).1
  calc
    _ =
      Units.map f.toMonoidHom
        (Units.map (algebraMap K L).toMonoidHom globalValue.1) :=
      nthRootsSubgroupMap_comp_eq_unitsMap
        (n : ℕ) globalValue f
          (finitePlaceKummerGlobalToLocalRingHom_commutes
            K n hnK hmu v b w)
    _ = Units.map f.toMonoidHom
        (rootQuotient (chosenSimpleKummerRootUnit K n hnK b) (finitePlaceKummerGlobalArtinAutomorphism
          K n hnK hmu v a b w)) :=
      finitePlaceKummerMappedGlobalCharacter_units
        K n hnK hmu v a b w
    _ = rootQuotient (chosenSimpleKummerRootUnit C
      n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
        (finitePlaceHilbert_completionUnit K v b)) (finitePlaceKummerLocalArtinAutomorphism
      K n hnK hmu v a b) :=
      finitePlaceKummerRootQuotient_eq_local
        K n hnK hmu v a b w
    _ = Units.map (algebraMap C S).toMonoidHom localValue.1 :=
      (finitePlaceKummerLocalHilbert_units
        K n hnK hmu v a b).symm
    _ = (nthRootsSubgroupMap C S (n : ℕ) localValue).1 := rfl

/-- The canonical finite-place Kummer root character is the finite-place
Hilbert symbol. -/
theorem finitePlaceKummerRootCharacter_localGlobal (a b : Kˣ) :
    finitePlaceKummerRootCharacter K n hnK hmu v a b =
      finitePlaceHilbertSymbol K n hnK hmu v a b := by
  let L := chosenSimpleKummerExtension K n hnK b
  let :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let w := chosenFinitePlaceExtension (L := L) v
  calc
    _ =
        finitePlaceKummerRootCharacterOfExtension
          K n hnK hmu v a b w :=
      (finitePlaceKummerRootCharacterOfExtension_eq
        K n hnK hmu v a b w).symm
    _ = finitePlaceHilbertSymbol K n hnK hmu v a b :=
      finitePlaceKummerRootCharacterOfExtension_localGlobal
        K n hnK hmu v a b w

end Reciprocity
end GlobalClassFieldTheory

end
