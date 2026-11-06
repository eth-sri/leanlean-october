module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.AbsoluteRamification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false
/-! Provides the public declarations in the `RamificationTheory.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence` Lean module. -/

namespace RamificationTheory

open ValuationTheory

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory































section
variable {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B)
include F A B e in
private theorem finiteDimensional_comap_algEquiv
      (E : IntermediateField F B)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.comap e.toAlgHom) := by
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  let eLin : Ecomap ≃ₗ[F] E :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e (e.symm x.1) ∈ E
        rw [e.apply_symm_apply]
        exact x.2⟩
      left_inv := by
        intro x
        ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact e.apply_symm_apply x.1
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  exact Module.Finite.equiv eLin.symm
































/-- Pull back an intermediate field along a ring equivalence which is
semilinear over a base-field equivalence.  This is the finite-level source
needed for Krull-continuity of conjugation by such a semilinear equivalence. -/
def semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') : IntermediateField F Ω where
  carrier := {x : Ω | e x ∈ E}
  zero_mem' := by
    simp
  one_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    simpa using E.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using E.mul_mem hx hy
  inv_mem' := by
    intro x hx
    simpa using E.inv_mem hx
  algebraMap_mem' := by
    intro x
    change e (algebraMap F Ω x) ∈ E
    rw [he x]
    exact E.algebraMap_mem (τ x)














/-- States the theorem `semilinearRingEquivPreimageIntermediateField_symm_mem`. -/
theorem semilinearRingEquivPreimageIntermediateField_symm_mem
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') {x : Ω'} (hx : x ∈ E) :
    e.symm x ∈ semilinearRingEquivPreimageIntermediateField τ e he E := by
  change e (e.symm x) ∈ E
  simpa using hx

/-- The semilinear pullback of a finite intermediate field is finite. -/
theorem finiteDimensional_semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') [FiniteDimensional F' E] :
    FiniteDimensional F
      (semilinearRingEquivPreimageIntermediateField τ e he E) := by
  let T := semilinearRingEquivPreimageIntermediateField τ e he E
  let f : E →ₛₗ[(τ.symm : F' →+* F)] T :=
    { toFun := fun x =>
        ⟨e.symm x.1,
          semilinearRingEquivPreimageIntermediateField_symm_mem
            τ e he E x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp only [Algebra.smul_def]
        change e.symm (algebraMap F' Ω' a * x.1) =
          algebraMap F Ω (τ.symm a) * e.symm x.1
        have hbase :
            e (algebraMap F Ω (τ.symm a)) =
              algebraMap F' Ω' a := by
          simpa using he (τ.symm a)
        apply e.injective
        calc
          e (e.symm (algebraMap F' Ω' a * x.1)) =
              algebraMap F' Ω' a * x.1 := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a)) * x.1 := by
                rw [hbase]
          _ = e (algebraMap F Ω (τ.symm a)) * e (e.symm x.1) := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a) * e.symm x.1) := by
                rw [map_mul] }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨e y.1, y.2⟩, ?_⟩
    ext
    exact e.symm_apply_apply y.1
  have hfgImage : Submodule.FG ((⊤ : Submodule F' E).map f) :=
    (Module.Finite.fg_top (R := F') (M := E)).map f
  have hmaptop : (⊤ : Submodule F' E).map f =
      (⊤ : Submodule F T) := by
    rw [Submodule.map_top, LinearMap.range_eq_top_of_surjective f hsurj]
  change Module.Finite F T
  exact Module.Finite.of_fg_top (by simpa [hmaptop] using hfgImage)

/-- Conjugation by a semilinear equivalence of an algebraic closure is
continuous for the Krull topology.  The semilinear base action is recorded
explicitly by `he`, and the group homomorphism is required only to have the
corresponding conjugation formula on underlying ring equivalences. -/
theorem semilinear_conjugation_continuous
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (φ : Gal(Ω / F) →* Gal(Ω' / F'))
    (hφ : ∀ g : Gal(Ω / F),
      (φ g).toRingEquiv =
        e.symm.trans (g.toRingEquiv.trans e)) :
    Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F' Ω' s).1 hs with
    ⟨E, hE, hEs⟩
  let Epre : IntermediateField F Ω :=
    semilinearRingEquivPreimageIntermediateField τ e he E
  have : FiniteDimensional F' E := hE
  have : FiniteDimensional F Epre :=
    finiteDimensional_semilinearRingEquivPreimageIntermediateField
      τ e he E
  refine (krullTopology_mem_nhds_one_iff F Ω (φ ⁻¹' s)).2 ?_
  refine ⟨Epre, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change φ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hxpre : e.symm x ∈ Epre :=
    semilinearRingEquivPreimageIntermediateField_symm_mem
      τ e he E hx
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff Epre σ).1 hσ
      (e.symm x) hxpre
  change (φ σ).toRingEquiv x = x
  rw [hφ σ]
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

include F A B e in
/-- Algebra-equivalence conjugation is continuous for Krull topologies. -/
theorem algEquiv_autCongr_continuous
      :
    Continuous (AlgEquiv.autCongr e : Gal(A / F) → Gal(B / F)) := by
  refine continuous_of_continuousAt_one (AlgEquiv.autCongr e).toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F B s).1 hs with
    ⟨E, hE, hEs⟩
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  have : FiniteDimensional F E := hE
  have : FiniteDimensional F Ecomap :=
    finiteDimensional_comap_algEquiv e E
  refine (krullTopology_mem_nhds_one_iff F A
    ((AlgEquiv.autCongr e) ⁻¹' s)).2 ?_
  refine ⟨Ecomap, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change AlgEquiv.autCongr e σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change e (σ (e.symm x)) = x
  have hxEcomap : e.symm x ∈ Ecomap := by
    change e (e.symm x) ∈ E
    rw [e.apply_symm_apply]
    exact hx
  have hfix := (IntermediateField.mem_fixingSubgroup_iff Ecomap σ).1 hσ
    (e.symm x) hxEcomap
  rw [hfix]
  exact e.apply_symm_apply x

include F A B e in
/-- The inverse of algebra-equivalence conjugation is continuous for Krull
topologies. -/
theorem algEquiv_autCongr_symm_continuous
      :
    Continuous ((AlgEquiv.autCongr e).symm : Gal(B / F) → Gal(A / F)) := by
  rw [AlgEquiv.autCongr_symm]
  exact algEquiv_autCongr_continuous e.symm
end


section
variable (K : Type u) [Field K]
    (τ : Gal(SeparableClosure K / K))
include K τ in
/-- Extend a `K`-automorphism of the absolute separable closure to the fixed
chosen algebraic closure.  The extension is canonical because
`AlgebraicClosure K` is purely inseparable over `SeparableClosure K`. -/
noncomputable def separableClosureExtensionAlgEquiv
      :
    Gal(AlgebraicClosure K / K) := by
  letI : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  haveI : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  haveI : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  haveI : IsAlgClosure (SeparableClosure K) (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance
      isAlgebraic := inferInstance }
  let eRing : SeparableClosure K ≃+* SeparableClosure K := τ.toRingEquiv
  let e0 : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) eRing
  refine
    { e0 with
      commutes' := ?_ }
  intro x
  calc
    e0 (algebraMap K (AlgebraicClosure K) x) =
        algebraMap (SeparableClosure K) (AlgebraicClosure K)
          (eRing (algebraMap K (SeparableClosure K) x)) := by
      change
        IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
            eRing (algebraMap K (AlgebraicClosure K) x) =
          algebraMap (SeparableClosure K) (AlgebraicClosure K)
            (eRing (algebraMap K (SeparableClosure K) x))
      have hmap :
          algebraMap K (AlgebraicClosure K) x =
            algebraMap (SeparableClosure K) (AlgebraicClosure K)
              (algebraMap K (SeparableClosure K) x) :=
        (IsScalarTower.algebraMap_apply K (SeparableClosure K)
          (AlgebraicClosure K) x).symm
      rw [hmap]
      exact
        IsAlgClosure.equivOfEquiv_algebraMap
          (AlgebraicClosure K) (AlgebraicClosure K) eRing
          (algebraMap K (SeparableClosure K) x)
    _ = algebraMap (SeparableClosure K) (AlgebraicClosure K)
          (algebraMap K (SeparableClosure K) x) := by
      rw [show eRing (algebraMap K (SeparableClosure K) x) =
          algebraMap K (SeparableClosure K) x from τ.commutes x]
    _ = algebraMap K (AlgebraicClosure K) x := rfl

/-- Restrict an absolute Galois element of the chosen algebraic closure to the
absolute separable closure. -/
def restrictToSeparableClosure
    (K : Type u) [Field K] :
    Gal(AlgebraicClosure K / K) →* Gal(SeparableClosure K / K) where
  toFun σ := AlgEquiv.separableClosure σ
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

include K τ in
/-- States the theorem `separableClosureExtensionAlgEquiv_restricts`. -/
@[simp]
theorem separableClosureExtensionAlgEquiv_restricts
      (x : SeparableClosure K) :
    separableClosureExtensionAlgEquiv K τ x = τ x := by
  dsimp [separableClosureExtensionAlgEquiv]
  let : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  have : IsAlgClosure (SeparableClosure K) (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance
      isAlgebraic := inferInstance }
  change
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
      τ.toRingEquiv (algebraMap (SeparableClosure K) (AlgebraicClosure K) x) =
        algebraMap (SeparableClosure K) (AlgebraicClosure K) (τ x)
  exact
    IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure K) (AlgebraicClosure K) τ.toRingEquiv x

include K τ in
/-- States the theorem `restrictToSeparableClosure_extension`. -/
@[simp]
theorem restrictToSeparableClosure_extension
      :
    AlgEquiv.separableClosure (separableClosureExtensionAlgEquiv K τ) = τ := by
  ext x
  exact separableClosureExtensionAlgEquiv_restricts K τ x
end


/-- States the theorem `extension_restrictToSeparableClosure`. -/
@[simp]
theorem extension_restrictToSeparableClosure
    (K : Type u) [Field K] (σ : Gal(AlgebraicClosure K / K)) :
    separableClosureExtensionAlgEquiv K (AlgEquiv.separableClosure σ) = σ := by
  let : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  have : IsPurelyInseparable (SeparableClosure K) (AlgebraicClosure K) :=
    separableClosure.isPurelyInseparable K (AlgebraicClosure K)
  have hAlg :
      (separableClosureExtensionAlgEquiv K
        (AlgEquiv.separableClosure σ)).toAlgHom = σ.toAlgHom := by
    apply IsPurelyInseparable.injective_restrictDomain
        (F := SeparableClosure K) (E := AlgebraicClosure K)
        (R := K) (L := AlgebraicClosure K)
    ext x
    change
      separableClosureExtensionAlgEquiv K (AlgEquiv.separableClosure σ) x =
        σ x
    exact separableClosureExtensionAlgEquiv_restricts K
      (AlgEquiv.separableClosure σ) x
  ext x
  exact congrArg (fun f : AlgebraicClosure K →ₐ[K] AlgebraicClosure K => f x) hAlg

/-- The algebraic absolute Galois group of the chosen algebraic closure is
canonically the Galois group of the absolute separable closure. -/
noncomputable def separableClosureMulEquiv
    (K : Type u) [Field K] :
    Gal(AlgebraicClosure K / K) ≃* Gal(SeparableClosure K / K) where
  toFun σ := AlgEquiv.separableClosure σ
  invFun τ := separableClosureExtensionAlgEquiv K τ
  left_inv σ := extension_restrictToSeparableClosure K σ
  right_inv τ := restrictToSeparableClosure_extension K τ
  map_mul' σ τ := by
    ext x
    rfl

/-- States the theorem `separableClosureMulEquiv_continuous`. -/
theorem separableClosureMulEquiv_continuous
    (K : Type u) [Field K] :
    Continuous (separableClosureMulEquiv K :
      Gal(AlgebraicClosure K / K) → Gal(SeparableClosure K / K)) := by
  refine continuous_of_continuousAt_one (restrictToSeparableClosure K) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff K (SeparableClosure K) s).1 hs with
    ⟨E, hE, hEs⟩
  let Elift : IntermediateField K (AlgebraicClosure K) := IntermediateField.lift E
  have : FiniteDimensional K E := hE
  have : FiniteDimensional K Elift := by
    let eLin : E ≃ₗ[K] Elift := (IntermediateField.liftAlgEquiv E).toLinearEquiv
    exact Module.Finite.equiv eLin
  refine (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K)
    ((separableClosureMulEquiv K) ⁻¹' s)).2 ?_
  refine ⟨Elift, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change AlgEquiv.separableClosure σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply Subtype.ext
  change σ x = x
  have hxElift : (x : AlgebraicClosure K) ∈ Elift := by
    exact (IntermediateField.mem_lift x).2 hx
  exact (IntermediateField.mem_fixingSubgroup_iff Elift σ).1 hσ x hxElift

/-- States the theorem `lift_separableClosure_le_absoluteSeparableClosure`. -/
theorem lift_separableClosure_le_absoluteSeparableClosure
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField.lift (separableClosure K E) ≤
      (separableClosure K (AlgebraicClosure K)) := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact (mem_separableClosure_iff.1 hy).map E.val E.val.injective

/-- The separable part of a finite algebraic-closure intermediate field, viewed
inside the absolute separable closure. -/
def separablePartInAbsoluteSeparableClosure
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.restrict
    (lift_separableClosure_le_absoluteSeparableClosure K E)

/-- States the theorem `finiteDimensional_separablePartInAbsoluteSeparableClosure`. -/
theorem finiteDimensional_separablePartInAbsoluteSeparableClosure
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    FiniteDimensional K (separablePartInAbsoluteSeparableClosure K E) := by
  let Esep : IntermediateField K E := separableClosure K E
  have : FiniteDimensional K Esep := inferInstance
  let EsepLift : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.lift Esep
  have : FiniteDimensional K EsepLift := by
    let eLin : Esep ≃ₗ[K] EsepLift :=
      (IntermediateField.liftAlgEquiv Esep).toLinearEquiv
    exact Module.Finite.equiv eLin
  let hle := lift_separableClosure_le_absoluteSeparableClosure K E
  let eAlg :
      EsepLift ≃ₐ[K] separablePartInAbsoluteSeparableClosure K E :=
    IntermediateField.restrictAlgEquiv hle
  exact Module.Finite.equiv eAlg.toLinearEquiv

/-- States the theorem `separableClosureExtension_mem_fixingSubgroup_of_mem_separablePart`. -/
theorem separableClosureExtension_mem_fixingSubgroup_of_mem_separablePart
    (K : Type u) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (τ : Gal(SeparableClosure K / K))
    (hτ : τ ∈ (separablePartInAbsoluteSeparableClosure K E).fixingSubgroup) :
    separableClosureExtensionAlgEquiv K τ ∈ E.fixingSubgroup := by
  let Esep : IntermediateField K E := separableClosure K E
  let EsepLift : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.lift Esep
  let hle := lift_separableClosure_le_absoluteSeparableClosure K E
  have hfixSepLift :
      ∀ y ∈ EsepLift, separableClosureExtensionAlgEquiv K τ y = y := by
    intro y hy
    have hyS : y ∈ separableClosure K (AlgebraicClosure K) := hle hy
    let ys : SeparableClosure K := ⟨y, hyS⟩
    have hyF : ys ∈ separablePartInAbsoluteSeparableClosure K E := by
      exact (IntermediateField.mem_restrict hle ys).2 hy
    have hτfix :
        τ ys = ys :=
      (IntermediateField.mem_fixingSubgroup_iff
        (separablePartInAbsoluteSeparableClosure K E) τ).1 hτ ys hyF
    calc
      separableClosureExtensionAlgEquiv K τ y =
          separableClosureExtensionAlgEquiv K τ (ys : AlgebraicClosure K) := rfl
      _ = τ ys := separableClosureExtensionAlgEquiv_restricts K τ ys
      _ = ys := congrArg Subtype.val hτfix
      _ = y := rfl
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let : Algebra E (AlgebraicClosure K) := E.val.toRingHom.toAlgebra
  have : IsScalarTower K E (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have : IsPurelyInseparable Esep E :=
    separableClosure.isPurelyInseparable K E
  let : Algebra Esep (AlgebraicClosure K) :=
    ((algebraMap E (AlgebraicClosure K)).comp
      (algebraMap Esep E)).toAlgebra
  let incl : E →ₐ[Esep] AlgebraicClosure K :=
    { algebraMap E (AlgebraicClosure K) with
      commutes' := by
        intro y
        rfl }
  let moved : E →ₐ[Esep] AlgebraicClosure K :=
    { ((separableClosureExtensionAlgEquiv K τ).toRingHom.comp
        (algebraMap E (AlgebraicClosure K))) with
      commutes' := by
        intro y
        change separableClosureExtensionAlgEquiv K τ
            (algebraMap E (AlgebraicClosure K) (algebraMap Esep E y)) =
          algebraMap E (AlgebraicClosure K) (algebraMap Esep E y)
        have hyLift : (algebraMap E (AlgebraicClosure K)
            (algebraMap Esep E y)) ∈ EsepLift := by
          exact (IntermediateField.mem_lift (algebraMap Esep E y)).2 y.2
        exact hfixSepLift
          (algebraMap E (AlgebraicClosure K) (algebraMap Esep E y)) hyLift }
  have hmoved : moved = incl := Subsingleton.elim _ _
  have hpoint :=
    congrArg (fun f : E →ₐ[Esep] AlgebraicClosure K => f ⟨x, hx⟩) hmoved
  dsimp [moved, incl] at hpoint
  exact hpoint

/-- States the theorem `separableClosureMulEquiv_symm_continuous`. -/
theorem separableClosureMulEquiv_symm_continuous
    (K : Type u) [Field K] :
    Continuous ((separableClosureMulEquiv K).symm :
      Gal(SeparableClosure K / K) → Gal(AlgebraicClosure K / K)) := by
  refine continuous_of_continuousAt_one (separableClosureMulEquiv K).symm.toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) s).1 hs with
    ⟨E, hE, hEs⟩
  let F : IntermediateField K (SeparableClosure K) :=
    separablePartInAbsoluteSeparableClosure K E
  have : FiniteDimensional K E := hE
  have : FiniteDimensional K F :=
    finiteDimensional_separablePartInAbsoluteSeparableClosure K E
  refine (krullTopology_mem_nhds_one_iff K (SeparableClosure K)
    (((separableClosureMulEquiv K).symm) ⁻¹' s)).2 ?_
  refine ⟨F, inferInstance, ?_⟩
  intro τ hτ
  apply hEs
  change separableClosureExtensionAlgEquiv K τ ∈ E.fixingSubgroup
  exact
    separableClosureExtension_mem_fixingSubgroup_of_mem_separablePart
      K E τ hτ

/-- Topological identification of the usual algebraic-closure absolute Galois
group with the Galois group of the absolute separable closure. -/
noncomputable def separableClosureContinuousMulEquiv
    (K : Type u) [Field K] :
    Gal(AlgebraicClosure K / K) ≃ₜ* Gal(SeparableClosure K / K) where
  toMulEquiv := separableClosureMulEquiv K
  continuous_toFun := separableClosureMulEquiv_continuous K
  continuous_invFun := separableClosureMulEquiv_symm_continuous K

/-- The natural inclusion `Gal(M/E) -> Gal(M/K)` for an intermediate field
`E` of a field extension `M/K`. -/
def ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) :
    Gal(M / E) →* Gal(M / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `ofIntermediateFieldInExtension_apply`. -/
@[simp]
theorem ofIntermediateFieldInExtension_apply
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) (σ : Gal(M / E)) :
    ofIntermediateFieldInExtension E σ = σ.restrictScalars K :=
  rfl





























variable (K : Type u) [Field K]

section
variable (E : IntermediateField K (AlgebraicClosure K))
include E in
/-- The natural inclusion `Gal(K^al/E) → G_K`, for an intermediate field
`E ⊆ K^al`. -/
def ofIntermediateField   :
    Gal(AlgebraicClosure K / E) →* Gal(AlgebraicClosure K / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

include E in
/-- States the theorem `ofIntermediateField_apply`. -/
@[simp]
theorem ofIntermediateField_apply
     
    (σ : Gal(AlgebraicClosure K / E)) :
    ofIntermediateField K E σ = σ.restrictScalars K :=
  rfl



































theorem finiteDimensional_extendScalars_sup
    (k : Type u) (M : Type v) [Field k] [Field M] [Algebra k M]
    (E F : IntermediateField k M)
    [FiniteDimensional k E] [FiniteDimensional k F] :
    FiniteDimensional E
      (IntermediateField.extendScalars (F := E) (E := E ⊔ F) le_sup_left) := by
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional k EF := E.finiteDimensional_sup F
  let : Algebra E EF := (IntermediateField.inclusion le_sup_left).toAlgebra
  have : IsScalarTower k E EF := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    change (algebraMap k M) x =
      ((IntermediateField.inclusion le_sup_left) ((algebraMap k E) x) :
        M)
    rfl
  have : Module.Finite E EF := FiniteDimensional.right k E EF
  let eLin : EEF ≃ₗ[E] EF :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  exact Module.Finite.equiv eLin.symm

/-- For a finite intermediate extension `E/K`, the natural inclusion
`Gal(M/E) → Gal(M/K)` is continuous for the two Krull topologies. -/
theorem ofIntermediateFieldInExtension_continuous
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    [IsGalois k M]
    (E : IntermediateField k M) [FiniteDimensional k E] :
    Continuous (ofIntermediateFieldInExtension E) := by
  refine continuous_of_continuousAt_one
    (ofIntermediateFieldInExtension E) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rcases (krullTopology_mem_nhds_one_iff k M s).1 hs with
    ⟨F, hF, hFs⟩
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional k F := hF
  have : FiniteDimensional E EEF :=
    finiteDimensional_extendScalars_sup k M E F
  refine (krullTopology_mem_nhds_one_iff E M
    ((ofIntermediateFieldInExtension E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateFieldInExtension E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxEF : x ∈ EF := (show F ≤ EF from le_sup_right) hx
  have hxEEF : x ∈ EEF := by
    change x ∈ EF
    exact hxEF
  exact (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x hxEEF

include E in
private theorem finiteDimensional_restrictScalars
      [FiniteDimensional K E]
    (F : IntermediateField E (AlgebraicClosure K)) [FiniteDimensional E F] :
    FiniteDimensional K (F.restrictScalars K) := by
  have : FiniteDimensional K F := FiniteDimensional.trans K E F
  let FK : IntermediateField K (AlgebraicClosure K) := F.restrictScalars K
  let eLin : FK ≃ₗ[K] F :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  exact Module.Finite.equiv eLin.symm

include E in
/-- The natural inclusion `Gal(K^al/E) → G_K` is continuous for the Krull
topologies when `E/K` is finite. -/
theorem ofIntermediateField_continuous
      [FiniteDimensional K E] :
    Continuous (ofIntermediateField K E) := by
  refine continuous_of_continuousAt_one (ofIntermediateField K E) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rcases (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) s).1 hs with
    ⟨F, hF, hFs⟩
  let EF : IntermediateField K (AlgebraicClosure K) := E ⊔ F
  let EEF : IntermediateField E (AlgebraicClosure K) :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional K F := hF
  have : FiniteDimensional E EEF :=
    finiteDimensional_extendScalars_sup K (AlgebraicClosure K) E F
  refine (krullTopology_mem_nhds_one_iff E (AlgebraicClosure K)
    ((ofIntermediateField K E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateField K E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxEF : x ∈ EF := (show F ≤ EF from le_sup_right) hx
  have hxEEF : x ∈ EEF := by
    change x ∈ EF
    exact hxEF
  exact (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x hxEEF

include E in
/-- The finite-subextension open subgroup of `G_K` corresponding to
`E ⊆ K^al`. This is the concrete form of `G_E ≤ G_K`. -/
def openSubgroupOfFiniteIntermediateField
      [FiniteDimensional K E] :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) :=
  ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E⟩

include E in
/-- States the theorem `openSubgroupOfFiniteIntermediateField_toSubgroup`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateField_toSubgroup
      [FiniteDimensional K E] :
    (openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      E.fixingSubgroup :=
  rfl















































































include E in
/-- The normal-closure open subgroup contained in the open subgroup attached
to a finite intermediate field. -/
def openSubgroupOfNormalClosureFiniteIntermediateField
      [FiniteDimensional K E] :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) :=
  openSubgroupOfFiniteIntermediateField K
    (IntermediateField.normalClosure K E (AlgebraicClosure K))

include E in
/-- States the theorem `openSubgroupOfNormalClosureFiniteIntermediateField_toSubgroup`. -/
@[simp]
theorem openSubgroupOfNormalClosureFiniteIntermediateField_toSubgroup
      [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      (IntermediateField.normalClosure K E
        (AlgebraicClosure K)).fixingSubgroup :=
  rfl

include E in
/-- The normal-closure open subgroup lies inside the open subgroup for `E`. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_le
      [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) ≤
      openSubgroupOfFiniteIntermediateField K E := by
  change (IntermediateField.normalClosure K E
      (AlgebraicClosure K)).fixingSubgroup ≤ E.fixingSubgroup
  exact E.fixingSubgroup_le (IntermediateField.le_normalClosure E)

include E in
/-- The open subgroup `Gal(K^al/E) ≤ G_K` is canonically isomorphic to the
ordinary Galois group `Gal(K^al/E)`. -/
def openSubgroupOfFiniteIntermediateFieldEquiv
      [FiniteDimensional K E] :
    openSubgroupOfFiniteIntermediateField K E ≃* Gal(AlgebraicClosure K / E) :=
  IntermediateField.fixingSubgroupEquiv E

include E in
/-- States the theorem `openSubgroupOfFiniteIntermediateFieldEquiv_apply`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateFieldEquiv_apply
      [FiniteDimensional K E]
    (σ : openSubgroupOfFiniteIntermediateField K E) :
    openSubgroupOfFiniteIntermediateFieldEquiv K E σ =
      { AlgEquiv.toRingEquiv (σ : Gal(AlgebraicClosure K / K)) with
        commutes' := σ.2 } :=
  rfl

include E in
/-- States the theorem `coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply`. -/
@[simp]
theorem coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply
      [FiniteDimensional K E]
    (σ : Gal(AlgebraicClosure K / E)) :
    ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ :
      Gal(AlgebraicClosure K / K)) =
      ofIntermediateField K E σ :=
  rfl

include E in
/-- The identification between the finite-subextension open subgroup and
`Gal(K^al/E)` is continuous from the open subgroup to the Galois group. -/
theorem openSubgroupOfFiniteIntermediateFieldEquiv_continuous
      [FiniteDimensional K E] :
    Continuous (openSubgroupOfFiniteIntermediateFieldEquiv K E :
      openSubgroupOfFiniteIntermediateField K E → Gal(AlgebraicClosure K / E)) := by
  let H : Subgroup (Gal(AlgebraicClosure K / K)) :=
    openSubgroupOfFiniteIntermediateField K E
  let e : H ≃* Gal(AlgebraicClosure K / E) :=
    openSubgroupOfFiniteIntermediateFieldEquiv K E
  change Continuous (e : H → Gal(AlgebraicClosure K / E))
  refine continuous_of_continuousAt_one e.toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff E (AlgebraicClosure K) s).1 hs with
    ⟨F, hF, hFs⟩
  let FK : IntermediateField K (AlgebraicClosure K) := F.restrictScalars K
  have : FiniteDimensional E F := hF
  have : FiniteDimensional K FK :=
    finiteDimensional_restrictScalars K E F
  have hOpen :
      IsOpen {τ : openSubgroupOfFiniteIntermediateField K E |
        (τ : Gal(AlgebraicClosure K / K)) ∈ FK.fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen FK).preimage continuous_subtype_val
  have hMem :
      {τ : openSubgroupOfFiniteIntermediateField K E |
        (τ : Gal(AlgebraicClosure K / K)) ∈ FK.fixingSubgroup} ∈
          𝓝 (1 : openSubgroupOfFiniteIntermediateField K E) := by
    apply hOpen.mem_nhds
    change (1 : Gal(AlgebraicClosure K / K)) ∈ FK.fixingSubgroup
    exact FK.fixingSubgroup.one_mem
  refine Filter.mem_of_superset hMem ?_
  intro τ hτ
  apply hFs
  change e τ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change (τ : Gal(AlgebraicClosure K / K)) x = x
  have hxFK : x ∈ FK := by
    change x ∈ F
    exact hx
  exact (IntermediateField.mem_fixingSubgroup_iff FK
    (τ : Gal(AlgebraicClosure K / K))).1 hτ x hxFK

include E in
/-- The inverse identification `Gal(K^al/E) → Gal(K^al/E) ≤ G_K` is
continuous for finite `E/K`. -/
theorem openSubgroupOfFiniteIntermediateFieldEquiv_symm_continuous
      [FiniteDimensional K E] :
    Continuous ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm :
      Gal(AlgebraicClosure K / E) → openSubgroupOfFiniteIntermediateField K E) := by
  have hcomp :
      Continuous
        (fun σ : Gal(AlgebraicClosure K / E) =>
          (((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ :
            openSubgroupOfFiniteIntermediateField K E) :
            Gal(AlgebraicClosure K / K))) := by
    simpa only [coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply,
      ofIntermediateField] using ofIntermediateField_continuous K E
  exact Continuous.subtype_mk hcomp fun σ =>
    ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ).property

include E in
/-- The finite-subextension open subgroup is topologically isomorphic to
`Gal(K^al/E)`. -/
def openSubgroupOfFiniteIntermediateFieldContinuousMulEquiv
      [FiniteDimensional K E] :
    openSubgroupOfFiniteIntermediateField K E ≃ₜ*
      Gal(AlgebraicClosure K / E) :=
  { toMulEquiv := openSubgroupOfFiniteIntermediateFieldEquiv K E
    continuous_toFun := openSubgroupOfFiniteIntermediateFieldEquiv_continuous K E
    continuous_invFun := openSubgroupOfFiniteIntermediateFieldEquiv_symm_continuous K E }
end





























/-- If `E/K` is normal inside `K^al`, then the subgroup fixing `E` is normal
in `G_K`. -/
instance fixingSubgroup_normal_of_normal
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    E.fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker E]
  infer_instance

/-- The finite-subextension open subgroup is normal when the finite
subextension is normal over `K`. -/
theorem openSubgroupOfFiniteIntermediateField_normal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Normal K E] :
    ((openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).Normal := by
  change E.fixingSubgroup.Normal
  infer_instance

/-- The normal-closure open subgroup is normal in `G_K`. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_normal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).Normal := by
  change (IntermediateField.normalClosure K E
    (AlgebraicClosure K)).fixingSubgroup.Normal
  have : Normal K (IntermediateField.normalClosure K E (AlgebraicClosure K)) := by
    have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    exact (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := K) (K := E) (L := AlgebraicClosure K)
      (fun _ => IsAlgClosed.splits _)).normal
  infer_instance

/-- Provides the instance `instNormal`. -/
instance openSubgroupOfNormalClosureFiniteIntermediateField.instNormal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E).toSubgroup.Normal :=
  openSubgroupOfNormalClosureFiniteIntermediateField_normal K E

/-- For a normal intermediate field `E ⊆ K^al`, the quotient `G_K/G_E` is the
ordinary Galois group `Gal(E/K)`.  The quotient is written with
`Gal(AlgebraicClosure K / K)` so that the normal-subgroup instance for
`E.fixingSubgroup` is available by typeclass search. -/
def quotientEquivGalOfNormalIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    Gal(AlgebraicClosure K / K) ⧸ E.fixingSubgroup ≃* Gal(E / K) :=
  (QuotientGroup.quotientMulEquivOfEq
      ((IntermediateField.restrictNormalHom_ker E).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (AlgEquiv.restrictNormalHom E : Gal(AlgebraicClosure K / K) →* Gal(E / K))
      (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K)))












/-- Quotienting `G_K` by the normal-closure open subgroup attached to a finite
intermediate field gives the Galois group of that normal closure. -/
def quotientNormalClosureOpenSubgroupEquivGal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    Gal(AlgebraicClosure K / K) ⧸
        (openSubgroupOfNormalClosureFiniteIntermediateField K E :
          Subgroup (Gal(AlgebraicClosure K / K))) ≃*
      Gal(IntermediateField.normalClosure K E (AlgebraicClosure K) / K) :=
  quotientEquivGalOfNormalIntermediateField K
    (IntermediateField.normalClosure K E (AlgebraicClosure K))















/-- The index of the normal-closure open subgroup is the cardinality of the
finite automorphism group of the normal closure. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_index_eq_natCard_gal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))).index =
      Nat.card (Gal(IntermediateField.normalClosure K E (AlgebraicClosure K) / K)) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (quotientNormalClosureOpenSubgroupEquivGal K E).toEquiv

/-- Provides the instance `instFiniteIndex`. -/
instance openSubgroupOfNormalClosureFiniteIntermediateField.instFiniteIndex
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,
    openSubgroupOfNormalClosureFiniteIntermediateField_index_eq_natCard_gal]
  exact Nat.card_pos.ne'

/-- Provides the instance `instFiniteIndex`. -/
instance openSubgroupOfFiniteIntermediateField.instFiniteIndex
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).FiniteIndex :=
  Subgroup.finiteIndex_of_le
    (openSubgroupOfNormalClosureFiniteIntermediateField_le K E)





























/-- An open subgroup of `G_K`, viewed as a closed subgroup.  This is the bridge
from the topological finite-level API to mathlib's infinite Galois
correspondence. -/
def closedSubgroupOfOpenSubgroup
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    ClosedSubgroup (Gal(AlgebraicClosure K / K)) :=
  ⟨H.toSubgroup, by
    change IsClosed (H : Set (Gal(AlgebraicClosure K / K)))
    exact H.isClosed⟩

/-- States the theorem `closedSubgroupOfOpenSubgroup_toSubgroup`. -/
@[simp]
theorem closedSubgroupOfOpenSubgroup_toSubgroup
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (closedSubgroupOfOpenSubgroup K H :
      Subgroup (Gal(AlgebraicClosure K / K))) = H.toSubgroup :=
  rfl

/-- The finite fixed field attached to an open subgroup of `G_K`. -/
def fixedFieldOfOpenSubgroup
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField H.toSubgroup

/-- States the theorem `fixedFieldOfOpenSubgroup_def`. -/
@[simp]
theorem fixedFieldOfOpenSubgroup_def
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenSubgroup K H =
      IntermediateField.fixedField H.toSubgroup :=
  rfl

/-- The fixing subgroup of the fixed field of an open subgroup is the original
open subgroup, as a subgroup of `G_K`. -/
theorem fixingSubgroup_fixedFieldOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    (fixedFieldOfOpenSubgroup K H).fixingSubgroup = H.toSubgroup := by
  exact InfiniteGalois.fixingSubgroup_fixedField
    (closedSubgroupOfOpenSubgroup K H)

/-- Open subgroups of `G_K` have finite fixed fields. -/
theorem finiteDimensional_fixedFieldOfOpenSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenSubgroup K H) := by
  refine (InfiniteGalois.isOpen_iff_finite
    (K := AlgebraicClosure K) (fixedFieldOfOpenSubgroup K H)).1 ?_
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H]
  exact H.isOpen'

/-- Provides the instance `instFiniteDimensional`. -/
instance fixedFieldOfOpenSubgroup.instFiniteDimensional
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenSubgroup K H) :=
  finiteDimensional_fixedFieldOfOpenSubgroup K H





































































































































































































































































































/-- The fixed field of an open normal subgroup is a finite Galois
intermediate field. -/
def fixedFieldOfOpenNormalSubgroup
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    IntermediateField K (AlgebraicClosure K) :=
  fixedFieldOfOpenSubgroup K H.toOpenSubgroup

/-- States the theorem `fixedFieldOfOpenNormalSubgroup_def`. -/
@[simp]
theorem fixedFieldOfOpenNormalSubgroup_def
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    fixedFieldOfOpenNormalSubgroup K H =
      IntermediateField.fixedField H.toSubgroup :=
  rfl

/-- Provides the instance `instFiniteDimensional`. -/
instance fixedFieldOfOpenNormalSubgroup.instFiniteDimensional
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenNormalSubgroup K H) :=
  fixedFieldOfOpenSubgroup.instFiniteDimensional K H.toOpenSubgroup

/-- States the theorem `isGalois_fixedFieldOfOpenNormalSubgroup`. -/
theorem isGalois_fixedFieldOfOpenNormalSubgroup
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    IsGalois K (fixedFieldOfOpenNormalSubgroup K H) := by
  refine (InfiniteGalois.normal_iff_isGalois
    (K := AlgebraicClosure K) (fixedFieldOfOpenNormalSubgroup K H)).1 ?_
  change (fixedFieldOfOpenSubgroup K H.toOpenSubgroup).fixingSubgroup.Normal
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H.toOpenSubgroup]
  infer_instance

/-- Provides the instance `instNormal`. -/
instance fixedFieldOfOpenNormalSubgroup.instNormal
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    Normal K (fixedFieldOfOpenNormalSubgroup K H) := by
  have : IsGalois K (fixedFieldOfOpenNormalSubgroup K H) :=
    isGalois_fixedFieldOfOpenNormalSubgroup K H
  infer_instance


















































































































end absoluteGaloisGroup
end Field

end

end RamificationTheory
