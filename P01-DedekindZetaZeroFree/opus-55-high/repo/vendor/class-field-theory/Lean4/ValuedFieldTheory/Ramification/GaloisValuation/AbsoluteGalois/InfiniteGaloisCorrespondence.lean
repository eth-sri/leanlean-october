module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.AbsoluteRamification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-! Provides the public declarations in the `RamificationTheory.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence` Lean module. -/

namespace RamificationTheory

open ValuationTheory

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

theorem finiteDimensional_comap_algEquiv
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (E : IntermediateField F B)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.comap e.toAlgHom) := by
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  let eLin : Ecomap ≃ₗ[F] E :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e (e.symm x.1) ∈ E
        simp⟩
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
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
    simp
  algebraMap_mem' := by
    intro x
    simp_all

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
        simp_all }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨e y.1, y.2⟩, ?_⟩
    ext
    exact e.symm_apply_apply y.1
  have hfgImage : Submodule.FG ((⊤ : Submodule F' E).map f) :=
    by simp_all
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

/-- Algebra-equivalence conjugation is continuous for Krull topologies. -/
theorem algEquiv_autCongr_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
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
  simp_all

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
  simp_all

/-- If `E/K` is normal inside `K^al`, then the subgroup fixing `E` is normal
in `G_K`. -/
instance fixingSubgroup_normal_of_normal
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    E.fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker E]
  infer_instance
