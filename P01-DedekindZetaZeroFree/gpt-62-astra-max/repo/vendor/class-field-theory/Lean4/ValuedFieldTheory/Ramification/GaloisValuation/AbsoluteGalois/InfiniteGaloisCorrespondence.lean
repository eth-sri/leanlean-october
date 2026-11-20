module
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding

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

variable {G : Type*} [Group G] (H : Subgroup G)

private theorem quotientAction_ker_eq_normalCore :
    (MulAction.toPermHom G (G ⧸ H)).ker = H.normalCore := by
  ext g
  constructor
  · intro hg b
    have hq : g • (QuotientGroup.mk (b⁻¹) : G ⧸ H) =
        QuotientGroup.mk (b⁻¹) := by
      have := congrArg
        (fun e : Equiv.Perm (G ⧸ H) => e (QuotientGroup.mk (b⁻¹))) hg
      exact this
    simpa [mul_assoc] using (H.inv_mem (QuotientGroup.eq.1 hq))
  · intro hg
    ext q
    refine Quotient.inductionOn q ?_
    intro b
    apply QuotientGroup.eq.2
    simpa [mul_assoc] using (H.inv_mem (hg (b⁻¹)))

 theorem normalCore_finiteIndex_of_finite_quotient [Finite (G ⧸ H)] :
    H.normalCore.FiniteIndex := by
  rw [← quotientAction_ker_eq_normalCore H, Subgroup.finiteIndex_iff,
    Subgroup.index_ker]
  exact ne_of_gt Nat.card_pos

end

section

variable {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B)

private theorem finiteDimensional_comap_algEquiv (E : IntermediateField F B)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.comap e.toAlgHom) := by
  let eLin : (E.comap e.toAlgHom) ≃ₗ[F] E :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e (e.symm x.1) ∈ E
        simp [e.apply_symm_apply]⟩
      left_inv := by
        grind [e.symm_apply_apply]
      right_inv := by
        grind [e.apply_symm_apply]
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  exact Module.Finite.equiv eLin.symm

 theorem finiteDimensional_map_algEquiv (E : IntermediateField F A)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.map e.toAlgHom) := by
  let eLin : E ≃ₗ[F] (E.map e.toAlgHom) :=
    { toFun := fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x => ⟨e.symm x.1, by
        rcases x.2 with ⟨y, hy, hxy⟩
        rw [← hxy]
        simpa using hy⟩
      left_inv := by
        grind [e.symm_apply_apply]
      right_inv := by
        grind [e.apply_symm_apply]
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        exact e.toLinearEquiv.map_smul a x.1 }
  exact Module.Finite.equiv eLin

end

section

variable {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z} [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω'] (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F, e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))

/-- Pull back an intermediate field along a ring equivalence which is
semilinear over a base-field equivalence.  This is the finite-level source
needed for Krull-continuity of conjugation by such a semilinear equivalence. -/
def semilinearRingEquivPreimageIntermediateField
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

/-- States the theorem `mem_semilinearRingEquivPreimageIntermediateField_iff`. -/
@[simp]
theorem mem_semilinearRingEquivPreimageIntermediateField_iff
    (E : IntermediateField F' Ω') (x : Ω) :
    x ∈ semilinearRingEquivPreimageIntermediateField τ e he E ↔ e x ∈ E :=
  Iff.rfl

/-- States the theorem `semilinearRingEquivPreimageIntermediateField_symm_mem`. -/
theorem semilinearRingEquivPreimageIntermediateField_symm_mem
    (E : IntermediateField F' Ω') {x : Ω'} (hx : x ∈ E) :
    e.symm x ∈ semilinearRingEquivPreimageIntermediateField τ e he E := by
  simpa using hx

/-- The semilinear pullback of a finite intermediate field is finite. -/
theorem finiteDimensional_semilinearRingEquivPreimageIntermediateField
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
  have hmaptop : (⊤ : Submodule F' E).map f =
      (⊤ : Submodule F T) := by
    rw [Submodule.map_top, LinearMap.range_eq_top_of_surjective f hsurj]
  exact Module.Finite.of_fg_top (by simpa [hmaptop] using ((Module.Finite.fg_top (R := F') (M := E)).map f))

include he in
/-- Conjugation by a semilinear equivalence of an algebraic closure is
continuous for the Krull topology.  The semilinear base action is recorded
explicitly by `he`, and the group homomorphism is required only to have the
corresponding conjugation formula on underlying ring equivalences. -/
theorem semilinear_conjugation_continuous
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
  let Epre :=
    semilinearRingEquivPreimageIntermediateField τ e he E
  have := hE
  have :=
    finiteDimensional_semilinearRingEquivPreimageIntermediateField
      τ e he E
  refine (krullTopology_mem_nhds_one_iff F Ω (φ ⁻¹' s)).2 ?_
  refine ⟨Epre, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change φ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff Epre σ).1 hσ
      (e.symm x) (semilinearRingEquivPreimageIntermediateField_symm_mem
        τ e he E hx)
  change (φ σ).toRingEquiv x = x
  rw [hφ σ]
  simp [hfix, e.apply_symm_apply]

end

/-- Algebra-equivalence conjugation is continuous for Krull topologies. -/
theorem algEquiv_autCongr_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
    Continuous (AlgEquiv.autCongr e : Gal(A / F) → Gal(B / F)) := by apply @AlgebraicNumberTheory.continuous_algEquiv_autCongr <;> assumption

section

variable (K : Type u) [Field K] (τ : Gal(SeparableClosure K / K))

/-- Extend a `K`-automorphism of the absolute separable closure to the fixed
chosen algebraic closure.  The extension is canonical because
`AlgebraicClosure K` is purely inseparable over `SeparableClosure K`. -/
noncomputable def separableClosureExtensionAlgEquiv :
    Gal(AlgebraicClosure K / K) := by
  letI : Algebra (SeparableClosure K) (AlgebraicClosure K) :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  haveI : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  haveI : IsAlgClosure (SeparableClosure K) (AlgebraicClosure K) :=
    { isAlgClosed := inferInstance
      isAlgebraic := inferInstance }
  let eRing := τ.toRingEquiv
  let e0 :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K) eRing
  refine
    { e0 with
      commutes' := ?_ }
  intro x
  let algebraMap₀ := algebraMap K (SeparableClosure K) x
  calc
    e0 (algebraMap K (AlgebraicClosure K) x) =
        algebraMap (SeparableClosure K) (AlgebraicClosure K)
          (eRing (algebraMap₀)) := by
      change
        IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
            eRing (algebraMap K (AlgebraicClosure K) x) =
          algebraMap (SeparableClosure K) (AlgebraicClosure K)
            (eRing (algebraMap₀))
      have hmap :
          algebraMap K (AlgebraicClosure K) x =
            algebraMap (SeparableClosure K) (AlgebraicClosure K)
              (algebraMap₀) :=
        (IsScalarTower.algebraMap_apply K (SeparableClosure K)
          (AlgebraicClosure K) x).symm
      rw [hmap]
      change
        IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure K)
            eRing (algebraMap K (AlgebraicClosure K) x) =
          algebraMap (SeparableClosure K) (AlgebraicClosure K)
            (eRing (algebraMap₀))
      have hmap :
          algebraMap K (AlgebraicClosure K) x =
            algebraMap (SeparableClosure K) (AlgebraicClosure K)
              (algebraMap₀) :=
        (IsScalarTower.algebraMap_apply K (SeparableClosure K)
          (AlgebraicClosure K) x).symm
      rw [hmap]
      exact
        IsAlgClosure.equivOfEquiv_algebraMap
          (AlgebraicClosure K) (AlgebraicClosure K) eRing
          (algebraMap₀)
    _ = algebraMap (SeparableClosure K) (AlgebraicClosure K)
          (algebraMap₀) := by
      rw [show eRing (algebraMap₀) =
          algebraMap₀ from τ.commutes x]
    _ = algebraMap K (AlgebraicClosure K) x := rfl

/-- States the theorem `separableClosureExtensionAlgEquiv_restricts`. -/
@[simp]
theorem separableClosureExtensionAlgEquiv_restricts (x : SeparableClosure K) :
    separableClosureExtensionAlgEquiv K τ x = τ x := by
  dsimp [separableClosureExtensionAlgEquiv]
  let :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
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

end

/-- States the theorem `extension_restrictToSeparableClosure`. -/
@[simp]
theorem extension_restrictToSeparableClosure
    (K : Type u) [Field K] (σ : Gal(AlgebraicClosure K / K)) :
    separableClosureExtensionAlgEquiv K (AlgEquiv.separableClosure σ) = σ := by
  let :=
    (separableClosure K (AlgebraicClosure K)).val.toRingHom.toAlgebra
  have : IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => by
      rfl
  have :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K)
      (A := AlgebraicClosure K)
  have :=
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

section

variable {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M] (E : IntermediateField K M)

/-- The natural inclusion `Gal(M/E) -> Gal(M/K)` for an intermediate field
`E` of a field extension `M/K`. -/
def ofIntermediateFieldInExtension :
    Gal(M / E) →* Gal(M / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `ofIntermediateFieldInExtension_apply`. -/
@[simp]
theorem ofIntermediateFieldInExtension_apply (σ : Gal(M / E)) :
    ofIntermediateFieldInExtension E σ = σ.restrictScalars K :=
  rfl

end

variable (K : Type u) [Field K]

/-- The natural inclusion `Gal(K^al/E) → G_K`, for an intermediate field
`E ⊆ K^al`. -/
def ofIntermediateField (E : IntermediateField K (AlgebraicClosure K)) :
    Gal(AlgebraicClosure K / E) →* Gal(AlgebraicClosure K / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `ofIntermediateField_apply`. -/
@[simp]
theorem ofIntermediateField_apply
    (E : IntermediateField K (AlgebraicClosure K))
    (σ : Gal(AlgebraicClosure K / E)) :
    ofIntermediateField K E σ = σ.restrictScalars K :=
  rfl

theorem finiteDimensional_extendScalars_sup
    (k : Type u) (M : Type v) [Field k] [Field M] [Algebra k M]
    (E F : IntermediateField k M)
    [FiniteDimensional k E] [FiniteDimensional k F] :
    FiniteDimensional E
      (IntermediateField.extendScalars (F := E) (E := E ⊔ F) le_sup_left) := by
  let EF := E ⊔ F
  let EEF :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have := E.finiteDimensional_sup F
  let : Algebra E EF := (IntermediateField.inclusion le_sup_left).toAlgebra
  have : IsScalarTower k E EF := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rfl
  have := FiniteDimensional.right k E EF
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
  let EF := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have := hF
  have :=
    finiteDimensional_extendScalars_sup k M E F
  refine (krullTopology_mem_nhds_one_iff E M
    ((ofIntermediateFieldInExtension E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateFieldInExtension E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x ?_
  exact ((show F ≤ EF from le_sup_right) hx)

section

variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]

/-- The finite-subextension open subgroup of `G_K` corresponding to
`E ⊆ K^al`. This is the concrete form of `G_E ≤ G_K`. -/
def openSubgroupOfFiniteIntermediateField :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) :=
  ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E⟩

/-- States the theorem `openSubgroupOfFiniteIntermediateField_toSubgroup`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateField_toSubgroup :
    (openSubgroupOfFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      E.fixingSubgroup :=
  rfl

/-- States the theorem `mem_openSubgroupOfFiniteIntermediateField`. -/
@[simp]
theorem mem_openSubgroupOfFiniteIntermediateField
    (σ : Gal(AlgebraicClosure K / K)) :
    σ ∈ openSubgroupOfFiniteIntermediateField K E ↔
      ∀ x ∈ E, σ x = x := by
  rw [← IntermediateField.mem_fixingSubgroup_iff E σ]
  rfl

end

/-- The normal-closure open subgroup contained in the open subgroup attached
to a finite intermediate field. -/
def openSubgroupOfNormalClosureFiniteIntermediateField
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) :=
  openSubgroupOfFiniteIntermediateField K
    (IntermediateField.normalClosure K E (AlgebraicClosure K))

section

variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]

/-- States the theorem `openSubgroupOfNormalClosureFiniteIntermediateField_toSubgroup`. -/
@[simp]
theorem openSubgroupOfNormalClosureFiniteIntermediateField_toSubgroup :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      (IntermediateField.normalClosure K E
        (AlgebraicClosure K)).fixingSubgroup :=
  rfl

/-- The normal-closure open subgroup lies inside the open subgroup for `E`. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_le :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))) ≤
      openSubgroupOfFiniteIntermediateField K E := by
  exact E.fixingSubgroup_le (IntermediateField.le_normalClosure E)

/-- The open subgroup `Gal(K^al/E) ≤ G_K` is canonically isomorphic to the
ordinary Galois group `Gal(K^al/E)`. -/
def openSubgroupOfFiniteIntermediateFieldEquiv :
    openSubgroupOfFiniteIntermediateField K E ≃* Gal(AlgebraicClosure K / E) :=
  IntermediateField.fixingSubgroupEquiv E

/-- States the theorem `openSubgroupOfFiniteIntermediateFieldEquiv_apply`. -/
@[simp]
theorem openSubgroupOfFiniteIntermediateFieldEquiv_apply
    (σ : openSubgroupOfFiniteIntermediateField K E) :
    openSubgroupOfFiniteIntermediateFieldEquiv K E σ =
      { AlgEquiv.toRingEquiv (σ : Gal(AlgebraicClosure K / K)) with
        commutes' := σ.2 } :=
  rfl

/-- States the theorem `coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply`. -/
@[simp]
theorem coe_openSubgroupOfFiniteIntermediateFieldEquiv_symm_apply
    (σ : Gal(AlgebraicClosure K / E)) :
    ((openSubgroupOfFiniteIntermediateFieldEquiv K E).symm σ :
      Gal(AlgebraicClosure K / K)) =
      ofIntermediateField K E σ :=
  rfl

end

/-- If `E/K` is normal inside `K^al`, then the subgroup fixing `E` is normal
in `G_K`. -/
instance fixingSubgroup_normal_of_normal
    (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    E.fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker E]
  infer_instance

/-- The normal-closure open subgroup is normal in `G_K`. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_normal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    ((openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K)))).Normal := by
  change (IntermediateField.normalClosure K E
    (AlgebraicClosure K)).fixingSubgroup.Normal
  infer_instance

/-- Provides the instance `instNormal`. -/
instance openSubgroupOfNormalClosureFiniteIntermediateField.instNormal
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E).toSubgroup.Normal :=
  openSubgroupOfNormalClosureFiniteIntermediateField_normal K E

section

variable (E : IntermediateField K (AlgebraicClosure K))

/-- For a normal intermediate field `E ⊆ K^al`, the quotient `G_K/G_E` is the
ordinary Galois group `Gal(E/K)`.  The quotient is written with
`Gal(AlgebraicClosure K / K)` so that the normal-subgroup instance for
`E.fixingSubgroup` is available by typeclass search. -/
def quotientEquivGalOfNormalIntermediateField [Normal K E] :
    Gal(AlgebraicClosure K / K) ⧸ E.fixingSubgroup ≃* Gal(E / K) :=
  (QuotientGroup.quotientMulEquivOfEq
      ((IntermediateField.restrictNormalHom_ker E).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (AlgEquiv.restrictNormalHom E : Gal(AlgebraicClosure K / K) →* Gal(E / K))
      (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K)))

/-- Quotienting `G_K` by the normal-closure open subgroup attached to a finite
intermediate field gives the Galois group of that normal closure. -/
def quotientNormalClosureOpenSubgroupEquivGal [FiniteDimensional K E] :
    Gal(AlgebraicClosure K / K) ⧸
        (openSubgroupOfNormalClosureFiniteIntermediateField K E :
          Subgroup (Gal(AlgebraicClosure K / K))) ≃*
      Gal(IntermediateField.normalClosure K E (AlgebraicClosure K) / K) :=
  quotientEquivGalOfNormalIntermediateField K
    (IntermediateField.normalClosure K E (AlgebraicClosure K))

/-- The index of the normal-closure open subgroup is the cardinality of the
finite automorphism group of the normal closure. -/
theorem openSubgroupOfNormalClosureFiniteIntermediateField_index_eq_natCard_gal [FiniteDimensional K E] :
    (openSubgroupOfNormalClosureFiniteIntermediateField K E :
      Subgroup (Gal(AlgebraicClosure K / K))).index =
      Nat.card (Gal(IntermediateField.normalClosure K E (AlgebraicClosure K) / K)) := by
  exact Nat.card_congr (quotientNormalClosureOpenSubgroupEquivGal K E).toEquiv

end

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

section

variable (H : OpenSubgroup (Gal(AlgebraicClosure K / K)))

/-- An open subgroup of `G_K`, viewed as a closed subgroup.  This is the bridge
from the topological finite-level API to mathlib's infinite Galois
correspondence. -/
def closedSubgroupOfOpenSubgroup :
    ClosedSubgroup (Gal(AlgebraicClosure K / K)) :=
  ⟨H.toSubgroup, by
    exact H.isClosed⟩

/-- States the theorem `closedSubgroupOfOpenSubgroup_toSubgroup`. -/
@[simp]
theorem closedSubgroupOfOpenSubgroup_toSubgroup :
    (closedSubgroupOfOpenSubgroup K H :
      Subgroup (Gal(AlgebraicClosure K / K))) = H.toSubgroup :=
  rfl

/-- The finite fixed field attached to an open subgroup of `G_K`. -/
def fixedFieldOfOpenSubgroup :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField H.toSubgroup

/-- States the theorem `fixedFieldOfOpenSubgroup_def`. -/
@[simp]
theorem fixedFieldOfOpenSubgroup_def :
    fixedFieldOfOpenSubgroup K H =
      IntermediateField.fixedField H.toSubgroup :=
  rfl

end

section

variable [IsGalois K (AlgebraicClosure K)] (H : OpenSubgroup (Gal(AlgebraicClosure K / K)))

/-- The fixing subgroup of the fixed field of an open subgroup is the original
open subgroup, as a subgroup of `G_K`. -/
theorem fixingSubgroup_fixedFieldOfOpenSubgroup :
    (fixedFieldOfOpenSubgroup K H).fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField
    (closedSubgroupOfOpenSubgroup K H)

/-- Open subgroups of `G_K` have finite fixed fields. -/
theorem finiteDimensional_fixedFieldOfOpenSubgroup :
    FiniteDimensional K (fixedFieldOfOpenSubgroup K H) := by
  refine (InfiniteGalois.isOpen_iff_finite
     (fixedFieldOfOpenSubgroup K H)).1 ?_
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H]
  exact H.isOpen'

end

/-- Provides the instance `instFiniteDimensional`. -/
instance fixedFieldOfOpenSubgroup.instFiniteDimensional
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K))) :
    FiniteDimensional K (fixedFieldOfOpenSubgroup K H) :=
  finiteDimensional_fixedFieldOfOpenSubgroup K H

section

variable [IsGalois K (AlgebraicClosure K)] (σ : Gal(AlgebraicClosure K / K))
    (H : OpenSubgroup (Gal(AlgebraicClosure K / K)))

/-- Conjugate an arbitrary open subgroup of `G_K` through the finite-level
reverse Galois correspondence.  Its fixed field is the image of the original
finite fixed field under the chosen absolute Galois element. -/
def conjugateOpenSubgroupOfOpenSubgroup :
    OpenSubgroup (Gal(AlgebraicClosure K / K)) := by
  let E :=
    fixedFieldOfOpenSubgroup K H
  haveI :=
    fixedFieldOfOpenSubgroup.instFiniteDimensional K H
  let σ' := σ
  haveI :=
    finiteDimensional_map_algEquiv σ' E
  exact openSubgroupOfFiniteIntermediateField K (E.map σ'.toAlgHom)

/-- The subgroup underlying the conjugate open subgroup is the pointwise
conjugate subgroup. -/
@[simp]
theorem conjugateOpenSubgroupOfOpenSubgroup_toSubgroup :
    (conjugateOpenSubgroupOfOpenSubgroup K σ H :
      Subgroup (Gal(AlgebraicClosure K / K))) =
      Subgroup.map (MulAut.conj σ).toMonoidHom H.toSubgroup := by
  let E :=
    fixedFieldOfOpenSubgroup K H
  let σ' := σ
  calc
    _ =
        (MulAut.conj σ') • E.fixingSubgroup :=
      IsGalois.map_fixingSubgroup E σ'
    _ = Subgroup.map (MulAut.conj σ').toMonoidHom E.fixingSubgroup := by
      rw [Subgroup.pointwise_smul_def]
      constructor <;> rintro ⟨η, hη, rfl⟩ <;> exact ⟨η, hη, rfl⟩
    _ = Subgroup.map (MulAut.conj σ').toMonoidHom H.toSubgroup := by
      rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H]

end

section

variable [IsGalois K (AlgebraicClosure K)] (H : OpenSubgroup (Gal(AlgebraicClosure K / K)))

/-- The normal core of an open subgroup of `G_K`, as an open normal subgroup.
This is the canonical finite Galois quotient lying below an arbitrary finite
level. -/
def openNormalCoreOfOpenSubgroup :
    OpenNormalSubgroup (Gal(AlgebraicClosure K / K)) where
  toOpenSubgroup :=
    ⟨H.toSubgroup.normalCore, by
      have :=
        Subgroup.quotient_finite_of_isOpen H.toSubgroup H.isOpen
      have :=
        normalCore_finiteIndex_of_finite_quotient H.toSubgroup
      exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup.normalCore
        (Subgroup.normalCore_isClosed H.toSubgroup (by exact H.isClosed))⟩
  isNormal' := Subgroup.normalCore_normal H.toSubgroup

/-- States the theorem `openNormalCoreOfOpenSubgroup_toSubgroup`. -/
@[simp]
theorem openNormalCoreOfOpenSubgroup_toSubgroup :
    (openNormalCoreOfOpenSubgroup K H :
      Subgroup (Gal(AlgebraicClosure K / K))) = H.toSubgroup.normalCore :=
  rfl

end

section

variable (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K)))

/-- The fixed field of an open normal subgroup is a finite Galois
intermediate field. -/
def fixedFieldOfOpenNormalSubgroup :
    IntermediateField K (AlgebraicClosure K) :=
  fixedFieldOfOpenSubgroup K H.toOpenSubgroup

/-- States the theorem `fixedFieldOfOpenNormalSubgroup_def`. -/
@[simp]
theorem fixedFieldOfOpenNormalSubgroup_def :
    fixedFieldOfOpenNormalSubgroup K H =
      IntermediateField.fixedField H.toSubgroup :=
  rfl

end

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
     (fixedFieldOfOpenNormalSubgroup K H)).1 ?_
  change (fixedFieldOfOpenSubgroup K H.toOpenSubgroup).fixingSubgroup.Normal
  rw [fixingSubgroup_fixedFieldOfOpenSubgroup K H.toOpenSubgroup]
  infer_instance

/-- Provides the instance `instNormal`. -/
instance fixedFieldOfOpenNormalSubgroup.instNormal
    [IsGalois K (AlgebraicClosure K)]
    (H : OpenNormalSubgroup (Gal(AlgebraicClosure K / K))) :
    Normal K (fixedFieldOfOpenNormalSubgroup K H) := by
  have :=
    isGalois_fixedFieldOfOpenNormalSubgroup K H
  infer_instance

end absoluteGaloisGroup
end Field

end

end RamificationTheory
