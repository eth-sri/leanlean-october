/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Sentence

@[expose] public section

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower Spectrum Cardinal

universe u v w w'

section Coding

variable {L : Language.{u, v}} [L.IsRelational]

/-- An `L`-structure on `ℕ` is `L`-isomorphic, by the identity, to the decoding of its code
(`StructureSpace.ofStructure`): relation-wise the two agree (`toStructure_ofStructure`). -/
def ofStructureEquiv (inst : L.Structure ℕ) :
    @Language.Equiv L ℕ ℕ inst (StructureSpace.ofStructure inst).toStructure :=
  @Language.Equiv.mk L ℕ ℕ inst (StructureSpace.ofStructure inst).toStructure (Equiv.refl ℕ)
    (fun f => isEmptyElim f) (fun R xs => StructureSpace.toStructure_ofStructure inst R xs)

/-- A sentence holds in the decoding of the code of a structure on `ℕ` iff it holds in the
structure. -/
theorem realize_toStructure_ofStructure (inst : L.Structure ℕ) (φ : L.Sentenceω) :
    @Sentenceω.Realize L φ ℕ (StructureSpace.ofStructure inst).toStructure ↔
      @Sentenceω.Realize L φ ℕ inst :=
  (@LomegaEquiv.of_equiv L ℕ ℕ inst (StructureSpace.ofStructure inst).toStructure
    (ofStructureEquiv inst) φ).symm

end Coding

section Transfer

variable {M : Type w} {N : Type w'}

/-- **Structures to realizations.**  An `L`-isomorphism of structures satisfying (the
uniqueness clause of) `T` is an isomorphism of their realizations. -/
theorem IsKnightModel.isIso_toRealization {instM : knightLang.Structure M}
    {instN : knightLang.Structure N} (hM : IsKnightModel M) (hN : IsKnightModel N)
    (e : M ≃[knightLang] N) :
    (toRealization M).IsIso (toRealization N) e.toEquiv := by
  intro n t
  have key : ∀ p : S Ordinal.omega0 n,
      Holds p ⇑(t.trans e.toEquiv.toEmbedding) ↔ Holds p ⇑t := fun p =>
    StrongHomClass.map_rel e p ⇑t
  cases h : (toRealization M).eval t with
  | none =>
    rw [toRealization_eval_eq_none_iff] at h ⊢
    grind
  | some p =>
    exact (hN.eval_eq_some_iff _ p).mpr ((key p).mpr ((hM.eval_eq_some_iff t p).mp h))

/-- **Realizations to structures.**  An isomorphism of realizations is an `L`-isomorphism of
their structures (no model hypothesis needed). -/
def KnightRealization.IsIso.structureOfEquiv {R : KnightRealization omegaStage M}
    {R' : KnightRealization omegaStage N} {e : M ≃ N} (h : R.IsIso R' e) :
    @Language.Equiv knightLang M N (structureOf R) (structureOf R') :=
  @Language.Equiv.mk knightLang M N (structureOf R) (structureOf R') e (fun f => isEmptyElim f)
    fun {n} p xs => by
      change (∃ hi : Function.Injective (⇑e ∘ xs), R'.eval ⟨⇑e ∘ xs, hi⟩ = some p) ↔
        ∃ hi : Function.Injective xs, R.eval ⟨xs, hi⟩ = some p
      constructor
      · rintro ⟨hi, hp⟩
        exact ⟨hi.of_comp, (h ⟨xs, hi.of_comp⟩).symm.trans hp⟩
      · rintro ⟨hi, hp⟩
        exact ⟨e.injective.comp hi, (h ⟨xs, hi⟩).trans hp⟩

/-- Under `T`, the structure of the realization of `M` is `L`-isomorphic to `M` by the identity
(`holds_structureOf_toRealization`). -/
def IsKnightModel.structureOfToRealizationEquiv {inst : knightLang.Structure M}
    (h : IsKnightModel M) :
    @Language.Equiv knightLang M M (structureOf (toRealization M)) inst :=
  @Language.Equiv.mk knightLang M M (structureOf (toRealization M)) inst (Equiv.refl M)
    (fun f => isEmptyElim f) fun p xs => (holds_structureOf_toRealization h p xs).symm

end Transfer

/-- The models of `S^ω` on the carrier `ℕ`. -/
abbrev KnightNatModel : Type 1 := {R : KnightRealization omegaStage ℕ // R.IsModel}

/-- **Models of `S^ω` on `ℕ` up to isomorphism**: the ambient `Realization.isoSetoid` pulled
back to the models. -/
noncomputable def knightModelSetoid : Setoid KnightNatModel :=
  (Realization.isoSetoid knightTower omegaStage ℕ).comap Subtype.val

theorem knightModelSetoid_r_iff {R R' : KnightNatModel} :
    knightModelSetoid.r R R' ↔ Nonempty (R.1.Iso R'.1) := Iff.rfl

/-- A coded `ℕ`-model of `T` decodes to a structure satisfying the clauses of `T`. -/
theorem isKnightModel_of_mem (c : ModelsOf knightSentence) :
    @IsKnightModel ℕ c.1.toStructure :=
  (@realize_knightSentence_iff ℕ c.1.toStructure).mp c.2

/-- Decode a coded `ℕ`-model of `T` and take its realization: a model of `S^ω` on `ℕ`. -/
noncomputable def realizationOfCode (c : ModelsOf knightSentence) : KnightNatModel :=
  ⟨@toRealization ℕ c.1.toStructure, @isModel_toRealization_of_realize ℕ c.1.toStructure c.2⟩

/-- The structure of a model of `S^ω` on `ℕ`, coded: a coded `ℕ`-model of `T`. -/
noncomputable def codeOfModel (R : KnightNatModel) : ModelsOf knightSentence :=
  ⟨StructureSpace.ofStructure (structureOf R.1),
    (realize_toStructure_ofStructure (structureOf R.1) knightSentence).mpr
      R.2.realize_knightSentence⟩

/-- The decoded structure of the code of an `ℕ`-model of `S^ω` (isomorphic to `structureOf R.1`
by the identity, `ofStructureEquiv`). -/
noncomputable abbrev codeStructure (R : KnightNatModel) : knightLang.Structure ℕ :=
  (StructureSpace.ofStructure (structureOf R.1)).toStructure

/-- `realizationOfCode` respects isomorphism. -/
theorem realizationOfCode_rel {c₁ c₂ : ModelsOf knightSentence}
    (h : (isoSetoid knightSentence).r c₁ c₂) :
    knightModelSetoid.r (realizationOfCode c₁) (realizationOfCode c₂) := by
  obtain ⟨e⟩ := isoSetoid_r_iff.mp h
  exact ⟨⟨@Language.Equiv.toEquiv knightLang ℕ ℕ c₁.1.toStructure c₂.1.toStructure e,
    (isKnightModel_of_mem c₁).isIso_toRealization (isKnightModel_of_mem c₂) e⟩⟩

/-- `codeOfModel` respects isomorphism. -/
theorem codeOfModel_rel {R R' : KnightNatModel} (h : knightModelSetoid.r R R') :
    (isoSetoid knightSentence).r (codeOfModel R) (codeOfModel R') := by
  obtain ⟨⟨e, he⟩⟩ := h
  refine isoSetoid_r_iff.mpr ⟨?_⟩
  -- code R ≃ structureOf R ≃ structureOf R' ≃ code R'
  exact @Language.Equiv.comp knightLang ℕ ℕ (codeStructure R) (structureOf R'.1) ℕ
    (codeStructure R') (ofStructureEquiv (structureOf R'.1))
    (@Language.Equiv.comp knightLang ℕ ℕ (codeStructure R) (structureOf R.1) ℕ
      (structureOf R'.1) (KnightRealization.IsIso.structureOfEquiv he)
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf R.1) (codeStructure R)
        (ofStructureEquiv (structureOf R.1))))

/-- Isomorphism classes of coded `ℕ`-models of `T` to isomorphism classes of `ℕ`-models of
`S^ω`. -/
noncomputable def classOfCode :
    Quotient (isoSetoid knightSentence) → Quotient knightModelSetoid :=
  Quotient.map realizationOfCode fun _ _ h => realizationOfCode_rel h

/-- Isomorphism classes of `ℕ`-models of `S^ω` to isomorphism classes of coded `ℕ`-models of
`T`. -/
noncomputable def classOfModel :
    Quotient knightModelSetoid → Quotient (isoSetoid knightSentence) :=
  Quotient.map codeOfModel fun _ _ h => codeOfModel_rel h

/-- **Prop. 3.3.5, isomorphism classes**: the countable (`ℕ`-carrier) models of `T` up to
isomorphism are in bijection with the models of `S^ω` on `ℕ` up to isomorphism. -/
noncomputable def isoClassEquiv :
    Quotient (isoSetoid knightSentence) ≃ Quotient knightModelSetoid where
  toFun := classOfCode
  invFun := classOfModel
  left_inv := by
    refine Quotient.ind fun c => Quotient.sound ?_
    refine isoSetoid_r_iff.mpr ⟨?_⟩
    -- code (structureOf (toRealization c)) ≃ structureOf (toRealization c) ≃ c
    exact @Language.Equiv.comp knightLang ℕ ℕ (codeStructure (realizationOfCode c))
      (structureOf (@toRealization ℕ c.1.toStructure)) ℕ c.1.toStructure
      (isKnightModel_of_mem c).structureOfToRealizationEquiv
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf (@toRealization ℕ c.1.toStructure))
        (codeStructure (realizationOfCode c)) (ofStructureEquiv _))
  right_inv := by
    refine Quotient.ind fun R => Quotient.sound ?_
    refine ⟨⟨Equiv.refl ℕ, fun t => ?_⟩⟩
    -- toRealization (code (structureOf R)) ≅ toRealization (structureOf R) = R
    have h := (IsKnightModel.isIso_toRealization (isKnightModel_of_mem (codeOfModel R))
      R.2.isKnightModel
      (@Language.Equiv.symm knightLang ℕ ℕ (structureOf R.1) (codeStructure R)
        (ofStructureEquiv _))) t
    rwa [toRealization_structureOf_eval] at h

/-- **`I(T, ℵ₀)` is the number of models of `S^ω` on `ℕ` up to isomorphism** (the transfer
#61 consumes).  Both sides live in `Cardinal.{1}` (`knightLang : Language.{0, 1}`;
`S ω n : Type 1`); no universe lifts are involved. -/
theorem natModelSpectrum_knightSentence :
    natModelSpectrum knightSentence = #(Quotient knightModelSetoid) :=
  mk_congr isoClassEquiv

end VaughtConjecture.Knight
