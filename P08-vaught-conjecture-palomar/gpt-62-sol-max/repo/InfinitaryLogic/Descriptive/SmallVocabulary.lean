/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import InfinitaryLogic.Descriptive.Polish
public import Mathlib.Logic.Small.Basic

/-!
# A chosen small-vocabulary presentation of a countable relational language

The coded descriptive theorems (`Descriptive/LopezEscobar.lean`, `SentenceRecovery.lean`,
`SentenceObservables.lean`, …) are stated for `L : Language.{0, 0}`, while `StructureSpace L` is
defined for every `L : Language.{u, v}`.  This module supplies a **chosen** presentation of a
countable relational `L` in `Type 0` together with the transport laws that let the small-universe
theorems be applied to `L`:

* `lang L : Language.{0, 0}`: the relation symbols of each arity renamed through `Shrink`
  (a choice: `equivShrink` is not canonical), no function symbols.
* `toLang L : lang L →ᴸ L`: the decoding homomorphism (Mathlib's `LHom` is cross-universe).
* `code`/`decode`: structure codes transported both ways by precomposing the query with the
  renaming; mutually inverse (`decode_code`, `code_decode`), continuous, hence the homeomorphism
  `codeHomeomorph` and measurable maps (`measurable_code`, `measurable_decode`).
* `iso_code_iff`: isomorphism of codes is **preserved and reflected** by `code`; the two
  directions are `code_preserves_iso` and `code_reflects_iso`.

The carrier `ℕ` and the relation interpretations do not change.  Formula transport is in
`Descriptive/SmallVocabularyLift.lean`.  The descriptive consequences are deferred to a separate
transport module.
-/

@[expose] public section

universe u v

namespace FirstOrder.Language

/-- Each arity's relation symbols are countable when their sigma type is. -/
instance instCountableRelationsOfSigma (L : Language.{u, v}) [Countable (Σ n, L.Relations n)]
    (n : ℕ) : Countable (L.Relations n) :=
  (show Function.Injective (fun R : L.Relations n => (⟨n, R⟩ : Σ n, L.Relations n))
    from fun _ _ h => by injection h).countable

namespace SmallVocabulary

variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- The chosen small presentation: relation symbols of each arity shrunk into `Type 0`, no
function symbols. -/
noncomputable def lang : Language.{0, 0} where
  Functions _ := Empty
  Relations n := Shrink.{0} (L.Relations n)

instance : (lang L).IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance (n : ℕ) : Countable ((lang L).Relations n) :=
  (equivShrink.{0, v} (L.Relations n)).symm.injective.countable

instance : Countable (Σ n, (lang L).Relations n) := inferInstance

/-- The renaming of an arity-`n` relation symbol into the small presentation. -/
noncomputable abbrev shrinkRel (n : ℕ) : L.Relations n ≃ (lang L).Relations n :=
  equivShrink.{0, v} (L.Relations n)

/-- **The decoding homomorphism** from the small presentation to `L` (symbols only). -/
noncomputable def toLang : lang L →ᴸ L where
  onFunction := fun {_} f => isEmptyElim f
  onRelation := fun {n} R => (shrinkRel L n).symm R

omit [L.IsRelational] in
@[simp] theorem toLang_onRelation {n : ℕ} (R : (lang L).Relations n) :
    (toLang L).onRelation R = (shrinkRel L n).symm R := rfl

/-! ### Codes -/

/-- A code of `L` read as a code of the small presentation. -/
noncomputable def code (c : StructureSpace L) : StructureSpace (lang L) :=
  fun q => c ⟨⟨q.1.1, (shrinkRel L q.1.1).symm q.1.2⟩, q.2⟩

/-- A code of the small presentation read as a code of `L`. -/
noncomputable def decode (c : StructureSpace (lang L)) : StructureSpace L :=
  fun q => c ⟨⟨q.1.1, shrinkRel L q.1.1 q.1.2⟩, q.2⟩

omit [L.IsRelational] in
@[simp] theorem code_apply (c : StructureSpace L) {n : ℕ} (R : (lang L).Relations n)
    (a : Fin n → ℕ) : code L c ⟨⟨n, R⟩, a⟩ = c ⟨⟨n, (shrinkRel L n).symm R⟩, a⟩ := rfl

omit [L.IsRelational] in
@[simp] theorem decode_apply (c : StructureSpace (lang L)) {n : ℕ} (R : L.Relations n)
    (a : Fin n → ℕ) : decode L c ⟨⟨n, R⟩, a⟩ = c ⟨⟨n, shrinkRel L n R⟩, a⟩ := rfl

omit [L.IsRelational] in
@[simp] theorem decode_code (c : StructureSpace L) : decode L (code L c) = c := by
  funext ⟨⟨n, R⟩, a⟩
  exact congrArg (fun S : L.Relations n => c ⟨⟨n, S⟩, a⟩) ((shrinkRel L n).symm_apply_apply R)

omit [L.IsRelational] in
@[simp] theorem code_decode (c : StructureSpace (lang L)) : code L (decode L c) = c := by
  funext ⟨⟨n, R⟩, a⟩
  exact congrArg (fun S : (lang L).Relations n => c ⟨⟨n, S⟩, a⟩)
    ((shrinkRel L n).apply_symm_apply R)

omit [L.IsRelational] in
theorem continuous_code : Continuous (code L) :=
  continuous_pi fun _ => continuous_apply _

omit [L.IsRelational] in
theorem continuous_decode : Continuous (decode L) :=
  continuous_pi fun _ => continuous_apply _

omit [L.IsRelational] in
/-- **The code homeomorphism** between the structure spaces of `L` and of its small
presentation. -/
noncomputable def codeHomeomorph : StructureSpace L ≃ₜ StructureSpace (lang L) where
  toFun := code L
  invFun := decode L
  left_inv := decode_code L
  right_inv := code_decode L
  continuous_toFun := continuous_code L
  continuous_invFun := continuous_decode L

omit [L.IsRelational] in
@[simp] theorem codeHomeomorph_apply (c : StructureSpace L) : codeHomeomorph L c = code L c := rfl

omit [L.IsRelational] in
@[simp] theorem codeHomeomorph_symm_apply (c : StructureSpace (lang L)) :
    (codeHomeomorph L).symm c = decode L c := rfl

/-! ### Isomorphism is preserved and reflected -/

end SmallVocabulary

end FirstOrder.Language
