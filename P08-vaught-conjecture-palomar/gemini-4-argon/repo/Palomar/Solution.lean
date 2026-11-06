/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExpansionDomainEndpoint

/-!
# Proof of the independent infinitary counterexample statement

This module deliberately does not import Challenge: its conventional infinitary
syntax and semantics are supplied by the proof library instead. Comparator must
compare their actual definitions as well as the final theorem. The finite model
and perfect-set assertions use the same sentence as the cardinality assertion.

This module consumes the migrated proof closure. Verification of the full migrated
package and its independent replay are prerequisites for submission.
-/

@[expose] public section

namespace PalomarChallenge

variable (R : ℕ → Type 1)

/-- A purely relational language, with no functions or constants. -/
def language : FirstOrder.Language := ⟨fun _ => Empty, R⟩

instance : (language R).IsRelational := fun _ => (inferInstance : IsEmpty Empty)

/-- A relation symbol together with a tuple of arguments. -/
abbrev RelQueryOn (M : Type) := Σ r : (Σ n, R n), (Fin r.1 → M)

/-- A Boolean relation truth table. -/
abbrev Code (M : Type) := RelQueryOn R M → Bool

/-- Codes for structures on the natural numbers. -/
abbrev StructureSpace := Code R ℕ

/-- Decode every relation coordinate. -/
@[instance_reducible]
def structureOfCode {M : Type} (c : Code R M) : (language R).Structure M where
  funMap f := isEmptyElim f
  RelMap {n} r xs := c ⟨⟨n, r⟩, xs⟩ = true

/-- Ordinary satisfaction in the decoded structure. -/
def Satisfies {M : Type} (φ : (language R).Sentenceω) (c : Code R M) : Prop :=
  letI := structureOfCode R c
  FirstOrder.Language.BoundedFormulaInf.Realize (M := M) φ Empty.elim Fin.elim0

/-- Isomorphism by a permutation preserving every relation truth value. -/
def Isomorphic (c d : Code R ℕ) : Prop :=
  ∃ e : ℕ ≃ ℕ, ∀ n (r : R n) (xs : Fin n → ℕ), c ⟨⟨n, r⟩, xs⟩ = d ⟨⟨n, r⟩, e ∘ xs⟩

theorem isomorphic_equivalence : Equivalence (Isomorphic R) := ⟨
    fun c => ⟨Equiv.refl ℕ, fun _ _ _ => rfl⟩,
    by
      rintro c d ⟨e, h⟩
      refine ⟨e.symm, fun n r xs => ?_⟩
      simpa [Function.comp_def] using (h n r (e.symm ∘ xs)).symm,
    by
      rintro c d f ⟨e, h⟩ ⟨e', h'⟩
      exact ⟨e.trans e', fun n r xs => (h n r xs).trans (h' n r (e ∘ xs))⟩⟩

/-- The genuine equivalence relation on codes. -/
def isoSetoid : Setoid (Code R ℕ) := ⟨Isomorphic R, isomorphic_equivalence R⟩

/-- Actual models, not arbitrary codes or chosen representatives. -/
abbrev NatModel (φ : (language R).Sentenceω) := {c : Code R ℕ // Satisfies R φ c}

/-- Isomorphism restricted to the models. -/
def modelSetoid (φ : (language R).Sentenceω) : Setoid (NatModel R φ) :=
  Setoid.comap Subtype.val (isoSetoid R)

/-- Isomorphism classes of models. -/
abbrev IsoClasses (φ : (language R).Sentenceω) := Quotient (modelSetoid R φ)

/-- No finite coded model, including on the empty carrier. -/
def NoFiniteModels (φ : (language R).Sentenceω) : Prop :=
  ∀ n (c : Code R (Fin n)), ¬ Satisfies R φ c

/-- Thinness in the ordinary product topology on Boolean relation coordinates. -/
def NoPerfectAntichain (φ : (language R).Sentenceω) : Prop :=
  ¬ ∃ P : Set (StructureSpace R), P.Nonempty ∧ Perfect P ∧
    (∀ c ∈ P, Satisfies R φ c) ∧
      ∀ c ∈ P, ∀ d ∈ P, c ≠ d → ¬ Isomorphic R c d

open FirstOrder.Language VaughtConjecture.Knight

/-- The ordinary permutation definition agrees with the library's structure isomorphisms. -/
theorem isomorphic_iff_library (c d : Code knightLang.Relations ℕ) :
    Isomorphic knightLang.Relations c d ↔
      (structureIsoSetoid knightLang).r c d :=
  ⟨fun ⟨e, h⟩ => ⟨@FirstOrder.Language.Equiv.mk knightLang ℕ ℕ
    (StructureSpaceOn.toStructure c) (StructureSpaceOn.toStructure d) e isEmptyElim
    fun {n} r xs => by change d ⟨⟨n, r⟩, e ∘ xs⟩ = true ↔ c ⟨⟨n, r⟩, xs⟩ = true; rw [h]⟩,
   fun ⟨e⟩ => ⟨@FirstOrder.Language.Equiv.toEquiv knightLang ℕ ℕ
    (StructureSpaceOn.toStructure c) (StructureSpaceOn.toStructure d) e,
    fun n r xs => Bool.eq_iff_iff.mpr
      (@FirstOrder.Language.Equiv.map_rel' knightLang ℕ ℕ
        (StructureSpaceOn.toStructure c) (StructureSpaceOn.toStructure d) e n r xs).symm⟩⟩

/-- A countable relational infinitary sentence with exact spectrum and CH-independent thinness. -/
theorem independent_challenge :
    ∃ (R : ℕ → Type 1) (_ : Countable (Σ n, R n)) (φ : (language R).Sentenceω),
      Cardinal.mk (IsoClasses R φ) = Cardinal.aleph 1 ∧
      NoFiniteModels R φ ∧ NoPerfectAntichain R φ := by
  refine ⟨knightLang.Relations, knightLang.countable_relations, knightSentence, ?_,
    fun n c hc => ?_, fun ⟨P, hne, hp, hm, ha⟩ => ExpansionDomainEndpoint.isThinOnNatModels
      ⟨P, hp, hne, hm, fun c hc d hd hcd => not_not.mp fun h =>
        ha c hc d hd h ((isomorphic_iff_library c d).mpr hcd)⟩⟩
  · change Cardinal.mk (Quotient (modelSetoid knightLang.Relations knightSentence)) = _
    rw [show modelSetoid knightLang.Relations knightSentence =
        FirstOrder.Language.isoSetoid knightSentence from
      Setoid.ext fun c d => isomorphic_iff_library c.1 d.1]
    exact ExpansionDomainEndpoint.natModelSpectrum_eq_aleph_one
  · have hmem : c ∈ ModelsOfOn (α := Fin n) knightSentence := hc
    rwa [hasNoFiniteModels_knightSentence n] at hmem
