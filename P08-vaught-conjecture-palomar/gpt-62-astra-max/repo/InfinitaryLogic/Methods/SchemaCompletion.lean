/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Methods.SchemaOmegaWitness
public import InfinitaryLogic.Methods.LanguageMapOccurrence
public import InfinitaryLogic.Methods.MarkerStage

/-!
# Layer 7b, checkpoint 1: the countable schema sentence universe

The ω-stage Henkin/template completion (Layer 7) is carried out at the **schema level**, over
the canonical countable index `J := ℕ` (the indiscernible-sequence positions `d₀, d₁, …`), where
the sentence set the completion ranges over is genuinely countable — unlike the uncountable
`L'[[J]]`-constant instances for arbitrary `J` that defeated the Layer-6c Zorn maximal.

This file fixes the **schema sentence universe**: the set of `(localColim s₀)[[ℕ]]`-sentences the
enumeration in checkpoint 3 will decide. A crucial simplification, established in
`SchemaOmegaWitness`, drives the shape: the target witness property
`TailTemplateOmegaWitnessed`/`OmegaCompleteForColim` has **only `iSup`/`iInf` clauses, no
existential** (the local-EM de-substituted formulas are already Skolemized). Since `ΓlocalColim`
— hence `ΓEMlocal` — is closed under `iSup`/`iInf` components
(`iSup_component_mem_ΓlocalColim`), every disjunct a completion might choose as a witness is
**already** a member of the seed family. So the universe is exactly the `templateSentence`
instantiations of the `ΓEMlocal` members at `ℕ`-tuples:

* the seed family `ΓEMlocal s₀` is **countable** (`ΓEMlocal_countable`);
* for each member `⟨m, φ⟩`, the increasing `ℕ`-tuples `t : Fin m ↪o ℕ` form a **countable** type
  (they inject into `Fin m → ℕ`);
* `templateSentence φ t` is the `L[[ℕ]]`-sentence "`φ` holds on `d_{t 0}, …, d_{t (m-1)}`".

`schemaSentenceUniverse_countable` is the checkpoint-1 payoff (the completion's decision list is
enumerable); `schemaSentenceUniverse_nonempty` supplies the base point the enumeration needs.
No completion, Zorn, term model, or `realizeWith` bridge appears here — this checkpoint only
pins the countable substrate.
-/

@[expose] public section

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage}

/-- Increasing `ℕ`-tuples of any fixed length are countable: the coercion to `Fin m → ℕ` is
injective, and `Fin m → ℕ` is countable. -/
instance instCountableFinOrderEmbNat (m : ℕ) : Countable (Fin m ↪o ℕ) :=
  (DFunLike.coe_injective (F := Fin m ↪o ℕ) (α := Fin m) (β := fun _ => ℕ)).countable

/-! ## Checkpoint 2, step 1: the template-realization bridge

Connects MarkerStage's `realizeWith` (over the double Henkin expansion `((L''[[J]])[[ℕ]])`) to the
`templateSentence` semantics: the schema sentence `templateSentence ψ t`, lifted into the Marker
language along the Henkin inclusion, is `realizeWith`-true under a skeleton interpretation `σ`
exactly when `ψ` holds on the `σ`-images `i ↦ σ (t i)` of its constants. The Henkin layer is inert
(no Henkin constants occur). This is the semantic content the base certification (step 3) and the
seed agreement (7c) both consume. Stated generically in `L''`/`J`, so the two `constantsOn`
instances of `realizeWith` stay unambiguous (as at its definition site). -/

section TemplateBridge

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J] {M : Type} [L''.Structure M]

end TemplateBridge

/-! ## Checkpoint 2: the empty base is Marker-consistent

The ω-stage completion (checkpoint 3) starts from the empty theory and decides every schema
sentence's sign via the already-proved `MarkerHenkinConsistent.extension` (which internally
homogenizes through `markerStage_homogeneous`). Since `schemaSentenceUniverse` is a *decision
list* — its canonical atoms include both true and false instances (e.g. `x₀ = x₁`) — the base is
NOT "all universe sentences are true"; it is the trivially-realizable empty fragment. The Morley
seed `{φ, x₀ ≠ x₁}` needs no explicit seeding: `extension` is forced to pick `φ` (its negation is
incompatible with `M ⊨ φ`) and distinctness (its negation is incompatible with the strictly
increasing skeleton interpretations). -/

section EmptyBase

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J]
  {M : Type} [L''.Structure M] [LinearOrder M] [WellFoundedLT M]

end EmptyBase

/-! ## Checkpoint 3a: the lifted universe and its `FSentence` membership

The ω-stage completion runs over `((localColim s₀)[[ℕ]])[[ℕ]]` (`FSentence`), so the universe must
be lifted along the same Henkin inclusion as the bridge. Two `functionsIn`-under-`mapLanguage`
facts (absent from the existing `relabel`/`subst`/`openBounds` API) drive the constant-support
computation: lifting sends every function symbol to its `Sum.inl` image, so it produces **no**
Henkin constants and preserves the skeleton-constant support. A lifted `templateSentence ψ t` then
has finite constant support `image t` (and empty Henkin support) — regardless of how many base
function symbols the (possibly `iSup`-branching) `ψ` uses, because `HasFiniteConstSupport` bounds
only the *constant* symbols, never all of `functionsIn`. -/

section FunctionsInMapLanguage

variable {L L' : Language.{0, 0}} (g : L →ᴸ L')

end FunctionsInMapLanguage

section HenkinLiftSupport

variable {L'' : Language.{0, 0}} {J : Type}

end HenkinLiftSupport

section TemplateSupport

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J]

end TemplateSupport

section LiftedUniverse

variable {s₀ : LocalStage}

end LiftedUniverse

/-! ## Checkpoint 3b: the ω-stage completion (subtype recursion)

A constructive Henkin enumeration over `ρ : ℕ → FSentence`. Each `stageStep` decides `ρ n` via
`extension` (branching on decidable consistency of the positive insert — `extension`'s `∨` is a
`Prop` and cannot eliminate into the `Subtype`), and, opportunistically and locally, adjoins the
connective witness of the decided sign: a positive `iSup` gets a disjunct via `iSup_choice`, a
negative `iInf` gets a refuted conjunct via `neg_iInf_choice`. The step carries the balanced
disjunction `(positive ∧ iSup-witnessed) ∨ (negative ∧ neg-iInf-witnessed)`, so the per-stage
facts 3c consumes are projections — no global classifier, no "φ ∉ F" discharge. The negative
witness is NOT recoverable from finite consistency after the theory is formed (a finite
fragment's body can falsify a component the fragment does not mention, so the failing component
drifts with the body); it must be pinned here, at decision time. -/

section Completion

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M]

variable (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

end Completion

/-! ## Checkpoint 3c: the union theory

The completed theory `T = ⋃ₙ (schemaCompletionStage ρ hM n).1`, kept as a raw set of Marker
sentences. Finite-character consistency (a finite subset lands in one stage), completeness on the
universe (each `ρ n` decided at its stage), and — the `iSup`-witness closure — will bundle into
`SchemaCompletionTheorySpec`. -/

section Union

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M]

variable
  (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

end Union

/-! ## Checkpoint 5b-1, part 1: the finite interpolation engine

Tuple uniformity (part 2) needs, for two length-`m` increasing tuples `t t'` into `ℕ` and ONE
certificate body, two admissible skeleton interpretations `σ₁ σ₂` whose tuple images agree:
`σ₁ ∘ t = σ₂ ∘ t'`. The engine is a global equalizer on `ℕ`: strictly monotone `q q' : ℕ → ℕ`
sending the anchors `p i`/`p' i` to the common value `p i + p' i` — `q` shifts by the largest
passed `p'`-anchor (a `Finset.sup` over a filter), so no piecewise case analysis is needed.
`exists_admissible_pair` threads the equalized values through a `Fin K`-suborder of the
(infinite) certificate domain. Crucially, `MarkerHenkinBody` constrains `σ` only ON the support
`S`, so the tuples need not lie in `S`: they enter only the auxiliary bounding set that picks
`K` — the Marker support itself is never enlarged. -/

section Interpolation

end Interpolation

/-! ## Checkpoint 5b-1, part 2: tuple uniformity

The completed schema theory decides a template sentence's sign **by its `ΓEMlocal` body alone**,
uniformly across the instantiating tuples: `schemaLift ψ t ∈ Tσ ↔ schemaLift ψ t' ∈ Tσ`. This is
the internal form of Marker §5.2's indiscernibility-equivalence axioms, and it is what makes the
term model's canonical sequence genuinely indiscernible for the completed schema (5b-3).

The proof is the honest two-interpretation argument: if `ψ t` is in and `ψ t'` is out, then (by
completeness on the universe) `{schemaLift ψ u, (schemaLift ψ v).not}` is a finite subset of the
theory, hence `MarkerHenkinConsistent`; its ONE certificate body is universal over admissible
skeleton interpretations, so it applies separately to the `exists_admissible_pair` pair
`σ₁, σ₂` — the first realizes `ψ` on `σ₁ ∘ t`, the second refutes `ψ` on `σ₂ ∘ t'`, and those
tuples are EQUAL. No single interpretation is asked to equalize both tuples (strictness would
forbid it); no Henkin witness dependence arises on this single-expansion path. -/

section TupleUniform

variable {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

end TupleUniform

/-! ## Checkpoint 5b-2: connective witnesses for canonical deForms

`TailTemplateOmegaWitnessed` — the 5b-3 target — is stated on `canonDeForm (localColim s₀) φ g`,
not on the raw `ΓlocalColim` connectives, so the completed theory's witness closures must be
exposed in exactly those terms. Both directions are corollaries of the universe-level closures:
`canonDeForm` and `schemaLift` each distribute over `iSup`/`iInf` definitionally, and
`canonDeForm_mem_ΓEMlocal` puts the deForm in the universe. The negative direction is the whole
point of the completion repair: the fixed refuted conjunct was pinned at decision time and is
simply read off here. -/

section CanonDeFormWitness

variable {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

end CanonDeFormWitness

end FirstOrder.Language
