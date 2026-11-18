/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.SetTheory.Cardinal.Regular
public import InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction
public import InfinitaryLogic.Lomega1omega.Theory
public import InfinitaryLogic.Methods.GeneratedSublanguage
public import InfinitaryLogic.Methods.ConstantSupport
public import InfinitaryLogic.Methods.Henkin.Construction

/-!
# The Marker stage: finite-fragment support extraction and Erdős–Rado certification

First layer of the template/consistency-property reshape of the Morley–Hanf chain (the
replacement for the ZFC-refutable in-`M` extraction ladder — see the audit fences on
`PureColoringHypothesis`/`MorleyHanfExtraction` in `Conditional/MorleyHanfTransfer.lean`).
Following Marker, *Lectures on Infinitary Model Theory* §5.2, the consistency-property route
certifies each **finite** fragment of an `L'[[J]]` template/constant theory by a large
homogeneous set in the source model, with the indiscernible sequence materializing only in
the model built by Model Existence.

This file provides the syntactic/combinatorial bridge between "finite fragment of a
constant theory" and "finite-arity Erdős–Rado approximation":

* a finite fragment is presented by its **index data** — a finite family of pairs
  `(fml p : L'.BoundedFormulaω Empty (ar p), tup p : Fin (ar p) ↪o J)` (per the template
  machinery in `Methods/EM/Realization.lean`, membership in a template theory carries
  exactly this witness data, so no syntactic support extraction is ever needed);
* `exists_markerSupport_factor` — collect the finite `J`-constant support of the family,
  enumerate it as `enum : Fin k ↪o J`, and factor every `tup p` through `enum`
  (via `exists_orderEmbedding_factor`);
* `markerStage_homogeneous` — pull the family back to a single arity-`k` truth-vector
  coloring over the source model and apply `finiteArityHomogeneousUpTo_beth_stage`:
  for every `α < ω₁`, a source of size `≥ ℶ_{ω₁}` yields a `(ℶ_α)⁺`-suborder on which the
  truth vector of the whole fragment is tuple-independent.

The per-`α` conclusion (available for **every** `α < ω₁` at once) is the Marker schedule.

## Layer 2: the certification predicates and their closure calculus

Toward the Marker consistency property, this file also provides the candidate member
predicate and its easy closure lemmas:

* `sentenceJConsts` — the syntactic `J`-constant support of an `L'[[J]]`-sentence (a `Set J`
  carved out of `functionsIn`; only countable in general, finite exactly for the sentences
  the construction certifies — support finiteness is *demanded* by the predicate, never
  computed);
* `MarkerFiniteCert M α F` — a finite set of sentences is certified at level `α`: a common
  finite support `S`, a `(ℶ_α)⁺`-suborder `e` of `M`, and satisfaction of every member under
  every constant interpretation that is increasing on `S` into `e`'s range;
* `MarkerCofinalConsistent M Sset` — every finite subset is certified at cofinally many
  `α < ω₁` (finite character makes weakening and chain closure pleasant);
* the closure lemmas that need **no** uniform countable choice: weakening, chain closure,
  the `C0` pair (no falsum, no contradiction), `C2` (double negation), `C3` (conjunction
  components), `C4'` (negated-disjunction components) — each by replacing the derived
  sentence with its trigger inside the certified fragment
  (`MarkerCofinalConsistent.extend_of_semantic`) and pushing pointwise `realize` lemmas
  through the same interpretations;
* `exists_uniform_of_cofinal_countable` — the `ω₁`-pigeonhole engine (ω₁ is regular, so a
  countably-colored cofinal α-schedule has a monochromatic cofinal subschedule);
* `MarkerISupUniform` — **the stated hard test**: does `⋁ᵢ φᵢ ∈ Sset` yield ONE disjunct
  `k` with `Sset ∪ {φs k}` still cofinally consistent? Per finite fragment `F` and level
  `α`, re-homogenization + the pigeonhole produce `k(F)`; the open question is uniformizing
  over ALL finite `F ⊆ Sset` — a directed intersection of antitone nonempty subsets of `ℕ`,
  which is NOT automatic. If provable, `markerConsistencyPropertyEq` is mostly assembly; if
  not, the fallback is a finite-member consistency notion with its own Henkin/model-existence
  adapter (the existing `ConsistencyPropertyEq` API also demands `extension` for ARBITRARY
  sentences, which certification cannot supply for sentences of infinite support — another
  reason the finite-member adapter may be the honest endpoint).

**C7/Henkin witness design (SETTLED: Henkin constant expansion — see Layer 3):** over a
relational `L'`, the closed `L'[[J]]`-terms are exactly the `J`-constants, so quantifier
witnesses must be fresh constants; a fresh `J`-constant would have to occupy a specific
order-position that an arbitrary linear `J` need not offer, so witnesses live in a separate
layer `(L'[[J]])[[ℕ]]` instead (`henkinConst`, `henkinConstsIn`, `expJConstsIn`), with the
reduct lemma (`Theoryω.model_reduct_of_expansion`) returning the final model to `L'[[J]]`.
The finite-member predicates over the expansion (`MarkerHenkinCert`,
`MarkerHenkinConsistent`, Layer 5) avoid the arbitrary-set `extension` field and the global
`C4` uniformization entirely — the Henkin construction consumes finite members along its
enumeration, per the classical Marker/Keisler shape. The `realizeWith` API (Layer 4)
confines all structure instances to two definition bodies; every closure rule is stated
through it. The choice-free closure rules (`C0`/`C1'`/`C2`/`C3`/`C4'`) are proved in
Layer 5; remaining: the re-homogenization rules (`C1`, `C3'`, `C4` — per-member
branch/index choice by coloring support tuples inside the certificate), `C7` via a fresh
witness index (enabled by the finite-Henkin-support invariant — see the Layer 5 audit
note), then the Henkin construction/model-existence adapter decision.
-/

@[expose] public section

universe u

namespace FirstOrder.Language

open Cardinal

/-! ## Layer 2: the certification predicates -/

section Certification

variable {L' : Language.{0, 0}} {J : Type}

-- `sentenceJConsts` and its monotonicity calculus (`_not`, `_component_iInf`,
-- `_component_iSup`, `_imp_left`, `_imp_right`) now live in `Methods/ConstantSupport.lean`,
-- the neutral home of the constant-support calculus (imported above). This section consumes
-- them unchanged.

variable [LinearOrder J] (M : Type) [L'.Structure M] [LinearOrder M]

/-- **The per-level Marker certification of a finite fragment**: a common finite constant
support `S`, a `(ℶ_α)⁺`-suborder `e` of the (well-ordered) source `M`, and satisfaction of
every member sentence under every constant interpretation that is strictly increasing on
`S` with values in the range of `e`. This is Marker's "`ℶ_α`-large set realizing `σ`",
stated semantically over interpretations so that the closure calculus needs no constructor
inversion through the template pipeline. -/
def MarkerFiniteCert (α : Ordinal.{0}) (F : Set L'[[J]].Sentenceω) : Prop :=
  ∃ S : Finset J, (∀ τ ∈ F, sentenceJConsts (L' := L') τ ⊆ ↑S) ∧
    ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
      ∀ σ : J → M, StrictMonoOn σ ↑S → (∀ j ∈ S, σ j ∈ Set.range e) →
        letI : (constantsOn J).Structure M := constantsOn.structure σ
        ∀ τ ∈ F, Sentenceω.Realize τ M

variable {M}

end Certification

/-! ## The ω₁-pigeonhole engine and the stated uniformization test -/

variable {L' : Language.{0, 0}} {J : Type} [LinearOrder J]

/-! ## Layer 3: the Henkin-witness substrate

**C7 design decision (settled): Henkin constant expansion.** Quantifier witnesses live in a
separate `withConstants` layer `(L'[[J]])[[ℕ]]`, NOT among the `J`-constants: an arbitrary
linear `J` need not have an element in the order-gap a witness would require (and
`MorleySeedTailTemplateRealizable` quantifies over every linear `J`); a relational `L'`
provides no closed terms beyond constants, so witnesses cannot be generated internally; and
a separate layer keeps the EM skeleton (`J`, order-positioned, universally quantified in
certification) apart from proof-theoretic witnesses (`ℕ`, existentially interpreted per
skeleton interpretation). The finite-member consistency predicate lives over the expansion;
the endpoint returns to `L'[[J]]` by the reduct lemma. -/

section HenkinSubstrate

variable {L'' : Language.{0, 0}} {J : Type}

/-- The `n`-th Henkin witness constant of a constant expansion `L[[ℕ]]`, as a closed term. -/
def henkinConst {L : Language.{0, 0}} (n : ℕ) : (L[[ℕ]]).Term Empty :=
  Term.func (Sum.inr n : (L[[ℕ]]).Functions 0) Fin.elim0

/-- The Henkin-constant support of an expansion formula — the generalized `sentenceJConsts`
at base `L'[[J]]` and constant type `ℕ`. Freshness of a witness index `n` for a fragment
`F` is `∀ τ ∈ F, n ∉ henkinConstsIn τ`. -/
abbrev henkinConstsIn {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) : Set ℕ :=
  sentenceJConsts (L' := L''[[J]]) (J := ℕ) φ

/-- The `J`-constant support of an expansion formula: the `J`-constants sit inside the base
`L''[[J]]` layer, under `Sum.inl ∘ Sum.inr`. -/
def expJConstsIn {α : Type} {n : ℕ} (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) : Set J :=
  {j | (⟨0, (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0)⟩ :
      Σ n, ((L''[[J]])[[ℕ]]).Functions n) ∈ BoundedFormulaω.functionsIn φ}

-- (The finite-member predicates `MarkerHenkinCert`/`MarkerHenkinConsistent` live in
-- Layer 5 below, stated through the `realizeWith` API of Layer 4.)

end HenkinSubstrate

/-! ## Layer 4: the `realizeWith` evaluation API and the constant-agreement congruence

All structure instances are confined to the two wrapper definitions; every lemma statement
mentions only the wrappers, so no local-instance synthesis ever leaks into downstream
theorem statements. All later Marker closure rules are to be stated through this API. -/

section RealizeWith

variable {L'' : Language.{0, 0}} {J : Type} {M : Type} [L''.Structure M]

/-- Evaluation of an expansion term under a skeleton interpretation `σ : J → M` and a
Henkin interpretation `h : ℕ → M`. -/
def termValueWith (σ : J → M) (h : ℕ → M) {β : Type}
    (t : ((L''[[J]])[[ℕ]]).Term β) (v : β → M) : M :=
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  letI : (constantsOn ℕ).Structure M := constantsOn.structure h
  t.realize v

/-- Realization of an expansion formula under a skeleton interpretation `σ : J → M` and a
Henkin interpretation `h : ℕ → M`. -/
def realizeWith (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) : Prop :=
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  letI : (constantsOn ℕ).Structure M := constantsOn.structure h
  φ.Realize v xs

/-! ### Constructor unfolds (term level) -/

@[simp] theorem termValueWith_var (σ : J → M) (h : ℕ → M) {β : Type} (x : β) (v : β → M) :
    termValueWith (L'' := L'') σ h (Term.var x) v = v x := rfl

@[simp] theorem termValueWith_base (σ : J → M) (h : ℕ → M) {β : Type} {l : ℕ}
    (f : L''.Functions l) (ts : Fin l → ((L''[[J]])[[ℕ]]).Term β) (v : β → M) :
    termValueWith σ h (Term.func (Sum.inl (Sum.inl f)) ts) v =
      Structure.funMap f (fun i => termValueWith σ h (ts i) v) := rfl

@[simp] theorem termValueWith_skeleton (σ : J → M) (h : ℕ → M) {β : Type} (j : J)
    (ts : Fin 0 → ((L''[[J]])[[ℕ]]).Term β) (v : β → M) :
    termValueWith σ h
      (Term.func (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0) ts) v = σ j := rfl

@[simp] theorem termValueWith_henkin (σ : J → M) (h : ℕ → M) {β : Type} (m : ℕ)
    (ts : Fin 0 → ((L''[[J]])[[ℕ]]).Term β) (v : β → M) :
    termValueWith σ h
      (Term.func (Sum.inr m : ((L''[[J]])[[ℕ]]).Functions 0) ts) v = h m := rfl

@[simp] theorem termValueWith_henkinConst (σ : J → M) (h : ℕ → M) (m : ℕ)
    (v : Empty → M) :
    termValueWith σ h (henkinConst (L := L''[[J]]) m) v = h m := rfl

/-! ### Constructor unfolds (formula level) -/

/-- The base relation symbol behind an expansion relation symbol (the constant layers add
no relations). -/
def baseRel {l : ℕ} : ((L''[[J]])[[ℕ]]).Relations l → L''.Relations l
  | Sum.inl (Sum.inl R) => R
  | Sum.inl (Sum.inr e) => e.elim
  | Sum.inr e => e.elim

@[simp] theorem realizeWith_falsum (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (v : α → M) (xs : Fin n → M) :
    realizeWith (L'' := L'') σ h BoundedFormulaω.falsum v xs ↔ False := Iff.rfl

@[simp] theorem realizeWith_equal (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (t₁ t₂ : ((L''[[J]])[[ℕ]]).Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.equal t₁ t₂) v xs ↔
      termValueWith σ h t₁ (Sum.elim v xs) = termValueWith σ h t₂ (Sum.elim v xs) :=
  Iff.rfl

@[simp] theorem realizeWith_rel (σ : J → M) (h : ℕ → M) {α : Type} {n l : ℕ}
    (R : ((L''[[J]])[[ℕ]]).Relations l) (ts : Fin l → ((L''[[J]])[[ℕ]]).Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.rel R ts) v xs ↔
      Structure.RelMap (baseRel (L'' := L'') R)
        (fun i => termValueWith σ h (ts i) (Sum.elim v xs)) := by
  rcases R with (R | e) | e
  · exact Iff.rfl
  · exact e.elim
  · exact e.elim

@[simp] theorem realizeWith_imp (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ ψ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (φ.imp ψ) v xs ↔ (realizeWith σ h φ v xs → realizeWith σ h ψ v xs) :=
  Iff.rfl

@[simp] theorem realizeWith_all (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α (n + 1)) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ.all v xs ↔ ∀ x, realizeWith σ h φ v (Fin.snoc xs x) := Iff.rfl

@[simp] theorem realizeWith_iSup (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.iSup φs) v xs ↔
      ∃ i, realizeWith σ h (φs i) v xs := Iff.rfl

@[simp] theorem realizeWith_iInf (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φs : ℕ → ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h (BoundedFormulaω.iInf φs) v xs ↔
      ∀ i, realizeWith σ h (φs i) v xs := Iff.rfl

@[simp] theorem realizeWith_not (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ.not v xs ↔ ¬realizeWith σ h φ v xs := Iff.rfl

@[simp] theorem realizeWith_ex (σ : J → M) (h : ℕ → M) {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α (n + 1)) (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ.ex v xs ↔ ∃ x, realizeWith σ h φ v (Fin.snoc xs x) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure h
  exact BoundedFormulaω.realize_ex φ

/-! ### The constant-agreement congruence -/

/-- **Term congruence**: two skeleton interpretations agreeing on the occurring skeleton
constants and two Henkin interpretations agreeing on the occurring witness constants give
every term the same value. -/
theorem termValueWith_congr {σ σ' : J → M} {h h' : ℕ → M} {β : Type}
    (t : ((L''[[J]])[[ℕ]]).Term β)
    (hσ : ∀ j : J, (⟨0, (Sum.inl (Sum.inr j) : ((L''[[J]])[[ℕ]]).Functions 0)⟩ :
        Σ l, ((L''[[J]])[[ℕ]]).Functions l) ∈ Term.functionsIn t → σ j = σ' j)
    (hh : ∀ m : ℕ, (⟨0, (Sum.inr m : ((L''[[J]])[[ℕ]]).Functions 0)⟩ :
        Σ l, ((L''[[J]])[[ℕ]]).Functions l) ∈ Term.functionsIn t → h m = h' m)
    (v : β → M) :
    termValueWith σ h t v = termValueWith σ' h' t v := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    have hmem : ∀ (i : Fin l) (s : Σ l, ((L''[[J]])[[ℕ]]).Functions l),
        s ∈ Term.functionsIn (ts i) → s ∈ Term.functionsIn (Term.func f ts) := by
      intro i s hs
      simp only [Term.functionsIn]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion.mpr ⟨i, hs⟩))
    have hhead : (⟨l, f⟩ : Σ l, ((L''[[J]])[[ℕ]]).Functions l) ∈
        Term.functionsIn (Term.func f ts) := by
      simp only [Term.functionsIn]
      exact Set.mem_insert _ _
    have hargs : ∀ i, termValueWith σ h (ts i) v = termValueWith σ' h' (ts i) v :=
      fun i => ih i (fun j hj => hσ j (hmem i _ hj)) (fun m hm => hh m (hmem i _ hm))
    rcases f with (f | c) | c
    · rw [termValueWith_base, termValueWith_base]
      exact congrArg _ (funext hargs)
    · cases l with
      -- `termValueWith_skeleton` is `rfl`, and its `j : J` cannot be unified with
      -- `c : (constantsOn J).Functions 0` at `implicit` transparency; `exact` checks at default.
      | zero => exact hσ c hhead
      | succ l => exact c.elim
    · cases l with
      | zero => exact hh c hhead
      | succ l => exact c.elim

/-- **Formula congruence** — the semantic-support engine of the Marker construction:
agreement on the occurring skeleton constants (`expJConstsIn`) and witness constants
(`henkinConstsIn`) gives identical realization. This is what makes tuple-canonical
colorings well-defined (`C4` re-homogenization) and fresh witness indices harmless
(`C7`). -/
theorem realizeWith_congr {σ σ' : J → M} {h h' : ℕ → M} {α : Type} {n : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α n)
    (hσ : ∀ j ∈ expJConstsIn (L'' := L'') φ, σ j = σ' j)
    (hh : ∀ m ∈ henkinConstsIn (L'' := L'') φ, h m = h' m)
    (v : α → M) (xs : Fin n → M) :
    realizeWith σ h φ v xs ↔ realizeWith σ' h' φ v xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    rw [realizeWith_equal, realizeWith_equal,
      termValueWith_congr t₁
        (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn]
          exact Set.mem_union_left _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn]
          exact Set.mem_union_left _ hm)) _,
      termValueWith_congr t₂
        (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn]
          exact Set.mem_union_right _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn]
          exact Set.mem_union_right _ hm)) _]
  | rel R ts =>
    rw [realizeWith_rel, realizeWith_rel]
    exact iff_of_eq (congrArg _ (funext fun i =>
      termValueWith_congr (ts i)
        (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn]
          exact Set.mem_iUnion.mpr ⟨i, hj⟩))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn]
          exact Set.mem_iUnion.mpr ⟨i, hm⟩)) _))
  | imp φ ψ ihφ ihψ =>
    rw [realizeWith_imp, realizeWith_imp,
      ihφ (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_union_left _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_union_left _ hm)),
      ihψ (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_union_right _ hj))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_union_right _ hm))]
  | all φ ih =>
    rw [realizeWith_all, realizeWith_all]
    exact forall_congr' fun x => ih hσ hh (Fin.snoc xs x)
  | iSup φs ih =>
    rw [realizeWith_iSup, realizeWith_iSup]
    exact exists_congr fun i =>
      ih i (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_iUnion.mpr ⟨i, hj⟩))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_iUnion.mpr ⟨i, hm⟩)) xs
  | iInf φs ih =>
    rw [realizeWith_iInf, realizeWith_iInf]
    exact forall_congr' fun i =>
      ih i (fun j hj => hσ j (by
          simp only [expJConstsIn, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn] at hj ⊢
          exact Set.mem_iUnion.mpr ⟨i, hj⟩))
        (fun m hm => hh m (by
          simp only [henkinConstsIn, sentenceJConsts, Set.mem_ofPred_eq,
            BoundedFormulaω.functionsIn] at hm ⊢
          exact Set.mem_iUnion.mpr ⟨i, hm⟩)) xs

end RealizeWith

-- The generic `functionsIn` structural calculus (relabel / castLE / subst / openBounds /
-- finiteness / subset-under-subst) now lives in `Methods/ConstantSupport.lean` (imported
-- above), the neutral home of the constant-support calculus. Consumed here unchanged.

/-! ## Layer 5: the finite Henkin closure calculus

**The freshness audit gate (settled by strengthening the predicate):** `henkinConstsIn` is
not automatically finite for an arbitrary `Lω₁ω` sentence — `iSup`/`iInf` can mention
countably many witness constants (e.g. `⋁ₙ (dₙ = dₙ)` has Henkin support all of `ℕ`) — so
"pick a fresh witness index outside the fragment's Henkin support" needs an invariant.
`MarkerHenkinCert` therefore carries a finite Henkin support `H : Finset ℕ` alongside the
skeleton support `S : Finset J`. The invariant is self-maintaining and non-restrictive:
the construction's seed sentences are `mapLanguage`-images of `L'[[J]]`-sentences (Henkin
support `∅`), and every closure operation shrinks the support (components, negations,
implication branches) or grows it by finitely many constants (substitution instances) —
an infinite-support sentence never enters a member of the Henkin enumeration. -/

section FiniteClosure

variable {L'' : Language.{0, 0}} {J : Type}

/-! ### Support lemmas for the expansion's skeleton constants -/

/-! ### Support lemmas for the expansion's Henkin constants (wrappers around the generic
`sentenceJConsts` family, restated so `rw` matches the `henkinConstsIn` spelling) -/

/-! ### The finite-member predicates -/

variable [LinearOrder J] (M : Type) [L''.Structure M] [LinearOrder M]

/-- **The certificate body at an explicit skeleton support `S`**: a `(ℶ_α)⁺`-suborder `e` of
the source, and — for EVERY skeleton interpretation increasing on `S` into `e`'s range —
SOME Henkin interpretation making every member true. The skeleton side stays universal (the
EM tuples); the witness side is existential per interpretation, because quantifier witnesses
vary with the tuple. The support-tracking conjuncts live in the wrapping predicates. -/
def MarkerHenkinBody (α : Ordinal.{0}) (S : Finset J)
    (F : Set ((L''[[J]])[[ℕ]].Sentenceω)) : Prop :=
  ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
    ∀ σ : J → M, StrictMonoOn σ ↑S → (∀ j ∈ S, σ j ∈ Set.range e) →
      ∃ h : ℕ → M, ∀ τ ∈ F, realizeWith σ h τ (Empty.elim : Empty → M) Fin.elim0

variable {M}

/-! ### Layer 5b engine: re-homogenization

The reusable machinery for the branch/index choice rules (`C1`, `C3'`, `C4`): color the
support tuples of a high-level certificate body by the branch a realizing interpretation
selects, re-homogenize inside the existing suborder via `finiteArityHomogeneousUpTo_beth_stage`
at a level lower by the finite ladder cost `2·|S|+2`, and read off a uniform branch. -/

section Rehomogenize

open Cardinal

variable {D : Type} [LinearOrder D]

/-! ### Layer 5b-2: the branch/index choice rules -/

/-! ### Layer 5c: the Henkin witness rule (C7)

The one closure rule of a different shape: no re-homogenization, but a fresh Henkin constant.
From `∃x φ(x) ∈ F`, pick a witness index `n` outside the finite Henkin support `H`, update the
Henkin interpretation at `n` to the existential witness (per skeleton interpretation), and
adjoin the instance `φ(dₙ)`. The finite-support invariant is what makes "fresh `n`" available. -/

/-- The Henkin witness instance of an existential: `φ` with its last bound variable filled by
the `n`-th Henkin constant. -/
noncomputable def witnessSentence
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) : ((L''[[J]])[[ℕ]]).Sentenceω :=
  (φ.openBounds).subst (fun _ => henkinConst n)

omit [LinearOrder J] in
/-- `∃` does not change the mentioned function symbols. -/
theorem functionsIn_ex {α : Type} {m : ℕ}
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω α (m + 1)) :
    BoundedFormulaω.functionsIn φ.ex = BoundedFormulaω.functionsIn φ := by
  simp [BoundedFormulaω.functionsIn]

omit [LinearOrder J] in
theorem henkinConstsIn_ex (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) :
    henkinConstsIn (L'' := L'') φ.ex = henkinConstsIn (L'' := L'') φ := by
  simp only [henkinConstsIn, sentenceJConsts, functionsIn_ex]

omit [LinearOrder J] [LinearOrder M] in
/-- **The semantic bridge**: realizing the witness sentence is realizing `φ` with the last
bound variable set to the Henkin interpretation of `dₙ`. -/
theorem realizeWith_witness (σ : J → M) (h : ℕ → M)
    (φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1) (n : ℕ) :
    realizeWith σ h (witnessSentence φ n) (Empty.elim : Empty → M) Fin.elim0 ↔
      realizeWith σ h φ (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 (h n)) := by
  let : (constantsOn J).Structure M := constantsOn.structure σ
  let : (constantsOn ℕ).Structure M := constantsOn.structure h
  show ((φ.openBounds).subst (fun _ => henkinConst n)).Realize (Empty.elim : Empty → M) Fin.elim0 ↔
    φ.Realize (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 (h n))
  rw [BoundedFormulaω.realize_subst]
  refine (realize_openBounds φ _).trans (iff_of_eq ?_)
  congr 1

/-- **Body-level `C7`**: from `∃x φ(x) ∈ F` and a Henkin index `n` fresh for `F`, the witness
instance can be adjoined — update the Henkin interpretation at `n` to the existential witness;
`n`'s freshness leaves every old member unchanged (`realizeWith_congr`). -/
theorem MarkerHenkinBody.witness {α : Ordinal.{0}} {S : Finset J}
    {F : Set ((L''[[J]])[[ℕ]].Sentenceω)} (hb : MarkerHenkinBody M α S F)
    {φ : ((L''[[J]])[[ℕ]]).BoundedFormulaω Empty 1} (hmem : φ.ex ∈ F) (n : ℕ)
    (hn : ∀ τ ∈ F, n ∉ henkinConstsIn (L'' := L'') τ) :
    MarkerHenkinBody M α S (insert (witnessSentence φ n) F) := by
  obtain ⟨e, hsat⟩ := hb
  refine ⟨e, fun σ hσmono hσrange => ?_⟩
  obtain ⟨h, hh⟩ := hsat σ hσmono hσrange
  have hex := hh φ.ex hmem
  rw [realizeWith_ex] at hex
  obtain ⟨x, hx⟩ := hex
  have hnφ : n ∉ henkinConstsIn (L'' := L'') φ := by
    rw [← henkinConstsIn_ex]; exact hn φ.ex hmem
  refine ⟨Function.update h n x, ?_⟩
  rintro τ (rfl | hτ)
  · rw [realizeWith_witness, Function.update_self]
    exact (realizeWith_congr φ (fun _ _ => rfl)
      (fun m hm => Function.update_of_ne (ne_of_mem_of_not_mem hm hnφ) x h) _ _).mpr hx
  · exact (realizeWith_congr τ (fun _ _ => rfl)
      (fun m hm => Function.update_of_ne (ne_of_mem_of_not_mem hm (hn τ hτ)) x h) _ _).mpr
      (hh τ hτ)

end Rehomogenize

/-! ## Layer 6a: the finite-support universe and the restricted extension rule

The bespoke finite-Henkin adapter avoids the ambient `ConsistencyPropertyEq` (whose
`extension` field quantifies over ARBITRARY sentences, which Marker consistency cannot
supply at infinite constant-support). Instead it works over the sentences of finite constant
support — exactly the sentences the Marker recursion from the template seed ever produces —
and replaces the arbitrary-sentence `extension` field with a restricted extension rule proved
by the same Layer-5b re-homogenization engine (branch over `Bool`, colour support tuples by
whether `τ` is realized). -/

/-! ## Layer 6b: the equality closure rules (C5/C6)

The equality rules the term-model quotient and truth lemma will need on the restricted
maximal theory. Both are proved semantically (certification is realizability in `M`, whose
equality is genuine) via unconditional/entailed insertion, with finite constant support
tracked through the syntactic support API. -/

/-! ## Layer 6c: the maximal finite-support theory (Zorn)

The finite closure calculus (C0–C7) is turned into a complete theory over the finite-support
universe by a finite-character Zorn argument, mirroring `ConsistencyProperty.chain_closure`
but with completeness only for finite-support sentences — exactly what the restricted truth
lemma will need. Parameterized by a consistent seed (the base consistency hook is a separate
cross-file integration; the abstract machinery here fixes the shape it must feed). -/

variable (M)

variable {M}

/-! ### Membership calculus of the maximal theory -/

end FiniteClosure

end FirstOrder.Language
