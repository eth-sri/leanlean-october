/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ChartLanguage
public import VaughtConjecture.Spectrum.Sentence
public import InfinitaryLogic.Lomega1omega.Semantics

/-! # Knight's sentence `T` in `L_{ω₁,ω}` (Def. 3.3.1–3.3.4), via `InfinitaryLogic`

Knight, §3.3: the language `L` (Def. 3.3.1) has, for each `n`, one `n`-ary relation symbol
`P_p` per stage-`ω` type `p ∈ S^ω_n`; the sentence `T` (Def. 3.3.3) says that the relations
`P_p` describe a model of `S^ω` (Def. 3.2.1, `Knight.Model`): the tuples carry at most one
type, types are consistent under restriction, every tuple extends to a typed one, and the four
existential-closure families are served.  Prop. 3.3.5 (the countable models of `T` correspond to
the countable models of `S^ω`): the sentence-side half — the two directions of the
correspondence between `L`-structures and `KnightRealization`s, clause by clause — is here; the
isomorphism-class bookkeeping is `Knight/Correspondence.lean` (#43).

**Language** (`knightLang : Language.{0, 1}`): relational, `Relations n := S ω n` (stage `ω`,
`omegaStage : LimitStage`), no function symbols; countable (`countable_S_omega`, Prop. 3.1.4
at `ω`), as `InfinitaryLogic`'s `StructureSpace` requires.

**Enumeration.**  `L_{ω₁,ω}` conjunctions and disjunctions over the countable parameter spaces
of Def. 3.3.3 — arities, stage-`ω` types `S ω n`, embeddings `Fin m ↪ Fin n`, domains
`SemScheme (n+1)`, ordinals below `ω` — are `einf`/`esup` (`InfinitaryLogic`) along the
enumeration `Encodable.ofCountable` of the (countable) index type: `cinf`/`csup` below, with
`realize_cinf`/`realize_csup`.  This replaces Knight-VC's `IFormula` constructors
`forallType`/`existsType` over relation symbols (`PORTING.md`).  Clause (a)(ii) is parameterized
in the paper by a labelling `q' : D → {−∞} ∪ Ord ∪ {∞}` — **uncountably** many — but the
family it requests, `BottomPatternFamily D q'`, depends on `q'` only through its `−∞`-pattern
on the finitely many cells of `D^{≤n}`; so the clause is written as a countable conjunction
over the **patterns** `π : D^{≤n} → Bool` for which some faithful `q'` extending `p` has pattern
`π` (`BottomPatternParam p`, `IsPatternOf`), a faithful re-encoding of the paper's
parameterization (`realize_bottomPatternClause` is stated in the paper's `q'` form).

**The sentence.**  One definition per clause — `nonemptyClause` (the carrier is nonempty, Def.
3.2.1's standing convention), `arityClause` (Def. 3.2.1(1): `P_p` holds only on injective
tuples), `consistencyClause` (Def. 3.2.1(2), exact: `P_p(x̄) → (P_q(x̄∘f) ⇔ S^ω f (p) = q)`; at
`f = id` this is "at most one type per tuple"), `coveringClause` (Def. 3.2.1(3), initial
segment), and the four existential-closure clauses `genSatClause`, `bottomPatternClause`,
`uniformityClause`, `highGradeDominanceClause` (Def. 3.2.1(4)(a)(i), (a)(ii), (b), (c)), all
instances of one shape `ecClause`: `∀ x̄, P_p(x̄) → ⋀_{params} ⋁_{q ∈ U, q a coface of p} ∃ y,
P_q(x̄⌢y)` — and `knightSentence`, their conjunction.

**Realization lemmas.**  Each clause has `realize_<clause>`, the semantic condition on an
`L`-structure `M` (`Holds p xs` is `P_p(x̄)`); `IsKnightModel M` bundles the eight conditions,
and `realize_knightSentence_iff : M ⊨ω knightSentence ↔ IsKnightModel M`.  The correspondence
shape: `toRealization M : KnightRealization omegaStage M` (the type of a tuple is the relation
holding on it) with `IsKnightModel.isModel_toRealization`, and `structureOf R : knightLang.Structure
M` for a realization `R` with `IsModel.isKnightModel`; both round-trip
(`toRealization_structureOf_eval`, `holds_structureOf_toRealization`).  Hence every countable
model of `T` is (the structure of) a model of `S^ω` and conversely; the isomorphism-class
bookkeeping (`isoSetoid`, `codeModel`, `AllCodedIsoClasses`) is `Knight/Correspondence.lean` (#43).

**No finite models.**  `hasNoFiniteModels_knightSentence : HasNoFiniteModels knightSentence`:
a structure realizing `T` is a model of `S^ω`, and every model is infinite
(`KnightRealization.IsModel.infinite_carrier`: covering labels the empty tuple and
existential closure
(4)(c) at `γ = 0` adds a fresh point to every labelled tuple) — no domain construction (#41)
is involved. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower
open scoped Lomega1omega

universe u w

/-! ### Stage `ω` and the language -/

/-- The limit stage `ω`: Knight's sentence describes the models of `S^ω` (Def. 3.3.3). -/
def omegaStage : LimitStage := ⟨Ordinal.omega0, Ordinal.isSuccLimit_omega0⟩

/-- Every limit stage lies above `ω`: the theory's language is a reduct of every chart
language. -/
theorem omegaStage_le (α : LimitStage) : omegaStage ≤ α :=
  Ordinal.omega0_le_of_isSuccLimit α.2

/-- The stage-`ω` types are countable (Prop. 3.1.4 at `ω`: `ω` is a countable ordinal). -/
instance countable_S_omega (n : ℕ) : Countable (S Ordinal.omega0 n) :=
  StageType.countable_S Ordinal.card_omega0.le n

/-- **Knight's language** `L` (Def. 3.3.1): relational, with one `n`-ary relation symbol `P_p`
per stage-`ω` type `p ∈ S^ω_n`, and no function symbols.  `S ω n : Type 1`, so the language
lives in `Language.{0, 1}`.  This is (definitionally) the `α = ω` case of the stage chart
language (`stageLang`, `Knight/ChartLanguage.lean`, #137). -/
def knightLang : Language.{0, 1} := stageLang omegaStage

instance knightLang.isRelational : knightLang.IsRelational :=
  stageLang.isRelational omegaStage

/-- The language is countable (as `InfinitaryLogic`'s coding space requires). -/
instance knightLang.countable_relations : Countable (Σ l, knightLang.Relations l) :=
  inferInstanceAs (Countable (Σ l, S Ordinal.omega0 l))

/-- `P_p(x̄)` holds in the `L`-structure `M`. -/
abbrev Holds {M : Type w} [knightLang.Structure M] {n : ℕ} (p : S Ordinal.omega0 n)
    (xs : Fin n → M) : Prop :=
  RelMap (L := knightLang) (n := n) p xs

/-! ### Formulas: countable connectives along the enumeration, atoms, tuples -/

/-- Formulas of `L` with `n` bound-variable slots and no free variables. -/
abbrev KnightFormula (n : ℕ) := knightLang.BoundedFormulaω Empty n

/-- Countable conjunction `⋀_{i : ι}` over a countable index type, as `einf` along the
enumeration `Encodable.ofCountable ι`. -/
def cinf {n : ℕ} {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    KnightFormula n :=
  BoundedFormulaω.einfWith (Encodable.ofCountable ι) φs

/-- Countable disjunction `⋁_{i : ι}` over a countable index type, as `esup` along the
enumeration `Encodable.ofCountable ι`. -/
def csup {n : ℕ} {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    KnightFormula n :=
  BoundedFormulaω.esupWith (Encodable.ofCountable ι) φs

/-- The atomic formula `P_p(x_{f 0}, …, x_{f (m-1)})` on the bound variables. -/
def atom {m n : ℕ} (p : S Ordinal.omega0 m) (f : Fin m → Fin n) : KnightFormula n :=
  BoundedFormulaω.rel (L := knightLang) (l := m) p fun i => Term.var (Sum.inr (f i))

/-- `⋀_{i ≠ j} x_i ≠ x_j`: the bound variables are pairwise distinct. -/
def distinct (n : ℕ) : KnightFormula n :=
  cinf fun ij : {ij : Fin n × Fin n // ij.1 ≠ ij.2} =>
    ∼ω (BoundedFormulaω.equal (Term.var (Sum.inr ij.1.1)) (Term.var (Sum.inr ij.1.2)))

/-- `∃ y₀ … y_{k-1}`: existential quantification over the last `k` bound variables. -/
def exsFrom {n : ℕ} : ∀ k : ℕ, KnightFormula (n + k) → KnightFormula n
  | 0, φ => φ
  | k + 1, φ => exsFrom k (BoundedFormulaω.ex φ)

section Realize

variable {M : Type w} [knightLang.Structure M] {n : ℕ} {v : Empty → M} {xs : Fin n → M}

@[simp] theorem realize_cinf {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    (cinf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaω.realize_einfWith _ φs

@[simp] theorem realize_csup {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    (csup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaω.realize_esupWith _ φs

@[simp] theorem realize_atom {m : ℕ} (p : S Ordinal.omega0 m) (f : Fin m → Fin n) :
    (atom p f).Realize v xs ↔ Holds p (xs ∘ f) :=
  Iff.rfl

@[simp] theorem realize_distinct :
    (distinct n).Realize v xs ↔ Function.Injective xs := by
  simp only [distinct, realize_cinf, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
    Term.realize_var, Sum.elim_inr, Subtype.forall, Prod.forall]
  exact ⟨fun h i j hij => by_contra fun hne => h i j hne hij, fun h i j hne hij => hne (h hij)⟩

/-- Realization of the universal closure of all bound variables (Mathlib's `alls`) at the
empty tuple. -/
theorem realize_alls (φ : KnightFormula n) :
    BoundedFormulaω.Realize φ.alls v Fin.elim0 ↔ ∀ ys : Fin n → M, φ.Realize v ys :=
  BoundedFormulaInf.realize_alls

@[simp] theorem realize_exsFrom (k : ℕ) (φ : KnightFormula (n + k)) :
    (exsFrom k φ).Realize v xs ↔ ∃ ys : Fin k → M, φ.Realize v (Fin.append xs ys) := by
  induction k with
  | zero =>
    have h (ys : Fin 0 → M) : Fin.append xs ys = xs :=
      funext fun i => by rw [Subsingleton.elim ys Fin.elim0, Fin.append_elim0]; rfl
    simp [exsFrom, h]
  | succ k ih =>
    simp only [exsFrom, ih, BoundedFormulaω.realize_ex]
    exact ⟨fun ⟨ys, y, h⟩ => ⟨Fin.snoc ys y, by rwa [Fin.append_snoc]⟩,
      fun ⟨ys, h⟩ => ⟨Fin.init ys, ys (Fin.last k), by rwa [← Fin.append_snoc, Fin.snoc_init_self]⟩⟩

end Realize

/-! ### The clauses of `T` (Def. 3.3.3) -/

/-- The carrier is nonempty (`∃ x, ⊤`): the standing convention "a model with domain `M`"
(`KnightRealization.IsModel.nonempty`). -/
def nonemptyClause : knightLang.Sentenceω :=
  BoundedFormulaω.ex (⊤ : KnightFormula 1)

/-- **Arity** (Def. 3.2.1(1)): `∀ x̄, P_p(x̄) → ⋀_{i ≠ j} x_i ≠ x_j` — a type is carried only by
injective tuples (in a `KnightRealization` this is automatic from the encoding). -/
def arityClause : knightLang.Sentenceω :=
  cinf fun n : ℕ => cinf fun p : S Ordinal.omega0 n => (atom p id ⟹ω distinct n).alls

open Classical in
/-- **Consistency** (Def. 3.2.1(2), exact): for all `n`, `p ∈ S^ω_n`, `f : m ↪ n` and
`q ∈ S^ω_m`, `∀ x̄, P_p(x̄) → (P_q(x̄∘f) ⇔ [S^ω f (p) = q])`: the type of the face `x̄∘f` is
exactly the partial restriction of the type of `x̄` — `P_q(x̄∘f)` when `typeMap f p = some q`,
`¬ P_{q'}(x̄∘f)` for every other `q'` (in particular for every `q'` when the face is invisible,
`typeMap f p = none`).  At `f = id` (`typeMap_refl`) this is "at most one type per tuple"
(`IsKnightModel.unique`). -/
def consistencyClause : knightLang.Sentenceω :=
  cinf fun n : ℕ => cinf fun p : S Ordinal.omega0 n => cinf fun mf : Σ m : ℕ, Fin m ↪ Fin n =>
    cinf fun q : S Ordinal.omega0 mf.1 =>
      (atom p id ⟹ω
        (if typeMap mf.2 p = some q then atom q mf.2 else ∼ω (atom q mf.2))).alls

/-- **Covering** (Def. 3.2.1(3), initial segment): `∀ x̄ injective, ⋁_k ∃ ȳ ⋁_{p ∈ S^ω_{n+k}}
P_p(x̄⌢ȳ)`. -/
def coveringClause : knightLang.Sentenceω :=
  cinf fun n : ℕ =>
    (distinct n ⟹ω
      csup fun k : ℕ => exsFrom k (csup fun p : S Ordinal.omega0 (n + k) => atom p id)).alls

/-- The request `⋁_{q ∈ U, q a coface of p} ∃ y, P_q(x̄⌢y)` (the conclusion of Def. 3.2.1(4)
for the family `U ⊆ (S^ω ι_{n,n+1})⁻¹(p)`). -/
def requestFormula {n : ℕ} (p : S Ordinal.omega0 n)
    (U : Set (S Ordinal.omega0 (n + 1))) : KnightFormula n :=
  csup fun q : {q : S Ordinal.omega0 (n + 1) // q ∈ U ∧ IsCoface p q} =>
    BoundedFormulaω.ex (atom q.1 id)

/-- The common shape of the four **existential-closure** clauses (Def. 3.2.1(4)): for a countable
parameter space `Param n p` and families `U n p a`, `⋀_n ⋀_p ∀ x̄, P_p(x̄) → ⋀_{a : Param n p}
⋁_{q ∈ U n p a, coface of p} ∃ y, P_q(x̄⌢y)`. -/
def ecClause (Param : ∀ n : ℕ, S Ordinal.omega0 n → Type u)
    [∀ n p, Countable (Param n p)]
    (U : ∀ (n : ℕ) (p : S Ordinal.omega0 n), Param n p → Set (S Ordinal.omega0 (n + 1))) :
    knightLang.Sentenceω :=
  cinf fun n : ℕ => cinf fun p : S Ordinal.omega0 n =>
    (atom p id ⟹ω cinf fun a : Param n p => requestFormula p (U n p a)).alls

/-- **(a)(i) Generalised saturation**: parameters `D` a domain on `n+1` with `D⟨n,n⟩ = dom p`
(`ExtendsDomain`), family `GenSatFamily D`. -/
def genSatClause : knightLang.Sentenceω :=
  ecClause (fun n p => {D : SemScheme (n + 1) // ExtendsDomain p D})
    (fun _ _ D => GenSatFamily D.1)

/-- A `−∞`-pattern on `D^{≤ n} = D⟨A, n⟩` (the cells of grade `≤ n`). -/
abbrev BotPattern {n : ℕ} (D : SemScheme (n + 1)) : Type :=
  D.scheme.below (Finset.univ, n) → Bool

/-- The cofaces with domain `D` and `−∞`-pattern `π` on `D^{≤ n}`. -/
def PatternFamily {n : ℕ} (D : SemScheme (n + 1)) (π : BotPattern D) :
    Set (S Ordinal.omega0 (n + 1)) :=
  {q | ∃ h : q.scheme = D, ∀ Θ : D.scheme.below (Finset.univ, n),
    q.label (SemScheme.castCell h.symm Θ.1) = ⊥ ↔ π Θ = true}

/-- `BottomPatternFamily D q'` depends on `q'` only through its `−∞`-pattern. -/
theorem bottomPatternFamily_eq_patternFamily {n : ℕ} {D : SemScheme (n + 1)}
    (q' : Cell D.scheme → ExtOrd) (π : BotPattern D) (hπ : ∀ Θ, q' Θ.1 = ⊥ ↔ π Θ = true) :
    BottomPatternFamily (α := Ordinal.omega0) D q' = PatternFamily D π := by
  ext q
  simp only [BottomPatternFamily, PatternFamily, Set.mem_ofPred_eq, hπ]

/-- `π` is the `−∞`-pattern of some labelling `q'` of `D` respecting the semantics of `D`
(faithfully, no stage bound) and extending `p` along the initial face — the paper's parameter
of Def. 3.2.1(4)(a)(ii), seen through its pattern. -/
def IsPatternOf {n : ℕ} (p : S Ordinal.omega0 n) (D : SemScheme (n + 1)) (π : BotPattern D) :
    Prop :=
  ∃ hD : ExtendsDomain p D, ∃ q' : Cell D.scheme → ExtOrd,
    RespectsSemantics D.rows q' ∧ (∀ d, q' (hD.cellOf d) = p.label d) ∧
      ∀ Θ, (q' Θ.1 = ⊥ ↔ π Θ = true)

/-- The parameter space of clause (a)(ii) as written here: domains `D` extending `dom p` with
a `−∞`-pattern realized by some faithful `q'` extending `p`.  Countable (finitely many patterns
per domain, countably many domains) — the paper's parameter `q'` ranges over uncountably many
labellings, but only its pattern matters (`bottomPatternFamily_eq_patternFamily`). -/
def BottomPatternParam {n : ℕ} (p : S Ordinal.omega0 n) : Type 1 :=
  {Dπ : Σ D : SemScheme (n + 1), BotPattern D // IsPatternOf p Dπ.1 Dπ.2}

instance {n : ℕ} (p : S Ordinal.omega0 n) : Countable (BottomPatternParam p) := by
  unfold BottomPatternParam
  infer_instance

/-- **(a)(ii) Prescribed `−∞`-pattern**: parameters `(D, π)` with `π` the pattern of a faithful
`q'` extending `p`, family `PatternFamily D π = BottomPatternFamily D q'`. -/
def bottomPatternClause : knightLang.Sentenceω :=
  ecClause (fun _ p => BottomPatternParam p) (fun _ _ Dπ => PatternFamily Dπ.1.1 Dπ.1.2)

/-- **(b) Uniformity**: parameters the non-successor ordinals `γ < ω` (i.e. `γ = 0`, indexed by
`{k : ℕ // IsNonSuccessor k}` — every `γ < ω` is a natural number), family
`UniformityFamily γ`. -/
def uniformityClause : knightLang.Sentenceω :=
  ecClause (fun _ _ => {k : ℕ // Value.IsNonSuccessor (k : Ordinal.{0})})
    (fun _ _ k => UniformityFamily (k.1 : Ordinal.{0}))

/-- **(c) High-grade dominance**: parameters `γ < ω` (indexed by `ℕ`), family
`HighGradeDominanceFamily γ`. -/
def highGradeDominanceClause : knightLang.Sentenceω :=
  ecClause (fun _ _ => ℕ) (fun _ _ k => HighGradeDominanceFamily (k : Ordinal.{0}))

/-- **Knight's sentence `T`** (Def. 3.3.3): the conjunction of the clauses. -/
def knightSentence : knightLang.Sentenceω :=
  nonemptyClause ⊓ arityClause ⊓ consistencyClause ⊓ coveringClause ⊓ genSatClause ⊓
    bottomPatternClause ⊓ uniformityClause ⊓ highGradeDominanceClause

/-! ### Clause-wise realization -/

section Realize

variable {M : Type w} [knightLang.Structure M]

/-- The semantic form of the request `requestFormula p U` over the tuple `xs`: some `y` and some
`q ∈ U`, a coface of `p`, with `P_q(xs⌢y)` (the structure-side `RealizesSome`). -/
def RelRealizesSome {n : ℕ} (xs : Fin n → M) (p : S Ordinal.omega0 n)
    (U : Set (S Ordinal.omega0 (n + 1))) : Prop :=
  ∃ (y : M) (q : S Ordinal.omega0 (n + 1)), q ∈ U ∧ IsCoface p q ∧ Holds q (Fin.snoc xs y)

variable {n : ℕ} {v : Empty → M} {xs : Fin n → M}

@[simp] theorem realize_requestFormula (p : S Ordinal.omega0 n)
    (U : Set (S Ordinal.omega0 (n + 1))) :
    (requestFormula p U).Realize v xs ↔ RelRealizesSome xs p U := by
  simp only [requestFormula, realize_csup, BoundedFormulaω.realize_ex, realize_atom,
    Function.comp_id, RelRealizesSome, Subtype.exists]
  exact ⟨fun ⟨q, ⟨hU, hc⟩, y, hy⟩ => ⟨y, q, hU, hc, hy⟩,
    fun ⟨y, q, hU, hc, hy⟩ => ⟨q, ⟨hU, hc⟩, y, hy⟩⟩

variable (M)

/-- The semantic content of `T` on an `L`-structure `M`: the eight clauses, realized.  This is
the structure-side counterpart of `KnightRealization.IsModel` (the two correspond:
`IsKnightModel.isModel_toRealization`, `IsModel.isKnightModel`). -/
structure IsKnightModel : Prop where
  /-- The carrier is nonempty. -/
  nonempty : Nonempty M
  /-- Clause (1): a type is carried only by injective tuples. -/
  arity : ∀ {n : ℕ} (p : S Ordinal.omega0 n) (xs : Fin n → M), Holds p xs →
    Function.Injective xs
  /-- Clause (2), exact: the type of a face is the partial restriction. -/
  consistent : ∀ {n : ℕ} (p : S Ordinal.omega0 n) (xs : Fin n → M), Holds p xs →
    ∀ {m : ℕ} (f : Fin m ↪ Fin n) (q : S Ordinal.omega0 m),
      Holds q (xs ∘ f) ↔ typeMap f p = some q
  /-- Clause (3): every injective tuple is an initial segment of a typed one. -/
  covering : ∀ {n : ℕ} (xs : Fin n → M), Function.Injective xs →
    ∃ (k : ℕ) (ys : Fin k → M) (p : S Ordinal.omega0 (n + k)), Holds p (Fin.append xs ys)
  /-- Clause (4)(a)(i). -/
  genSat : ∀ {n : ℕ} (p : S Ordinal.omega0 n) (xs : Fin n → M), Holds p xs →
    ∀ D : SemScheme (n + 1), ExtendsDomain p D → RelRealizesSome xs p (GenSatFamily D)
  /-- Clause (4)(a)(ii), in the paper's parameterization. -/
  bottomPattern : ∀ {n : ℕ} (p : S Ordinal.omega0 n) (xs : Fin n → M), Holds p xs →
    ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd),
      RespectsSemantics D.rows q' → (∀ d, q' (hD.cellOf d) = p.label d) →
      RelRealizesSome xs p (BottomPatternFamily D q')
  /-- Clause (4)(b). -/
  uniformity : ∀ {n : ℕ} (p : S Ordinal.omega0 n) (xs : Fin n → M), Holds p xs →
    ∀ γ : Ordinal.{0}, Value.IsNonSuccessor γ → γ < Ordinal.omega0 →
      RelRealizesSome xs p (UniformityFamily γ)
  /-- Clause (4)(c). -/
  highGradeDominance : ∀ {n : ℕ} (p : S Ordinal.omega0 n) (xs : Fin n → M), Holds p xs →
    ∀ γ : Ordinal.{0}, γ < Ordinal.omega0 → RelRealizesSome xs p (HighGradeDominanceFamily γ)

/-- **Realization of `T`**: `M ⊨ T` iff the eight clauses hold in `M`. -/
theorem realize_knightSentence_iff : knightSentence.Realize M ↔ IsKnightModel M := by
  simp only [knightSentence, Sentenceω.realize_def, BoundedFormulaω.realize_inf, and_assoc,
    nonemptyClause, BoundedFormulaω.realize_ex, BoundedFormulaω.realize_top,
    arityClause, consistencyClause, coveringClause, genSatClause, bottomPatternClause,
    uniformityClause, highGradeDominanceClause, ecClause, realize_cinf, realize_alls,
    BoundedFormulaω.realize_imp, realize_atom, Function.comp_id, realize_distinct, realize_csup,
    realize_exsFrom, realize_requestFormula, Sigma.forall, Subtype.forall]
  constructor
  · rintro ⟨⟨x, _⟩, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    refine ⟨⟨x⟩, fun p xs hp => h₂ _ p xs hp, fun p xs hp m f q => ?_, fun xs => h₄ _ xs,
      fun p xs hp D hD => h₅ _ p xs hp D hD, fun p xs hp D hD q' hq' hext => ?_,
      fun p xs hp γ hγ hlt => ?_, fun p xs hp γ hlt => ?_⟩
    · have := h₃ _ p m f q xs hp
      split_ifs at this with hc
      · exact ⟨fun _ => hc, fun _ => this⟩
      · rw [BoundedFormulaω.realize_not, realize_atom] at this
        exact ⟨fun h' => absurd h' this, fun h' => absurd h' hc⟩
    · classical
      simpa only [bottomPatternFamily_eq_patternFamily q' _ (fun _ => decide_eq_true_iff.symm)] using
        h₆ _ p xs hp ⟨⟨D, fun Θ => decide (q' Θ.1 = ⊥)⟩, hD, q', hq', hext,
          fun _ => decide_eq_true_iff.symm⟩
    · obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hlt; exact h₇ _ p xs hp k hγ
    · obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hlt; exact h₈ _ p xs hp k
  · rintro ⟨⟨x⟩, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    refine ⟨⟨x, trivial⟩, fun _ p xs hp => h₂ p xs hp, fun n p m f q xs hp => ?_,
      fun _ xs => h₄ xs, fun _ p xs hp D hD => h₅ p xs hp D hD,
      fun _ p xs hp ⟨⟨D, π⟩, hD, q', hq', hext, hπ⟩ =>
        bottomPatternFamily_eq_patternFamily q' π hπ ▸ h₆ p xs hp D hD q' hq' hext,
      fun _ p xs hp k hk => h₇ p xs hp k hk (Ordinal.natCast_lt_omega0 k),
      fun _ p xs hp k => h₈ p xs hp k (Ordinal.natCast_lt_omega0 k)⟩
    split_ifs with hc
    · exact (h₃ p xs hp f q).mpr hc
    · rw [BoundedFormulaω.realize_not, realize_atom]
      exact fun h' => hc ((h₃ p xs hp f q).mp h')

variable {M}

/-- At most one type per tuple: the instance `f = id` of the consistency clause. -/
theorem IsKnightModel.unique (h : IsKnightModel M) {n : ℕ} {p p' : S Ordinal.omega0 n}
    {xs : Fin n → M} (hp : Holds p xs) (hp' : Holds p' xs) : p' = p := by
  have := (h.consistent p xs hp (Function.Embedding.refl (Fin n)) p').mp
    (by simpa only [Function.Embedding.coe_refl, Function.comp_id] using hp')
  rw [typeMap_refl, Option.some.injEq] at this
  exact this.symm

end Realize

/-! ### From structures to realizations and back -/

section Correspondence

variable (M : Type w) [knightLang.Structure M]

open Classical in
/-- The Knight realization of an `L`-structure: the type of an injective tuple is the type `p`
with `P_p(x̄)`, if any (chosen; unique under the consistency clause,
`toRealization_eval_eq_some_iff`). -/
def toRealization : KnightRealization omegaStage M where
  eval {n} t := if h : ∃ p : S Ordinal.omega0 n, Holds p ⇑t then some h.choose else none

variable {M}

theorem toRealization_eval_eq_none_iff {n : ℕ} (t : Fin n ↪ M) :
    (toRealization M).eval t = none ↔ ∀ p : S Ordinal.omega0 n, ¬ Holds p ⇑t := by
  dsimp only [toRealization]
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]; exact h
  · simpa using h

theorem toRealization_eval_isSome_iff {n : ℕ} (t : Fin n ↪ M) :
    ((toRealization M).eval t).isSome ↔ ∃ p : S Ordinal.omega0 n, Holds p ⇑t := by
  simp only [← Option.ne_none_iff_isSome, Ne, toRealization_eval_eq_none_iff, not_forall, not_not]

/-- Under "at most one type per tuple", the type of `t` is the `p` with `P_p(t)`. -/
theorem toRealization_eval_eq_some_iff
    (hu : ∀ {n : ℕ} {p p' : S Ordinal.omega0 n} {xs : Fin n → M}, Holds p xs → Holds p' xs →
      p' = p)
    {n : ℕ} (t : Fin n ↪ M) (p : S Ordinal.omega0 n) :
    (toRealization M).eval t = some p ↔ Holds p ⇑t := by
  dsimp only [toRealization]
  split_ifs with h
  · exact ⟨fun hp => Option.some.inj hp ▸ h.choose_spec,
      fun hp => congrArg some (hu hp h.choose_spec)⟩
  · exact ⟨fun hp => hp.elim, fun hp => h ⟨p, hp⟩⟩

/-- Under the clauses of `T`, the type of `t` in `toRealization M` is the `p` with `P_p(t)`. -/
theorem IsKnightModel.eval_eq_some_iff (h : IsKnightModel M) {n : ℕ} (t : Fin n ↪ M)
    (p : S Ordinal.omega0 n) : (toRealization M).eval t = some p ↔ Holds p ⇑t :=
  toRealization_eval_eq_some_iff (fun hp hp' => h.unique hp hp') t p

omit [knightLang.Structure M] in
/-- A point off an injective `snoc` is off the tuple. -/
theorem notMem_range_of_injective_snoc {n : ℕ} {t : Fin n → M} {y : M}
    (h : Function.Injective (Fin.snoc t y : Fin (n + 1) → M)) : y ∉ Set.range t := by
  rintro ⟨i, hi⟩
  exact (Fin.castSucc_lt_last i).ne (h (by simp [hi]))

/-- The structure-side request transfers to the realization (given arity and uniqueness). -/
theorem RelRealizesSome.toRealization (h : IsKnightModel M) {n : ℕ} (t : Fin n ↪ M)
    (p : S Ordinal.omega0 n) {U : Set (S Ordinal.omega0 (n + 1))} (hr : RelRealizesSome ⇑t p U) :
    (toRealization M).RealizesSome t p U := by
  obtain ⟨y, q, hU, hc, hq⟩ := hr
  have hy : y ∉ Set.range t := notMem_range_of_injective_snoc (h.arity q _ hq)
  exact ⟨y, hy, q, hU, hc, (h.eval_eq_some_iff (snoc t y hy) q).mpr hq⟩

/-- **Structures satisfying `T` are models of `S^ω`** (Prop. 3.3.5, one direction, on the
realization `toRealization M`). -/
theorem IsKnightModel.isModel_toRealization (h : IsKnightModel M) :
    (toRealization M).IsModel where
  nonempty := h.nonempty
  consistent {m n} t q f hq := by
    have hcons := h.consistent q t ((h.eval_eq_some_iff t q).mp hq) f
    change (toRealization M).eval (f.trans t) = typeMap f q
    cases htm : typeMap f q with
    | none =>
      refine (toRealization_eval_eq_none_iff _).mpr fun q' hq' => ?_
      have := (hcons q').mp (by rwa [Function.Embedding.coe_trans] at hq')
      exact Option.some_ne_none _ (this.symm.trans htm)
    | some q' =>
      exact (h.eval_eq_some_iff _ q').mpr (by rw [Function.Embedding.coe_trans]; exact (hcons q').mpr htm)
  covering {n} t := by
    obtain ⟨k, ys, p, hp⟩ := h.covering ⇑t t.injective
    exact ⟨k, ⟨Fin.append t ys, h.arity p _ hp⟩, by ext i; simp, (toRealization_eval_isSome_iff _).mpr ⟨p, hp⟩⟩
  genSat t p hp D hD :=
    (h.genSat p ⇑t ((h.eval_eq_some_iff t p).mp hp) D hD).toRealization h t p
  bottomPattern t p hp D hD q' hq' hext :=
    (h.bottomPattern p ⇑t ((h.eval_eq_some_iff t p).mp hp) D hD q' hq' hext).toRealization h t p
  uniformity t p hp γ hγ hlt :=
    (h.uniformity p ⇑t ((h.eval_eq_some_iff t p).mp hp) γ hγ hlt).toRealization h t p
  highGradeDominance t p hp γ hlt :=
    (h.highGradeDominance p ⇑t ((h.eval_eq_some_iff t p).mp hp) γ hlt).toRealization h t p

end Correspondence

section StructureOf

variable {M : Type w}

/-- The `L`-structure of a Knight realization at stage `ω`: `P_p(x̄)` iff `x̄` is injective and
`R(x̄) = p` — (definitionally) the `α = ω` case of the stage chart structure (`stageStructureOf`,
`Knight/ChartLanguage.lean`, #137). -/
@[instance_reducible] def structureOf (R : KnightRealization omegaStage M) :
    knightLang.Structure M :=
  stageStructureOf R

theorem holds_structureOf (R : KnightRealization omegaStage M) {n : ℕ}
    (p : S Ordinal.omega0 n) (xs : Fin n → M) :
    @Holds M (structureOf R) n p xs ↔ ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some p :=
  Iff.rfl

theorem holds_structureOf_of_eval (R : KnightRealization omegaStage M) {n : ℕ}
    {p : S Ordinal.omega0 n} {t : Fin n ↪ M} (ht : R.eval t = some p) :
    @Holds M (structureOf R) n p ⇑t :=
  ⟨t.injective, ht⟩

/-- The realization-side request transfers to the structure. -/
theorem KnightRealization.RealizesSome.relRealizesSome {R : KnightRealization omegaStage M}
    {n : ℕ} {t : Fin n ↪ M} {p : S Ordinal.omega0 n} {U : Set (S Ordinal.omega0 (n + 1))}
    (hr : R.RealizesSome t p U) : @RelRealizesSome M (structureOf R) n ⇑t p U := by
  obtain ⟨y, _, q, hU, hc, hq⟩ := hr
  exact ⟨y, q, hU, hc, holds_structureOf_of_eval R hq⟩

/-- **Models of `S^ω` satisfy `T`** (Prop. 3.3.5, the other direction, on the structure
`structureOf R`). -/
theorem KnightRealization.IsModel.isKnightModel {R : KnightRealization omegaStage M}
    (hR : R.IsModel) : @IsKnightModel M (structureOf R) := by
  let _ : knightLang.Structure M := structureOf R
  refine ⟨hR.nonempty, fun _ _ ⟨h, _⟩ => h,
    fun p xs ⟨hinj, hp⟩ _ f q => ⟨fun ⟨_, hq⟩ => (hR.consistent ⟨xs, hinj⟩ p f hp).symm.trans hq,
      fun hq => ⟨hinj.comp f.injective, (hR.consistent ⟨xs, hinj⟩ p f hp).trans hq⟩⟩,
    fun xs hinj => ?_,
    fun p xs hp D hD => (hR.genSat ⟨xs, hp.1⟩ p hp.2 D hD).relRealizesSome,
    fun p xs hp D hD q' hq' hext => (hR.bottomPattern ⟨xs, hp.1⟩ p hp.2 D hD q' hq' hext).relRealizesSome,
    fun p xs hp γ hγ hlt => (hR.uniformity ⟨xs, hp.1⟩ p hp.2 γ hγ hlt).relRealizesSome,
    fun p xs hp γ hlt => (hR.highGradeDominance ⟨xs, hp.1⟩ p hp.2 γ hlt).relRealizesSome⟩
  obtain ⟨k, s, hs, hsome⟩ := hR.covering ⟨xs, hinj⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨k, fun j => s (Fin.natAdd _ j), p, ?_⟩
  convert holds_structureOf_of_eval R hp using 1
  ext i; exact Fin.addCases (fun i => by simpa using (congrArg (· i) hs).symm) (by simp) i

/-- Models of `S^ω` satisfy `T`, stated on the sentence. -/
theorem KnightRealization.IsModel.realize_knightSentence {R : KnightRealization omegaStage M}
    (hR : R.IsModel) : @Sentenceω.Realize knightLang knightSentence M (structureOf R) :=
  (@realize_knightSentence_iff M (structureOf R)).mpr hR.isKnightModel

/-- Round trip on realizations: the realization of the structure of `R` is `R`. -/
theorem toRealization_structureOf_eval (R : KnightRealization omegaStage M) {n : ℕ}
    (t : Fin n ↪ M) : (@toRealization M (structureOf R)).eval t = R.eval t := by
  let _ : knightLang.Structure M := structureOf R
  cases hR : R.eval t with
  | none =>
    exact (toRealization_eval_eq_none_iff t).mpr fun p ⟨_, hp⟩ =>
      Option.some_ne_none _ (hp.symm.trans hR)
  | some p =>
    refine (toRealization_eval_eq_some_iff ?_ t p).mpr ⟨t.injective, hR⟩
    rintro _ _ _ _ ⟨_, hp⟩ ⟨_, hp'⟩
    exact Option.some.inj (hp'.symm.trans hp)

end StructureOf

section RoundTrip

variable {M : Type w} [knightLang.Structure M]

/-- Structures satisfying `T` are models of `S^ω`, stated on the sentence. -/
theorem isModel_toRealization_of_realize (h : knightSentence.Realize M) :
    (toRealization M).IsModel :=
  ((realize_knightSentence_iff M).mp h).isModel_toRealization

/-- Round trip on structures: under `T`, the structure of the realization of `M` has the same
relations as `M`. -/
theorem holds_structureOf_toRealization (h : IsKnightModel M) {n : ℕ}
    (p : S Ordinal.omega0 n) (xs : Fin n → M) :
    @Holds M (structureOf (toRealization M)) n p xs ↔ Holds p xs := by
  rw [holds_structureOf]
  exact ⟨fun hp => (h.eval_eq_some_iff _ p).mp hp.2,
   fun hp => ⟨h.arity p xs hp, (h.eval_eq_some_iff ⟨xs, h.arity p xs hp⟩ p).mpr hp⟩⟩

/-- **`T` has no finite models** (Prop. 3.3.5's finiteness side, `Spectrum.HasNoFiniteModels`):
a structure realizing `knightSentence` is a model of `S^ω` (`isModel_toRealization_of_realize`),
and every model of `S^α` is infinite (`IsModel.infinite_carrier`: covering plus existential closure
supply fresh points).  No domain construction (#41) is needed. -/
theorem hasNoFiniteModels_knightSentence : Spectrum.HasNoFiniteModels knightSentence := by
  intro n
  rw [Set.eq_empty_iff_forall_notMem]
  intro c hc
  let : knightLang.Structure (Fin n) := StructureSpaceOn.toStructure c
  have := (isModel_toRealization_of_realize (M := Fin n) hc).infinite_carrier
  exact not_finite (Fin n)
