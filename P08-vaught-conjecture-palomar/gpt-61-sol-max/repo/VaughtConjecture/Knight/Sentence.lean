
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ChartLanguage
import VaughtConjecture.Spectrum.Sentence
import InfinitaryLogic.Lomega1omega.Semantics

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

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower
open scoped Lomega1omega

universe u w

/-! ### Stage `ω` and the language -/

/-- The limit stage `ω`: Knight's sentence describes the models of `S^ω` (Def. 3.3.3). -/
def omegaStage : LimitStage := ⟨Ordinal.omega0, Ordinal.isSuccLimit_omega0⟩

/-- Every limit stage lies above `ω`: the theory's language is a reduct of every chart
language. -/
theorem omegaStage_le α : omegaStage ≤ α :=
  Ordinal.omega0_le_of_isSuccLimit α.2

/-- The stage-`ω` types are countable (Prop. 3.1.4 at `ω`: `ω` is a countable ordinal). -/
instance countable_S_omega (n : ℕ) : Countable (S Ordinal.omega0 n) :=
  StageType.countable_S Ordinal.card_omega0.le n

/-- **Knight's language** `L` (Def. 3.3.1): relational, with one `n`-ary relation symbol `P_p`
per stage-`ω` type `p ∈ S^ω_n`, and no function symbols.  `S ω n : Type 1`, so the language
lives in `Language.{0, 1}`.  This is (definitionally) the `α = ω` case of the stage chart
language (`stageLang`, `Knight/ChartLanguage.lean`, #137). -/
def knightLang := stageLang omegaStage

instance knightLang.isRelational : knightLang.IsRelational :=
  stageLang.isRelational omegaStage

/-- The language is countable (as `InfinitaryLogic`'s coding space requires). -/
instance knightLang.countable_relations : Countable (Σ l, knightLang.Relations l) :=
  inferInstanceAs (Countable (Σ l, S Ordinal.omega0 l))

/-- `P_p(x̄)` holds in the `L`-structure `M`. -/
abbrev Holds {M : Type w} [knightLang.Structure M] {n : ℕ} (p : S Ordinal.omega0 n)
    (xs : Fin n → M) :=
  RelMap (L := knightLang) (n := n) p xs

/-! ### Formulas: countable connectives along the enumeration, atoms, tuples -/

/-- Formulas of `L` with `n` bound-variable slots and no free variables. -/
abbrev KnightFormula n := knightLang.BoundedFormulaω Empty n

/-- Countable conjunction `⋀_{i : ι}` over a countable index type, as `einf` along the
enumeration `Encodable.ofCountable ι`. -/
noncomputable def cinf {n : ℕ} {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    KnightFormula n :=
  BoundedFormulaω.einfWith (Encodable.ofCountable ι) φs

/-- Countable disjunction `⋁_{i : ι}` over a countable index type, as `esup` along the
enumeration `Encodable.ofCountable ι`. -/
noncomputable def csup {n : ℕ} {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    KnightFormula n :=
  BoundedFormulaω.esupWith (Encodable.ofCountable ι) φs

/-- The atomic formula `P_p(x_{f 0}, …, x_{f (m-1)})` on the bound variables. -/
def atom {m n : ℕ} (p : S Ordinal.omega0 m) (f : Fin m → Fin n) : KnightFormula n :=
  BoundedFormulaω.rel   p fun i => Term.var (Sum.inr (f i))

/-- `⋀_{i ≠ j} x_i ≠ x_j`: the bound variables are pairwise distinct. -/
noncomputable def distinct n :=
  cinf fun ij : {ij : Fin n × Fin n // ij.1 ≠ ij.2} =>
    ∼ω (BoundedFormulaω.equal (Term.var (Sum.inr ij.1.1)) (Term.var (Sum.inr ij.1.2)))

/-- `∃ y₀ … y_{k-1}`: existential quantification over the last `k` bound variables. -/
def exsFrom {n} : ∀ k , KnightFormula (n + k) → KnightFormula n
  | 0, φ => φ
  | k + 1, φ => exsFrom k (BoundedFormulaω.ex φ)

local notation "S₀" => S Ordinal.omega0

section

variable {M : Type w} [knightLang.Structure M] {n : ℕ} {v : Empty → M} {xs : Fin n → M}

@[simp] theorem realize_cinf {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    (cinf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaω.realize_einfWith _ φs

@[simp] theorem realize_csup {ι : Type u} [Countable ι] (φs : ι → KnightFormula n) :
    (csup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaω.realize_esupWith _ φs

@[simp] theorem realize_atom {m : ℕ} (p : S₀ m) (f : Fin m → Fin n) :
    (atom p f).Realize v xs ↔ Holds p (xs ∘ f) :=
  Iff.rfl

@[simp] theorem realize_distinct :
    (distinct n).Realize v xs ↔ Function.Injective xs := by
  simp only [distinct, realize_cinf,  
      Subtype.forall, Prod.forall]
  exact ⟨fun h i j hij => by_contra fun hne => h i j hne hij, fun h i j hne hij => hne (h hij)⟩

/-- Realization of the universal closure of all bound variables (Mathlib's `alls`) at the
empty tuple. -/
theorem realize_alls (φ : KnightFormula n) :
    BoundedFormulaω.Realize φ.alls v Fin.elim0 ↔ ∀ ys , φ.Realize v ys :=
  BoundedFormulaInf.realize_alls

@[simp] theorem realize_exsFrom k φ :
    (exsFrom k φ).Realize v xs ↔ ∃ ys , φ.Realize v (Fin.append xs ys) := by
  induction k with
  | zero =>
    
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      have : Fin.append xs Fin.elim0 = xs := by
        simp_all
      rwa [this]
    · rintro ⟨ys, h⟩
      have : Fin.append xs ys = xs := by
        funext i
        rw [Subsingleton.elim ys Fin.elim0, Fin.append_elim0]
        rfl
      rwa [this] at h
  | succ k ih =>
    simp only [exsFrom, ih, BoundedFormulaω.realize_ex]
    constructor
    · rintro ⟨ys, y, h⟩
      exact ⟨Fin.snoc ys y, by rwa [Fin.append_snoc]⟩
    · rintro ⟨ys, h⟩
      exact ⟨Fin.init ys, ys (Fin.last k), by rwa [← Fin.append_snoc, Fin.snoc_init_self]⟩

end

/-! ### The clauses of `T` (Def. 3.3.3) -/

/-- The carrier is nonempty (`∃ x, ⊤`): the standing convention "a model with domain `M`"
(`KnightRealization.IsModel.nonempty`). -/
def nonemptyClause : knightLang.Sentenceω :=
  BoundedFormulaω.ex (⊤ : KnightFormula 1)

/-- **Arity** (Def. 3.2.1(1)): `∀ x̄, P_p(x̄) → ⋀_{i ≠ j} x_i ≠ x_j` — a type is carried only by
injective tuples (in a `KnightRealization` this is automatic from the encoding). -/
noncomputable def arityClause : knightLang.Sentenceω :=
  cinf fun n => cinf fun p => (atom p id ⟹ω distinct n).alls

open Classical in
/-- **Consistency** (Def. 3.2.1(2), exact): for all `n`, `p ∈ S^ω_n`, `f : m ↪ n` and
`q ∈ S^ω_m`, `∀ x̄, P_p(x̄) → (P_q(x̄∘f) ⇔ [S^ω f (p) = q])`: the type of the face `x̄∘f` is
exactly the partial restriction of the type of `x̄` — `P_q(x̄∘f)` when `typeMap f p = some q`,
`¬ P_{q'}(x̄∘f)` for every other `q'` (in particular for every `q'` when the face is invisible,
`typeMap f p = none`).  At `f = id` (`typeMap_refl`) this is "at most one type per tuple"
(`IsKnightModel.unique`). -/
noncomputable def consistencyClause : knightLang.Sentenceω :=
  cinf fun n => cinf fun p => cinf fun mf : Σ m : ℕ, Fin m ↪ Fin n =>
    cinf fun q : S₀ mf.1 =>
      (atom p id ⟹ω
        (if typeMap mf.2 p = some q then atom q mf.2 else ∼ω (atom q mf.2))).alls

/-- **Covering** (Def. 3.2.1(3), initial segment): `∀ x̄ injective, ⋁_k ∃ ȳ ⋁_{p ∈ S^ω_{n+k}}
P_p(x̄⌢ȳ)`. -/
noncomputable def coveringClause : knightLang.Sentenceω :=
  cinf fun n : ℕ =>
    (distinct n ⟹ω
      csup fun k : ℕ => exsFrom k (csup fun p : S₀ (n + k) => atom p id)).alls

/-- The request `⋁_{q ∈ U, q a coface of p} ∃ y, P_q(x̄⌢y)` (the conclusion of Def. 3.2.1(4)
for the family `U ⊆ (S^ω ι_{n,n+1})⁻¹(p)`). -/
noncomputable def requestFormula {n : ℕ} (p : S₀ n)
    (U : Set (S₀ (n + 1))) :=
  csup fun q : {q : S₀ (n + 1) // q ∈ U ∧ IsCoface p q} =>
    BoundedFormulaω.ex (atom q.1 id)

/-- The common shape of the four **existential-closure** clauses (Def. 3.2.1(4)): for a countable
parameter space `Param n p` and families `U n p a`, `⋀_n ⋀_p ∀ x̄, P_p(x̄) → ⋀_{a : Param n p}
⋁_{q ∈ U n p a, coface of p} ∃ y, P_q(x̄⌢y)`. -/
noncomputable def ecClause (Param : ∀ n : ℕ, S₀ n → Type u)
    [∀ n p, Countable (Param n p)]
    (U : ∀ (n : ℕ) (p : S₀ n), Param n p → Set (S₀ (n + 1))) :
    knightLang.Sentenceω :=
  cinf fun n : ℕ => cinf fun p : S₀ n =>
    (atom p id ⟹ω cinf fun a : Param n p => requestFormula p (U n p a)).alls

/-- **(a)(i) Generalised saturation**: parameters `D` a domain on `n+1` with `D⟨n,n⟩ = dom p`
(`ExtendsDomain`), family `GenSatFamily D`. -/
noncomputable def genSatClause :=
  ecClause (fun n p => {D : SemScheme (n + 1) // ExtendsDomain p D})
    (fun _ _ D => GenSatFamily D.1)

/-- A `−∞`-pattern on `D^{≤ n} = D⟨A, n⟩` (the cells of grade `≤ n`). -/
abbrev BotPattern {n} (D : SemScheme (n + 1)) :=
  D.scheme.below (Finset.univ, n) → Bool

/-- The cofaces with domain `D` and `−∞`-pattern `π` on `D^{≤ n}`. -/
def PatternFamily {n : ℕ} (D : SemScheme (n + 1)) (π : BotPattern D) :
    Set (S₀ (n + 1)) :=
  {q | ∃ h : q.scheme = D, ∀ Θ : D.scheme.below (Finset.univ, n),
    q.label (SemScheme.castCell h.symm Θ.1) = ⊥ ↔ π Θ = true}

/-- `BottomPatternFamily D q'` depends on `q'` only through its `−∞`-pattern. -/
theorem bottomPatternFamily_eq_patternFamily {n} {D : SemScheme (n + 1)}
    q' π (hπ : ∀ Θ, q' Θ.1 = ⊥ ↔ π Θ = true) :
    BottomPatternFamily (α := Ordinal.omega0) D q' = PatternFamily D π := by
  ext q
  simp  [BottomPatternFamily, PatternFamily,  hπ]

/-- `π` is the `−∞`-pattern of some labelling `q'` of `D` respecting the semantics of `D`
(faithfully, no stage bound) and extending `p` along the initial face — the paper's parameter
of Def. 3.2.1(4)(a)(ii), seen through its pattern. -/
def IsPatternOf {n : ℕ} (p : S₀ n) (D : SemScheme (n + 1)) (π : BotPattern D) :=
  ∃ hD : ExtendsDomain p D, ∃ q' : CellLabels D.scheme,
    RespectsSemantics D.rows q' ∧ (PointwiseEq (q' ∘ hD.cellOf) p.label) ∧
      ∀ Θ, (q' Θ.1 = ⊥ ↔ π Θ = true)

/-- The parameter space of clause (a)(ii) as written here: domains `D` extending `dom p` with
a `−∞`-pattern realized by some faithful `q'` extending `p`.  Countable (finitely many patterns
per domain, countably many domains) — the paper's parameter `q'` ranges over uncountably many
labellings, but only its pattern matters (`bottomPatternFamily_eq_patternFamily`). -/
def BottomPatternParam {n : ℕ} (p : S₀ n) :=
  {Dπ : Σ D : SemScheme (n + 1), BotPattern D // IsPatternOf p Dπ.1 Dπ.2}

instance {n : ℕ} (p : S₀ n) : Countable (BottomPatternParam p) := by
  unfold BottomPatternParam
  infer_instance

/-- **(a)(ii) Prescribed `−∞`-pattern**: parameters `(D, π)` with `π` the pattern of a faithful
`q'` extending `p`, family `PatternFamily D π = BottomPatternFamily D q'`. -/
noncomputable def bottomPatternClause :=
  ecClause (fun _ p => BottomPatternParam p) (fun _ _ Dπ => PatternFamily Dπ.1.1 Dπ.1.2)

/-- **(b) Uniformity**: parameters the non-successor ordinals `γ < ω` (i.e. `γ = 0`, indexed by
`{k : ℕ // IsNonSuccessor k}` — every `γ < ω` is a natural number), family
`UniformityFamily γ`. -/
noncomputable def uniformityClause :=
  ecClause (fun _ _ => {k : ℕ // Value.IsNonSuccessor (k)})
    (fun _ _ k => UniformityFamily (k.1))

/-- **(c) High-grade dominance**: parameters `γ < ω` (indexed by `ℕ`), family
`HighGradeDominanceFamily γ`. -/
noncomputable def highGradeDominanceClause :=
  ecClause (fun _ _ => ℕ) (fun _ _ k => HighGradeDominanceFamily (k))

/-- **Knight's sentence `T`** (Def. 3.3.3): the conjunction of the clauses. -/
noncomputable def knightSentence :=
  nonemptyClause ⊓ arityClause ⊓ consistencyClause ⊓ coveringClause ⊓ genSatClause ⊓
    bottomPatternClause ⊓ uniformityClause ⊓ highGradeDominanceClause

/-! ### Clause-wise realization -/

section

variable {M : Type w} [knightLang.Structure M]

/-- The semantic form of the request `requestFormula p U` over the tuple `xs`: some `y` and some
`q ∈ U`, a coface of `p`, with `P_q(xs⌢y)` (the structure-side `RealizesSome`). -/
def RelRealizesSome {n : ℕ} (xs : Fin n → M) (p : S₀ n)
    (U : Set (S₀ (n + 1))) :=
  ∃ (y : M) (q : S₀ (n + 1)), q ∈ U ∧ IsCoface p q ∧ Holds q (Fin.snoc xs y)

variable {n : ℕ} {v : Empty → M} {xs : Fin n → M}

@[simp] theorem realize_requestFormula (p : S₀ n)
    (U : Set (S₀ (n + 1))) :
    (requestFormula p U).Realize v xs ↔ RelRealizesSome xs p U := by simp_all [requestFormula, RelRealizesSome] <;> aesop

variable (M)

theorem realize_nonemptyClause : nonemptyClause.Realize M ↔ Nonempty M := by simp_all [nonemptyClause, Sentenceω.realize_def]

theorem realize_arityClause :
    arityClause.Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs → Function.Injective xs := by
  simp only [arityClause, Sentenceω.realize_def, realize_cinf, realize_alls,
    BoundedFormulaω.realize_imp, realize_atom, Function.comp_id, realize_distinct]

theorem realize_consistencyClause :
    consistencyClause.Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
        ∀ {m : ℕ} (f : Fin m ↪ Fin n) (q : S₀ m),
          Holds q (xs ∘ f) ↔ typeMap f p = some q := by
  simp only [consistencyClause, Sentenceω.realize_def, realize_cinf, realize_alls,
    BoundedFormulaω.realize_imp, realize_atom, Function.comp_id, Sigma.forall]
  refine forall_congr' fun n => forall_congr' fun p => ?_
  constructor
  · intro h xs hp m f q
    have := h m f q xs hp
    split_ifs at this with hc
    · exact ⟨fun _ => hc, fun _ => this⟩
    · simp_all
  · intro h m f q xs hp
    split_ifs with hc
    · exact (h xs hp f q).mpr hc
    · simp_all

theorem realize_coveringClause :
    coveringClause.Realize M ↔
      ∀ {n : ℕ} (xs : Fin n → M), Function.Injective xs →
        ∃ (k : ℕ) (ys : Fin k → M) (p : S₀ (n + k)), Holds p (Fin.append xs ys) := by
  simp only [coveringClause, Sentenceω.realize_def, realize_cinf, realize_alls,
    BoundedFormulaω.realize_imp, realize_distinct, realize_csup, realize_exsFrom, realize_atom,
    Function.comp_id]

theorem realize_ecClause (Param : ∀ n : ℕ, S₀ n → Type u)
    [∀ n p, Countable (Param n p)]
    (U : ∀ (n : ℕ) (p : S₀ n), Param n p → Set (S₀ (n + 1))) :
    (ecClause Param U).Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
        ∀ a : Param n p, RelRealizesSome xs p (U n p a) := by
  simp only [ecClause, Sentenceω.realize_def, realize_cinf, realize_alls,
    BoundedFormulaω.realize_imp, realize_atom, Function.comp_id, realize_requestFormula]

theorem realize_genSatClause :
    genSatClause.Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
        ∀ D : SemScheme (n + 1), ExtendsDomain p D → RelRealizesSome xs p (GenSatFamily D) := by simp_all [genSatClause, realize_ecClause]

/-- Clause (a)(ii), realized, in the **paper's parameterization** by the labelling `q'`: the
pattern encoding is transparent. -/
theorem realize_bottomPatternClause :
    bottomPatternClause.Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
        ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : CellLabels D.scheme),
          RespectsSemantics D.rows q' → (PointwiseEq (q' ∘ hD.cellOf) p.label) →
          RelRealizesSome xs p (BottomPatternFamily D q') := by
  rw [bottomPatternClause, realize_ecClause]
  constructor
  · intro h n p xs hp D hD q' hq' hext
    classical
    have := h p xs hp ⟨⟨D, fun Θ => decide (q' Θ.1 = ⊥)⟩, hD, q', hq', hext,
      fun Θ => decide_eq_true_iff.symm⟩
    rwa [bottomPatternFamily_eq_patternFamily q' _ (fun Θ => decide_eq_true_iff.symm)]
  · rintro h n p xs hp ⟨⟨D, π⟩, hD, q', hq', hext, hπ⟩
    rw [← bottomPatternFamily_eq_patternFamily q' π hπ]
    exact h p xs hp D hD q' hq' hext

theorem realize_uniformityClause :
    uniformityClause.Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
        ∀ γ : Ordinal₀, Value.IsNonSuccessor γ → γ < Ordinal.omega0 →
          RelRealizesSome xs p (UniformityFamily γ) := by
  rw [uniformityClause, realize_ecClause]
  constructor
  · intro h n p xs hp γ hγ hlt
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hlt
    exact h p xs hp ⟨k, hγ⟩
  · simp_all

theorem realize_highGradeDominanceClause :
    highGradeDominanceClause.Realize M ↔
      ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
        ∀ γ : Ordinal₀, γ < Ordinal.omega0 →
          RelRealizesSome xs p (HighGradeDominanceFamily γ) := by
  rw [highGradeDominanceClause, realize_ecClause]
  constructor
  · intro h n p xs hp γ hlt
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hlt
    exact h p xs hp k
  · simp_all

/-- The semantic content of `T` on an `L`-structure `M`: the eight clauses, realized.  This is
the structure-side counterpart of `KnightRealization.IsModel` (the two correspond:
`IsKnightModel.isModel_toRealization`, `IsModel.isKnightModel`). -/
structure IsKnightModel : Prop where
  /-- The carrier is nonempty. -/
  nonempty : Nonempty M
  /-- Clause (1): a type is carried only by injective tuples. -/
  arity : ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
    Function.Injective xs
  /-- Clause (2), exact: the type of a face is the partial restriction. -/
  consistent : ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
    ∀ {m : ℕ} (f : Fin m ↪ Fin n) (q : S₀ m),
      Holds q (xs ∘ f) ↔ typeMap f p = some q
  /-- Clause (3): every injective tuple is an initial segment of a typed one. -/
  covering : ∀ {n : ℕ} (xs : Fin n → M), Function.Injective xs →
    ∃ (k : ℕ) (ys : Fin k → M) (p : S₀ (n + k)), Holds p (Fin.append xs ys)
  /-- Clause (4)(a)(i). -/
  genSat : ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
    ∀ D : SemScheme (n + 1), ExtendsDomain p D → RelRealizesSome xs p (GenSatFamily D)
  /-- Clause (4)(a)(ii), in the paper's parameterization. -/
  bottomPattern : ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
    ∀ (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) (q' : CellLabels D.scheme),
      RespectsSemantics D.rows q' → (PointwiseEq (q' ∘ hD.cellOf) p.label) →
      RelRealizesSome xs p (BottomPatternFamily D q')
  /-- Clause (4)(b). -/
  uniformity : ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
    ∀ γ : Ordinal₀, Value.IsNonSuccessor γ → γ < Ordinal.omega0 →
      RelRealizesSome xs p (UniformityFamily γ)
  /-- Clause (4)(c). -/
  highGradeDominance : ∀ {n : ℕ} (p : S₀ n) (xs : Fin n → M), Holds p xs →
    ∀ γ : Ordinal₀, γ < Ordinal.omega0 → RelRealizesSome xs p (HighGradeDominanceFamily γ)

/-- **Realization of `T`**: `M ⊨ T` iff the eight clauses hold in `M`. -/
theorem realize_knightSentence_iff : knightSentence.Realize M ↔ IsKnightModel M := by
  have h : knightSentence.Realize M ↔
      nonemptyClause.Realize M ∧ arityClause.Realize M ∧ consistencyClause.Realize M ∧
        coveringClause.Realize M ∧ genSatClause.Realize M ∧ bottomPatternClause.Realize M ∧
          uniformityClause.Realize M ∧ highGradeDominanceClause.Realize M := by
    simp  [knightSentence, Sentenceω.realize_def,  and_assoc]
  rw [h, realize_nonemptyClause, realize_arityClause, realize_consistencyClause,
    realize_coveringClause, realize_genSatClause, realize_bottomPatternClause,
    realize_uniformityClause, realize_highGradeDominanceClause]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩

variable {M}

/-- At most one type per tuple: the instance `f = id` of the consistency clause. -/
theorem IsKnightModel.unique (h : IsKnightModel M) {n : ℕ} {p p' : S₀ n}
    {xs : Fin n → M} (hp : Holds p xs) (hp' : Holds p' xs) : p' = p := by
  have := (h.consistent p xs hp (Function.Embedding.refl (Fin n)) p').mp
    (by aesop)
  rw [typeMap_refl, Option.some.injEq] at this
  exact this.symm

end

/-! ### From structures to realizations and back -/

section

variable (M : Type w) [knightLang.Structure M]

open Classical in
/-- The Knight realization of an `L`-structure: the type of an injective tuple is the type `p`
with `P_p(x̄)`, if any (chosen; unique under the consistency clause,
`toRealization_eval_eq_some_iff`). -/
noncomputable def toRealization : KnightRealization omegaStage M where
  eval {n} t := if h : ∃ p : S₀ n, Holds p ⇑t then some h.choose else none

variable {M}

theorem toRealization_eval_eq_none_iff {n} t :
    (toRealization M).eval t = none ↔ ∀ p : S₀ n, ¬ Holds p ⇑t := by simp_all [toRealization]

theorem toRealization_eval_isSome_iff {n} t :
    ((toRealization M).eval t).isSome ↔ ∃ p : S₀ n, Holds p ⇑t := by
  simp  [← Option.ne_none_iff_isSome,  toRealization_eval_eq_none_iff,  ]

/-- Under "at most one type per tuple", the type of `t` is the `p` with `P_p(t)`. -/
theorem toRealization_eval_eq_some_iff
    (hu : ∀ {n : ℕ} {p p' : S₀ n} {xs : Fin n → M}, Holds p xs → Holds p' xs →
      p' = p)
    {n : ℕ} (t : Fin n ↪ M) (p : S₀ n) :
    (toRealization M).eval t = some p ↔ Holds p ⇑t := by
  dsimp only [toRealization]
  split_ifs with h
  · exact ⟨fun hp => Option.some.inj hp ▸ h.choose_spec,
      fun hp => congrArg some (hu hp h.choose_spec)⟩
  · simp_all

/-- Under the clauses of `T`, the type of `t` in `toRealization M` is the `p` with `P_p(t)`. -/
def IsKnightModel.eval_eq_some_iff (h : IsKnightModel M) {n : ℕ} (t : Fin n ↪ M)
    (p : S₀ n) :=
  toRealization_eval_eq_some_iff (h.unique) t p

omit [knightLang.Structure M] in
/-- A point off an injective `snoc` is off the tuple. -/
theorem notMem_range_of_injective_snoc {n} {t} {y}
    (h : Function.Injective (Fin.snoc t y : Fin (n + 1) → M)) : y ∉ Set.range t := by
  rintro ⟨i, hi⟩
  have : (Fin.snoc t y : Fin (n + 1) → M) (Fin.castSucc i) =
      (Fin.snoc t y : Fin (n + 1) → M) (Fin.last n) := by
    simp_all
  exact (Fin.castSucc_lt_last i).ne (h this)

/-- The structure-side request transfers to the realization (given arity and uniqueness). -/
theorem RelRealizesSome.toRealization (h : IsKnightModel M) {n : ℕ} (t : Fin n ↪ M)
    (p : S₀ n) {U : Set (S₀ (n + 1))} (hr : RelRealizesSome ⇑t p U) :
    (toRealization M).RealizesSome t p U := by
  obtain ⟨y, q, hU, hc, hq⟩ := hr
  have hy  := notMem_range_of_injective_snoc (h.arity q _ hq)
  exact ⟨y, hy, q, hU, hc, (h.eval_eq_some_iff (snoc t y hy) q).mpr hq⟩

/-- **Structures satisfying `T` are models of `S^ω`** (Prop. 3.3.5, one direction, on the
realization `toRealization M`). -/
theorem IsKnightModel.isModel_toRealization (h : IsKnightModel M) :
    (toRealization M).IsModel where
  nonempty := h.nonempty
  consistent := by
    intro m n t q f hq
    change S Ordinal.omega0 n at q
    have hcons := h.consistent q t ((h.eval_eq_some_iff t q).mp hq) f
    change (toRealization M).eval (f.trans t) = typeMap f q
    cases htm : typeMap f q with
    | none =>
      refine (toRealization_eval_eq_none_iff _).mpr fun q' hq' => ?_
      have := (hcons q').mp (by rwa [] at hq')
      rw [htm] at this
      exact Option.some_ne_none _ this.symm
    | some q' =>
      refine (h.eval_eq_some_iff _ q').mpr ?_
      
      exact (hcons q').mpr htm
  covering := by
    intro n t
    obtain ⟨k, ys, p, hp⟩ := h.covering ⇑t t.injective
    refine ⟨k, ⟨Fin.append t ys, h.arity p _ hp⟩, ?_, ?_⟩
    · ext i
      simp  
    · exact (toRealization_eval_isSome_iff _).mpr ⟨p, hp⟩
  genSat := fun t p hp D hD =>
    (h.genSat p ⇑t ((h.eval_eq_some_iff t p).mp hp) D hD).toRealization h t p
  bottomPattern := fun t p hp D hD q' hq' hext =>
    (h.bottomPattern p ⇑t ((h.eval_eq_some_iff t p).mp hp) D hD q' hq' hext).toRealization h t p
  uniformity := fun t p hp γ hγ hlt =>
    (h.uniformity p ⇑t ((h.eval_eq_some_iff t p).mp hp) γ hγ hlt).toRealization h t p
  highGradeDominance := fun t p hp γ hlt =>
    (h.highGradeDominance p ⇑t ((h.eval_eq_some_iff t p).mp hp) γ hlt).toRealization h t p

end

section

variable {M : Type w}

/-- The `L`-structure of a Knight realization at stage `ω`: `P_p(x̄)` iff `x̄` is injective and
`R(x̄) = p` — (definitionally) the `α = ω` case of the stage chart structure (`stageStructureOf`,
`Knight/ChartLanguage.lean`, #137). -/
@[instance_reducible] noncomputable def structureOf (R : KnightRealization omegaStage M) :
    knightLang.Structure M :=
  stageStructureOf R



theorem holds_structureOf_of_eval (R : KnightRealization omegaStage M) {n : ℕ}
    {p : S₀ n} {t : Fin n ↪ M} (ht : R.eval t = some p) :
    @Holds M (structureOf R) n p ⇑t :=
  ⟨t.injective, ht⟩

/-- The realization-side request transfers to the structure. -/
theorem KnightRealization.RealizesSome.relRealizesSome {R : KnightRealization omegaStage M}
    {n : ℕ} {t : Fin n ↪ M} {p : S₀ n} {U : Set (S₀ (n + 1))}
    (hr : R.RealizesSome t p U) : @RelRealizesSome M (structureOf R) n ⇑t p U := by
  obtain ⟨y, hy, q, hU, hc, hq⟩ := hr
  exact ⟨y, q, hU, hc, holds_structureOf_of_eval R hq⟩

/-- **Models of `S^ω` satisfy `T`** (Prop. 3.3.5, the other direction, on the structure
`structureOf R`). -/
theorem KnightRealization.IsModel.isKnightModel {R : KnightRealization omegaStage M}
    (hR : R.IsModel) : @IsKnightModel M (structureOf R) := by
  let _  := structureOf R
  refine ⟨hR.nonempty, fun _ _ ⟨h, _⟩ => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- consistency
    rintro n p xs ⟨hinj, hp⟩ m f q
    have hcons  := hR.consistent ⟨xs, hinj⟩ p f hp
    constructor
    · rintro ⟨_, hq⟩
      exact hcons.symm.trans hq
    · intro hq
      exact ⟨hinj.comp f.injective, hcons.trans hq⟩
  · -- covering
    intro n xs hinj
    obtain ⟨k, s, hs, hsome⟩ := hR.covering ⟨xs, hinj⟩
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨k, fun j => s (Fin.natAdd n j), p, ?_⟩
    have heq : Fin.append xs (fun j => s (Fin.natAdd n j)) = ⇑s := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact (congrArg (fun g : Fin n ↪ M => g i) hs).symm
      · rw [Fin.append_right]
    rw [heq]
    exact holds_structureOf_of_eval R hp
  · -- (a)(i)
    intro n p xs hp D hD
    exact (hR.genSat ⟨xs, hp.1⟩ p hp.2 D hD).relRealizesSome
  · -- (a)(ii)
    intro n p xs hp D hD q' hq' hext
    exact (hR.bottomPattern ⟨xs, hp.1⟩ p hp.2 D hD q' hq' hext).relRealizesSome
  · -- (b)
    intro n p xs hp γ hγ hlt
    exact (hR.uniformity ⟨xs, hp.1⟩ p hp.2 γ hγ hlt).relRealizesSome
  · -- (c)
    intro n p xs hp γ hlt
    exact (hR.highGradeDominance ⟨xs, hp.1⟩ p hp.2 γ hlt).relRealizesSome

/-- Models of `S^ω` satisfy `T`, stated on the sentence. -/
def KnightRealization.IsModel.realize_knightSentence {R : KnightRealization omegaStage M}
    (hR : R.IsModel) :=
  (@realize_knightSentence_iff M (structureOf R)).mpr hR.isKnightModel

/-- Round trip on realizations: the realization of the structure of `R` is `R`. -/
theorem toRealization_structureOf_eval (R : KnightRealization omegaStage M) {n : ℕ}
    (t : Fin n ↪ M) : (@toRealization M (structureOf R)).eval t = R.eval t := by
  let _  := structureOf R
  cases hR : R.eval t with
  | none =>
    refine (toRealization_eval_eq_none_iff t).mpr fun p hp => ?_
    obtain ⟨_, hp⟩ := hp
    have hp' : R.eval t = some p := hp
    rw [hR] at hp'
    exact Option.some_ne_none _ hp'.symm
  | some p =>
    refine (toRealization_eval_eq_some_iff ?_ t p).mpr ⟨t.injective, hR⟩
    rintro n p p' xs ⟨h, hp⟩ ⟨_, hp'⟩
    exact Option.some_injective _ (hp'.symm.trans hp)

end

section

variable {M : Type w} [knightLang.Structure M]

/-- Structures satisfying `T` are models of `S^ω`, stated on the sentence. -/
def isModel_toRealization_of_realize (h : knightSentence.Realize M) :=
  ((realize_knightSentence_iff M).mp h).isModel_toRealization

/-- Round trip on structures: under `T`, the structure of the realization of `M` has the same
relations as `M`. -/
theorem holds_structureOf_toRealization (h : IsKnightModel M) {n : ℕ}
    (p : S₀ n) (xs : Fin n → M) :
    @Holds M (structureOf (toRealization M)) n p xs ↔ Holds p xs := by
  
  constructor
  · rintro ⟨hinj, hp⟩
    exact (h.eval_eq_some_iff _ p).mp hp
  · intro hp
    exact ⟨h.arity p xs hp, (h.eval_eq_some_iff ⟨xs, h.arity p xs hp⟩ p).mpr hp⟩

/-- **`T` has no finite models** (Prop. 3.3.5's finiteness side, `Spectrum.HasNoFiniteModels`):
a structure realizing `knightSentence` is a model of `S^ω` (`isModel_toRealization_of_realize`),
and every model of `S^α` is infinite (`IsModel.infinite_carrier`: covering plus existential closure
supply fresh points).  No domain construction (#41) is needed. -/
theorem hasNoFiniteModels_knightSentence : Spectrum.HasNoFiniteModels knightSentence := by
  intro n
  rw [Set.eq_empty_iff_forall_notMem]
  intro c hc
  let  := StructureSpaceOn.toStructure c
  have h  := hc
  have := (isModel_toRealization_of_realize h).infinite_carrier
  exact not_finite (Fin n)


