/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Terminal
public import VaughtConjecture.DirectedNat

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

/-- Any two injective tuples `t`, `s` on `M` jointly embed into one injective tuple: `t` is an
initial segment, and `s` embeds via `g`. -/
theorem exists_common_tuple {M : Type w} {n m : ℕ} (t : Fin n ↪ M) (s : Fin m ↪ M) :
    ∃ (k : ℕ) (w : Fin (n + k) ↪ M) (g : Fin m ↪ Fin (n + k)),
      (Fin.castAddEmb k).trans w = t ∧ g.trans w = s := by
  classical
  set B : Finset M := Finset.univ.image s \ Finset.univ.image t with hBdef
  have hBt : ∀ b ∈ B, b ∉ Set.range t := by
    simp_all
  let e : Fin B.card → M := fun j => (B.equivFin.symm j : M)
  have hte : ∀ (a : Fin n) (b : Fin B.card), t a ≠ e b := by
    grind
  have hwinj : Function.Injective (Fin.append (⇑t) e) := by
    intro i j hij
    induction i using Fin.addCases with
    | left i₁ =>
      induction j using Fin.addCases with
      | left j₁ =>
        simp_all
      | right j₁ =>
        simp_all
    | right i₁ =>
      induction j using Fin.addCases with
      | left j₁ =>
        rw [Fin.append_right, Fin.append_left] at hij
        tauto
      | right j₁ =>
        aesop
  let w : Fin (n + B.card) ↪ M := ⟨Fin.append (⇑t) e, hwinj⟩
  have hw_left : ∀ j : Fin n, w (Fin.castAdd B.card j) = t j := by aesop
  have hmem : ∀ i : Fin m, (¬ ∃ j, t j = s i) → s i ∈ B := by
    simp_all
  obtain ⟨g0, hg0⟩ : ∃ g0 : Fin m → Fin (n + B.card), ∀ i, w (g0 i) = s i := by
    refine ⟨fun i => if h : ∃ j, t j = s i then Fin.castAdd B.card h.choose
      else Fin.natAdd n (B.equivFin ⟨s i, hmem i h⟩), fun i => ?_⟩
    dsimp only
    by_cases h : ∃ j, t j = s i
    · grind
    aesop
  refine ⟨B.card, w, ⟨g0, fun i j hij => s.injective (by grind)⟩, ?_, ?_⟩
  · ext j
    tauto
  · ext i
    tauto

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

/-- **`K^p` is weakly increasing along inclusion of covers** (the monotonicity behind
Lemma 5.3.10's dichotomy): if `p` is the exact restriction of `q`, then `K^p ≤ K^q`.  Exact
restriction preserves the `∞`-label and the grade of a witnessing top cell
(`label_mapCell`, `grade_mapCell`), and availability (Def. 2.5.4(2)) + completeness
(Def. 2.5.15) then produce a full-scope `∞`-cell of the same grade in `q`
(`grade_mem_topGrades`). -/
theorem topGrade_le_of_typeMap_eq_some {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : p.topGrade ≤ q.topGrade := by
  by_cases hne : p.topGrades.Nonempty
  · obtain ⟨Θ, hsc, hgr, htop⟩ : p.topGrade ∈ p.topGrades :=
      Nat.sSup_mem hne p.topGrades_bddAbove
    have hmem : p.topGrade ∈ q.topGrades := by
      have hlab : q.label (mapCell h Θ) = ⊤ := by rw [label_mapCell h Θ, htop]
      have hmem' := grade_mem_topGrades hlab
      rwa [grade_mapCell h Θ, hgr] at hmem'
    exact le_csSup q.topGrades_bddAbove hmem
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold topGrade
    simp_all

end StageType

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w}

/-- A **labelled cover** of the realization `R`: an injective tuple together with its label
(the rebuilt form of Def. 3.2.8's "finite subset `A ∈ dom [M]` with its type `M(A)`" — on
tuples, as everywhere in this library). -/
structure LabelledExt (R : KnightRealization α M) where
  /-- The arity of the cover. -/
  arity : ℕ
  /-- The underlying injective tuple. -/
  tuple : Fin arity ↪ M
  /-- The label (stage type) the realization assigns to the tuple. -/
  type : S α.1 arity
  /-- The tuple is labelled, by `type`. -/
  eval_eq : R.eval tuple = some type

namespace LabelledExt

variable {R : KnightRealization α M}

/-- The order of the labelled-cover poset: `x ≤ y` iff the tuple of `x` is a **visible face**
of the tuple of `y` **with the labels restricting exactly** — some embedding carries `x`'s
tuple onto a sub-tuple of `y`'s and `typeMap` along it carries `y`'s label onto `x`'s.  This
is the paper's inclusion of labelled finite subsets, and the common-extension shape
`StabilizesTo` quantifies with.  A preorder, not a partial order: mutually comparable covers
are permutations of one another, not equal. -/
instance : Preorder (LabelledExt R) where
  le x y := ∃ f : Fin x.arity ↪ Fin y.arity,
    f.trans y.tuple = x.tuple ∧ typeMap f y.type = some x.type
  le_refl x := ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _, typeMap_refl _⟩
  le_trans x y z := by
    rintro ⟨f, hft, hfp⟩ ⟨g, hgt, hgp⟩
    refine ⟨f.trans g, ?_, ?_⟩
    · rw [Function.Embedding.trans_assoc, hgt, hft]
    · rwa [← typeMap_trans f g z.type y.type hgp]

/-- `K^p` is weakly increasing along the labelled-cover order. -/
theorem topGrade_mono {x y : LabelledExt R} (h : x ≤ y) :
    x.type.topGrade ≤ y.type.topGrade := by
  obtain ⟨f, -, hpq⟩ := h
  exact topGrade_le_of_typeMap_eq_some hpq

/-- The principal **tail** above a labelled cover: all labelled covers extending it. -/
def tail (x : LabelledExt R) : Set (LabelledExt R) := {y | x ≤ y}

end LabelledExt

variable {R : KnightRealization α M}

/-- **Absorption** (minimal hypotheses — clauses (2) and (3) suffice): above any labelled
cover there is a labelled cover containing any prescribed tuple.  *Concatenate*
(`exists_common_tuple`), *cover* (clause (3)), *restrict* (clause (2)).  No
existential-closure clause is consulted, and no coface is manufactured: the larger cover is
one of the realization's own. -/
theorem exists_labelledExt_le (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) {m : ℕ} (s : Fin m ↪ M) :
    ∃ y : R.LabelledExt, x ≤ y ∧ ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s := by
  obtain ⟨k, w, g0, hwt, hws⟩ := exists_common_tuple x.tuple s
  obtain ⟨k', u, hu, husome⟩ := hcov w
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp husome
  have htuple : ((Fin.castAddEmb k).trans (Fin.castAddEmb k')).trans u = x.tuple := by
    aesop
  have htype : typeMap ((Fin.castAddEmb k).trans (Fin.castAddEmb k')) q = some x.type := by
    have h := hcons u q ((Fin.castAddEmb k).trans (Fin.castAddEmb k')) hq
    rw [htuple, x.eval_eq] at h
    tauto
  refine ⟨⟨_, u, q, hq⟩, ⟨(Fin.castAddEmb k).trans (Fin.castAddEmb k'), htuple, htype⟩,
    g0.trans (Fin.castAddEmb k'), ?_⟩
  aesop

/-- Convenience wrapper of `exists_labelledExt_le` for a full model. -/
theorem IsModel.exists_labelledExt_le (hR : R.IsModel) (x : R.LabelledExt) {m : ℕ}
    (s : Fin m ↪ M) :
    ∃ y : R.LabelledExt, x ≤ y ∧ ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s :=
  KnightRealization.exists_labelledExt_le hR.consistent hR.covering x s

/-- **Headline 1 — model-internal directedness** (minimal hypotheses — clauses (2) and (3)
suffice): any two labelled covers have a common labelled extension.  Cor. 5.3.8's printed
"amalgamation" citation is replaced by this theorem; no §4.3, no `ExtendsDomain`, no
producer. -/
theorem directed_labelledExt (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x y : R.LabelledExt) :
    ∃ z : R.LabelledExt, x ≤ z ∧ y ≤ z := by
  obtain ⟨z, hxz, g, hg⟩ := exists_labelledExt_le hcons hcov x y.tuple
  refine ⟨z, hxz, g, hg, ?_⟩
  have h := hcons z.tuple z.type g z.eval_eq
  rw [hg, y.eval_eq] at h
  tauto

/-- A covering realization has labelled covers (clause (3) alone suffices: it labels an
extension of the empty tuple). -/
theorem nonempty_labelledExt (hcov : R.IsInitialSegmentCovering) : Nonempty R.LabelledExt := by
  obtain ⟨k, u, -, husome⟩ := hcov (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp husome
  exact ⟨⟨_, u, q, hq⟩⟩

/-- A set of labelled covers is **dominating** when every labelled cover has a member above it
(Def. 5.3.9's "dominating set"; for a model this quantification over labelled covers agrees
with quantification over arbitrary tuples, `isDominating_iff` — the form
`StabilizesTo` uses). -/
def IsDominating (D : Set R.LabelledExt) : Prop :=
  ∀ x : R.LabelledExt, ∃ y ∈ D, x ≤ y

/-- A set of labelled covers is **coinitial** when above every labelled cover it contains a
whole principal tail (Cor. 5.3.8's "coinitial set"): every cover has an extension past which
*all* covers are members.  Unlike dominating sets, coinitial sets are closed under finite
intersection (`IsCoinitial.inter`) — they form a filter with the tails
(`isCoinitial_tail`). -/
def IsCoinitial (D : Set R.LabelledExt) : Prop :=
  ∀ x : R.LabelledExt, ∃ y, x ≤ y ∧ y.tail ⊆ D

/-- The actual cover order supplies Mathlib's directed-order interface. -/
theorem labelledExt_isDirectedOrder (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) : IsDirectedOrder R.LabelledExt :=
  ⟨directed_labelledExt hcons hcov⟩

/-- Knight's coinitial tails are precisely eventual properties of the cover filter. -/
theorem isCoinitial_iff_eventually (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (D : Set R.LabelledExt) :
    IsCoinitial D ↔ ∀ᶠ x in Filter.atTop, x ∈ D := by
  let := nonempty_labelledExt hcov
  let := labelledExt_isDirectedOrder hcons hcov
  constructor
  · intro h
    obtain ⟨y, _, hy⟩ := h (Classical.arbitrary R.LabelledExt)
    aesop
  · intro h x
    obtain ⟨y, hy⟩ := Filter.eventually_atTop.mp h
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x y
    exact ⟨z, hxz, fun w hw => hy w (hyz.trans hw)⟩

/-- The **stabilization set** of a cell: the labelled covers extending `x` on which the
transported cell has provisional value `γ` (relationally, `IsProvisionalValue` — no chooser).
This is Def. 5.3.9's value set as a subset of the labelled-cover poset; `StabilizesTo` says
exactly that it is dominating (`stabilizesTo_iff_isDominating`).  Every member lies
above `x` by construction. -/
def stableSet (x : R.LabelledExt) (Xi : Cell x.type.scheme.scheme) (γ : ExtOrd) :
    Set R.LabelledExt :=
  {y | ∃ (f : Fin x.arity ↪ Fin y.arity) (_ : f.trans y.tuple = x.tuple)
    (hpq : typeMap f y.type = some x.type),
    y.type.IsProvisionalValue (mapCell hpq Xi) γ}

/-- **Def. 5.3.9's dominating form is poset domination** (minimal hypotheses — clauses (2)
and (3) suffice): the provisional values of `Ξ` stabilize to `γ` over `x` (`StabilizesTo`,
quantifying over arbitrary tuples) iff the stabilization set is dominating in the
labelled-cover poset.  This pins the ambient poset of the §5.3 arguments once: the coinitial
upgrade (headline 2) and tail intersections (headline 3) then apply to these sets as soon as
the Lemma 5.3.7 ratchet instance lands. -/
theorem stabilizesTo_iff_isDominating (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt)
    (Xi : Cell x.type.scheme.scheme) (γ : ExtOrd) :
    R.StabilizesTo x.tuple x.type Xi γ ↔ IsDominating (stableSet x Xi γ) := by
  constructor
  · intro H x'
    obtain ⟨m', u, g, f, q, hpq, hq, hgu, hfu, hval⟩ := H x'.tuple
    refine ⟨⟨_, u, q, hq⟩, ⟨f, hfu, hpq, hval⟩, g, hgu, ?_⟩
    have h := hcons u q g hq
    rw [hgu, x'.eval_eq] at h
    tauto
  · intro hD m s
    obtain ⟨k, u₀, hu₀, husome⟩ := hcov s
    obtain ⟨q₀, hq₀⟩ := Option.isSome_iff_exists.mp husome
    obtain ⟨z, hzD, e, he, -⟩ := hD ⟨_, u₀, q₀, hq₀⟩
    have he' : e.trans z.tuple = u₀ := he
    obtain ⟨f, hf, hpq, hval⟩ := hzD
    refine ⟨z.arity, z.tuple, (Fin.castAddEmb k).trans e, f, z.type, hpq, z.eval_eq, ?_,
      hf, hval⟩
    rwa [Function.Embedding.trans_assoc, he']

/-- The **growth set** at threshold `K`: the labelled covers whose label has top grade
(Def. 5.3.1's `K^p`) strictly above `K`.  Upward closed by `topGrade_mono`. -/
def growthSet (R : KnightRealization α M) (K : ℕ) : Set R.LabelledExt :=
  {y | K < y.type.topGrade}

/-- The **growth branch** of Lemma 5.3.10's dichotomy, in dominating form (mirroring
`StabilizesTo`): for every `K` there are dominating covers of top grade `> K`.  The
alternative branch — `K^q` eventually constant — is Case 1 of Lemma 5.3.10 (no second witness
needed); the split between them is classical control flow in the consumer (#51 boundary 3),
never a theorem-milestone here. -/
def HasTopGradeGrowth (R : KnightRealization α M) : Prop :=
  ∀ K : ℕ, IsDominating (R.growthSet K)

end KnightRealization

end VaughtConjecture.Knight
