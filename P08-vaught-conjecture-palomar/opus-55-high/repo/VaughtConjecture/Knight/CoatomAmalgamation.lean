/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Fin.SuccPred
public import VaughtConjecture.Knight.Coface
public import VaughtConjecture.Knight.Model
public import VaughtConjecture.Knight.OnePointSuccessor

/-! # Coatom amalgamation: the faithful receiver for Cor. 4.3.22

The paper's §4.3 completion ends in **Corollary 4.3.22**: if `pa ∈ S^α(A∖{a})` and
`pb ∈ S^α(A∖{b})` agree on the common lower face, `(pa)_b = (pb)_a`, then some `q ∈ S^α_A` has
`q_a = pa`, `q_b = pb`, and a cell `Ξ ∈ D'^{A,|A|}` (full scope, full grade) with
`q(Ξ) = max ran q`.  The contribution of Cor. 4.3.22 to the paper's later arguments — coface
existence (Prop. 4.3.23), the uniformity and high-arity dominance candidates
(Lemmas 4.4.2/4.4.3), and the countable model recursion (Prop. 4.4.5) — is consumed through this
statement; those arguments have further inputs of their own, recorded below.  This module states
it as a receiver on V-C's own objects and proves the first tier of consumers.

## The live coatom geometry

A plan on a set of size `≥ 2` has **exactly two** visible coatoms, the pivots `A∖{a}` and
`A∖{b}` of its step decomposition, and their intersection `A∖{a,b}` is visible in both
sub-plans (`IsPlan.pivot_pair`, Def. 2.1.1).  So the two inputs of the amalgamation are two
`(n+1)`-ary faces of an `(n+2)`-ary filler, not an `(n+1)`-type against a one-point type: a
`CoatomPair n` carries the two coatom embeddings `f₁ f₂ : Fin (n+1) ↪ Fin (n+2)` with distinct
ranges and explicit embeddings `g₁ g₂ : Fin n ↪ Fin (n+1)` of the common lower face, commuting
(`g₁.trans f₁ = g₂.trans f₂`).  Compatibility is the literal face equality
`typeMap g₁ pa = some r = typeMap g₂ pb` (Def. 3.1.5's partial restriction; the lower face is
visible on both sides by Def. 2.1.1(3)(a)), and the amalgam is asserted by the two literal face
equalities `typeMap f₁ q = some pa`, `typeMap f₂ q = some pb` (`CoatomPair.IsAmalgam`) together
with the maximal full cell (`StageType.HasMaximalFullCell`).

`MaximalCoatomAmalgamationSupply α` is the receiver: the corollary at every `n`, every coatom
pair, every compatible pair.  It is a **consumer** of the §4.3 construction — nothing here
builds a filler — and it is stated with no reference to the construction's internals
(stacks, caps, raw rows, decoders).

## Consumers proved here (Prop. 4.3.23 and Lemmas 4.4.2/4.4.3, faithfully)

* `CoatomPair.ofPoints a b'`: the canonical pair at a point `a` and a pivot `b'` of the
  `a`-face, with the lower-face embeddings `succAbove` and `predAbove`; commutation is
  Mathlib's `Fin.succAbove_succAbove_succAbove_predAbove`.
* `exists_amalgam_point` (**finite joint amalgamation**, the recursion of Prop. 4.3.23 and
  of "recursively amalgamated" in Lemma 4.4.3): from the supply, every `p : S α (n+1)` at the
  coatom `A∖{a}` and every one-point type `r : S α 1` at `{a}` have a common filler
  `q : S α (n+2)` with a maximal full cell.  Induction on `n`: a pivot of `dom p` supplies
  the second coatom (`exists_erase_mem_plan`), the induction hypothesis amalgamates the
  restriction of `p` with `r` on that coatom, and the supply glues.  One-point visibility
  propagates through `typeMap_trans`.
* `exists_isCoface` (Prop. 4.3.23): every `p : S α (n+1)` has a coface, with a maximal full
  cell.
* `exists_uniformity_candidate` / `exists_highGradeDominance_candidate`
  (Lemmas 4.4.2/4.4.3): a one-point type with a label in `[γ, γ+ω)`, resp. above `γ`,
  amalgamates into a coface in `UniformityFamily γ`, resp. `HighGradeDominanceFamily γ`; the
  latter reads the maximal full cell.
* `KnightRealization.hasCandidates_of_coatomAmalgamation`: the full candidate bundle of
  `Knight/ModelAssembly.lean` from the supply alone — the one-point types with label `γ + 1`
  it consumes are Lemma 4.2.2's second clause, compiled in `Knight/OnePointSuccessor.lean`
  (`exists_successorOneType_of_lt`); `hasCandidates_of_coatomAmalgamation_of_onePoint` keeps
  that input explicit.
* `KnightRealization.isModel_of_coatomAmalgamation`: the residual model inputs, exactly.  From
  the supply, a realization is a model as soon as it is exactly parent-consistent, initial-segment
  covering and exact-copy servicing.

## What is deliberately not here

This module does **not** produce `CofinalHighStageModels`: it reduces faithful model construction
to the three realization invariants just named (`isModel_of_candidates`), none of which is implied
by the amalgamation package and none of which is assumed or derived here.  The countable
recursion from the package to `CofinalHighStageModels` is a separate tranche.
Construction-private, not root-exported. -/

@[expose] public section

namespace VaughtConjecture.Knight

open StageType AmalgamationPlan.Plan

variable {α : Ordinal.{0}} {n : ℕ}

/-! ### Coatom pairs -/

/-- A **coatom pair** on `Fin (n+2)`: two coatom faces with distinct ranges, each given by an
embedding of `Fin (n+1)`, together with explicit embeddings of their common lower face into
each of them, commuting into the filler. -/
structure CoatomPair (n : ℕ) where
  /-- The first coatom face. -/
  f₁ : Fin (n + 1) ↪ Fin (n + 2)
  /-- The second coatom face. -/
  f₂ : Fin (n + 1) ↪ Fin (n + 2)
  /-- The common lower face inside the first coatom. -/
  g₁ : Fin n ↪ Fin (n + 1)
  /-- The common lower face inside the second coatom. -/
  g₂ : Fin n ↪ Fin (n + 1)
  /-- The two routes from the lower face into the filler agree. -/
  comm : g₁.trans f₁ = g₂.trans f₂
  /-- The two coatoms are distinct faces. -/
  ne : Finset.univ.image f₁ ≠ Finset.univ.image f₂

namespace CoatomPair

section
variable (a : Fin (n + 2)) (b' : Fin (n + 1))

/-- The canonical coatom pair at a point `a : Fin (n+2)` and a point `b'` of the `a`-face:
the coatoms omit `a` and `b := a.succAbove b'`; the lower face omits `b'` inside the first and
`b'.predAbove a` inside the second.  Commutation is
`Fin.succAbove_succAbove_succAbove_predAbove`. -/
def ofPoints  : CoatomPair n where
  f₁ := Fin.succAboveEmb a
  f₂ := Fin.succAboveEmb (a.succAbove b')
  g₁ := Fin.succAboveEmb b'
  g₂ := Fin.succAboveEmb (b'.predAbove a)
  comm := by
    refine Function.Embedding.ext fun k => ?_
    simp only [Function.Embedding.trans_apply, Fin.succAboveEmb_apply]
    exact (Fin.succAbove_succAbove_succAbove_predAbove a b' k).symm
  ne := by
    intro h
    have hb : a.succAbove b' ∈ Finset.univ.image (Fin.succAboveEmb a) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ b')
    rw [h] at hb
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hb
    exact Fin.succAbove_ne _ k hk

@[simp] theorem ofPoints_g₂  :
    (ofPoints a b').g₂ = Fin.succAboveEmb (b'.predAbove a) := rfl

end

/-- **Compatibility** on the common lower face: both inputs restrict, along their lower-face
embeddings, to one and the same type (`(pa)_b = (pb)_a`). -/
def Compatible (C : CoatomPair n) (pa pb : S α (n + 1)) : Prop :=
  ∃ r : S α n, typeMap C.g₁ pa = some r ∧ typeMap C.g₂ pb = some r

/-- `q` is an **amalgam** of `pa` and `pb` over the coatom pair: both are literal faces of
`q` along the two coatom embeddings (`q_a = pa`, `q_b = pb`). -/
structure IsAmalgam (C : CoatomPair n) (pa pb : S α (n + 1)) (q : S α (n + 2)) : Prop where
  /-- `q` restricts to `pa` along the first coatom. -/
  face₁ : typeMap C.f₁ q = some pa
  /-- `q` restricts to `pb` along the second coatom. -/
  face₂ : typeMap C.f₂ q = some pb

end CoatomPair

/-- A stage type on `n` points **has a maximal full cell** (Cor. 4.3.22's `Ξ ∈ D'^{A,|A|}`
with `q(Ξ) = max ran q`): a cell of grade `n` — hence of full scope,
`CellScheme.scope_eq_univ_of_grade_eq` — whose label dominates every label. -/
def StageType.HasMaximalFullCell (q : S α n) : Prop :=
  ∃ Ξ : Cell q.scheme.scheme, q.scheme.scheme.grade Ξ = n ∧ ∀ d, q.label d ≤ q.label Ξ

/-- **Maximal coatom amalgamation supply** (Knight, Cor. 4.3.22, verbatim on `S α`): at every
`n`, every coatom pair and every compatible pair of `(n+1)`-types has an amalgam in `S α (n+2)`
with a maximal full cell.  This is the receiver for the §4.3 completion; it is consumed below
and produced nowhere in this repository. -/
def MaximalCoatomAmalgamationSupply (α : Ordinal.{0}) : Prop :=
  ∀ (n : ℕ) (C : CoatomPair n) (pa pb : S α (n + 1)), C.Compatible pa pb →
    ∃ q : S α (n + 2), C.IsAmalgam pa pb q ∧ q.HasMaximalFullCell

/-! ### Faces of `Fin`: the pivot coatom and the one-point face -/

/-- The range of `Fin.succAboveEmb p` is the coatom omitting `p`. -/
theorem image_succAboveEmb (p : Fin (n + 1)) :
    Finset.univ.image (Fin.succAboveEmb p) = Finset.univ.erase p := by aesop

/-- Every plan on `Fin (n+1)` has a visible coatom: for `n = 0` the empty face, otherwise a
pivot of the step decomposition (`IsPlan.pivot_pair`). -/
theorem exists_erase_mem_plan (C : CellScheme (ι := Fin (n + 1)) Finset.univ) :
    ∃ b', Finset.univ.erase b' ∈ C.plan := by
  cases n with
  | zero => exact ⟨0, by simpa using C.isPlan.empty_mem⟩
  | succ n =>
    obtain ⟨a, b, ha, -, -, hz, -, -⟩ := C.isPlan.pivot_pair (by simp)
    exact ⟨a, (hz a ha).mpr (Or.inl rfl)⟩

/-- The one-point face at `a`. -/
def pointEmb (a : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => a, fun i j _ => Subsingleton.elim i j⟩

theorem pointEmb_fin_one a : pointEmb a = Function.Embedding.refl (Fin 1) := by aesop

/-- The one-point face at `a` factors through the second coatom of the canonical pair at
`(a, b')` (`Fin.succAbove_succAbove_predAbove`). -/
theorem pointEmb_eq_trans (a : Fin (n + 2)) b' :
    pointEmb a = (pointEmb (b'.predAbove a)).trans (Fin.succAboveEmb (a.succAbove b')) :=
  Function.Embedding.ext fun _ => (Fin.succAbove_succAbove_predAbove a b').symm

/-- The initial face `Fin.castSuccEmb` is the coatom omitting the last point. -/
theorem castSuccEmb_eq_succAboveEmb_last :
    (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) = Fin.succAboveEmb (Fin.last n) := by aesop

/-- The empty face is visible in every plan. -/
theorem image_fin_zero_mem_plan (f : Fin 0 ↪ Fin n)
    (C : CellScheme (ι := Fin n) Finset.univ) : Finset.univ.image f ∈ C.plan := by
  simpa using C.isPlan.empty_mem

/-! ### Finite joint amalgamation (Prop. 4.3.23's recursion) -/

/-- **Finite joint amalgamation with a one-point type**: from the supply, for every point
`a : Fin (n+2)`, every `p : S α (n+1)` on the coatom omitting `a` and every one-point type
`r : S α 1`, there is `q : S α (n+2)` with `q ↾ (A∖{a}) = p`, `q ↾ {a} = r` and a maximal
full cell.  Induction on `n`; the second coatom is a pivot of `dom p`. -/
theorem exists_amalgam_point (H : MaximalCoatomAmalgamationSupply α) :
    ∀ n (a : Fin (n + 2)) p r,
      ∃ q : S α (n + 2), typeMap (Fin.succAboveEmb a) q = some p ∧
        typeMap (pointEmb a) q = some r ∧ q.HasMaximalFullCell := by
  intro n
  induction n with
  | zero =>
    intro a p r
    obtain ⟨b', hb'⟩ := exists_erase_mem_plan p.scheme.scheme
    have hvis : Finset.univ.image (Fin.succAboveEmb b') ∈ p.scheme.scheme.plan := by
      rwa [image_succAboveEmb]
    have hvis' : Finset.univ.image (Fin.succAboveEmb (b'.predAbove a)) ∈
        r.scheme.scheme.plan := image_fin_zero_mem_plan _ _
    obtain ⟨q, hq, hmax⟩ := H 0 (CoatomPair.ofPoints a b') p r
      ⟨p.restrictFace _ hvis, typeMap_eq_some _ p hvis, by
        rw [CoatomPair.ofPoints_g₂, typeMap_eq_some _ r hvis']
        exact congrArg some (Subsingleton.elim _ _)⟩
    have hface₂ : typeMap (Fin.succAboveEmb (a.succAbove b')) q = some r := hq.face₂
    refine ⟨q, hq.face₁, ?_, hmax⟩
    rw [pointEmb_eq_trans a b', ← typeMap_trans _ _ q r hface₂, pointEmb_fin_one,
      typeMap_refl]
  | succ n ih =>
    intro a p r
    obtain ⟨b', hb'⟩ := exists_erase_mem_plan p.scheme.scheme
    have hvis : Finset.univ.image (Fin.succAboveEmb b') ∈ p.scheme.scheme.plan := by
      rwa [image_succAboveEmb]
    obtain ⟨q', hq'₁, hq'₂, -⟩ := ih (b'.predAbove a) (p.restrictFace _ hvis) r
    obtain ⟨q, hq, hmax⟩ := H (n + 1) (CoatomPair.ofPoints a b') p q'
      ⟨p.restrictFace _ hvis, typeMap_eq_some _ p hvis, hq'₁⟩
    have hface₂ : typeMap (Fin.succAboveEmb (a.succAbove b')) q = some q' := hq.face₂
    refine ⟨q, hq.face₁, ?_, hmax⟩
    rw [pointEmb_eq_trans a b', ← typeMap_trans _ _ q q' hface₂, hq'₂]

/-! ### The uniformity and high-grade dominance candidates (Lemmas 4.4.2/4.4.3) -/

/-- Every `r : S α 1` is a coface of the unique `p : S α 0`. -/
theorem isCoface_zero p (r : S α 1) : IsCoface p r := by
  rw [IsCoface, typeMap_eq_some _ r (image_fin_zero_mem_plan _ _)]
  exact congrArg some (Subsingleton.elim _ _)

/-- A one-point type's cells have grade `1`. -/
theorem grade_eq_one (r : S α 1) Sig :
    r.scheme.scheme.grade Sig = 1 := by
  have h₁ := r.scheme.scheme.grade_pos Sig
  have h₂ := r.scheme.scheme.grade_le_card_scope Sig
  have h₃ : (r.scheme.scheme.scope Sig).card ≤ 1 :=
    (Finset.card_le_univ _).trans (by simp)
  omega

/-- A label of the `{a}`-face of `q` is a label of `q`: the amalgam's cells include the cells
of its one-point face, with the same labels (`restrictFace_label`). -/
theorem exists_label_eq_of_typeMap_point {q} {a : Fin (n + 2)} {r : S α 1}
    (h : typeMap (pointEmb a) q = some r) Sig :
    ∃ d, q.label d = r.label Sig := by
  have hvis :=
    (typeMap_isSome_iff _ q).mp (by rw [h]; rfl)
  rw [typeMap_eq_some _ q hvis, Option.some.injEq] at h
  aesop

/-- **Uniformity candidate** (Lemma 4.4.2's amalgamation step): from the supply and a one-point
type with a label in `[γ, γ + ω)`, every `p : S α n` has a coface in `UniformityFamily γ`. -/
theorem exists_uniformity_candidate (H : MaximalCoatomAmalgamationSupply α) (p : S α n)
    {γ : Ordinal.{0}} (r : S α 1) (Sig : Cell r.scheme.scheme)
    (hlo : ExtOrd.ofOrd γ ≤ r.label Sig) (hhi : r.label Sig < ExtOrd.ofOrd (γ + Ordinal.omega0)) :
    ∃ q ∈ UniformityFamily (α := α) γ, IsCoface p q := by
  cases n with
  | zero => exact ⟨r, ⟨Sig, hlo, hhi⟩, isCoface_zero p r⟩
  | succ n =>
    obtain ⟨q, hq, hr, -⟩ := exists_amalgam_point H n (Fin.last (n + 1)) p r
    obtain ⟨d, hd⟩ := exists_label_eq_of_typeMap_point hr Sig
    refine ⟨q, ⟨d, hd ▸ hlo, hd ▸ hhi⟩, ?_⟩
    rw [IsCoface, castSuccEmb_eq_succAboveEmb_last]
    exact hq

/-- **High-grade dominance candidate** (Lemma 4.4.3's amalgamation step): from the supply and a
one-point type with a label above `γ`, every `p : S α n` has a coface in
`HighGradeDominanceFamily γ` — the maximal full cell of the amalgam dominates that label. -/
theorem exists_highGradeDominance_candidate (H : MaximalCoatomAmalgamationSupply α)
    (p : S α n) {γ : Ordinal.{0}} (r : S α 1) (Sig : Cell r.scheme.scheme)
    (hγ : ExtOrd.ofOrd γ < r.label Sig) :
    ∃ q ∈ HighGradeDominanceFamily (α := α) γ, IsCoface p q := by
  cases n with
  | zero => exact ⟨r, ⟨Sig, grade_eq_one r Sig, hγ⟩, isCoface_zero p r⟩
  | succ n =>
    obtain ⟨q, hq, hr, Ξ, hΞ, hmax⟩ := exists_amalgam_point H n (Fin.last (n + 1)) p r
    obtain ⟨d, hd⟩ := exists_label_eq_of_typeMap_point hr Sig
    refine ⟨q, ⟨Ξ, hΞ, lt_of_lt_of_le (hd ▸ hγ) (hmax d)⟩, ?_⟩
    rw [IsCoface, castSuccEmb_eq_succAboveEmb_last]
    exact hq

end VaughtConjecture.Knight
