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

@[expose] public section

namespace VaughtConjecture.Knight

open StageType AmalgamationPlan.Plan

variable {α : Ordinal.{0}} {n : ℕ}

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

/-- The canonical coatom pair at a point `a : Fin (n+2)` and a point `b'` of the `a`-face:
the coatoms omit `a` and `b := a.succAbove b'`; the lower face omits `b'` inside the first and
`b'.predAbove a` inside the second.  Commutation is
`Fin.succAbove_succAbove_succAbove_predAbove`. -/
def ofPoints (a : Fin (n + 2)) (b' : Fin (n + 1)) : CoatomPair n where
  f₁ := Fin.succAboveEmb a
  f₂ := Fin.succAboveEmb (a.succAbove b')
  g₁ := Fin.succAboveEmb b'
  g₂ := Fin.succAboveEmb (b'.predAbove a)
  comm := by
    refine Function.Embedding.ext fun k => ?_
    simp only [Function.Embedding.trans_apply, Fin.succAboveEmb_apply]
    exact (Fin.succAbove_succAbove_succAbove_predAbove a b' k).symm
  ne := by simp

@[simp] theorem ofPoints_g₂ (a : Fin (n + 2)) (b' : Fin (n + 1)) :
    (ofPoints a b').g₂ = Fin.succAboveEmb (b'.predAbove a) := rfl

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

/-- The range of `Fin.succAboveEmb p` is the coatom omitting `p`. -/
theorem image_succAboveEmb (p : Fin (n + 1)) :
    Finset.univ.image (Fin.succAboveEmb p) = Finset.univ.erase p := by aesop

/-- Every plan on `Fin (n+1)` has a visible coatom: for `n = 0` the empty face, otherwise a
pivot of the step decomposition (`IsPlan.pivot_pair`). -/
theorem exists_erase_mem_plan (C : CellScheme (ι := Fin (n + 1)) Finset.univ) :
    ∃ b' : Fin (n + 1), Finset.univ.erase b' ∈ C.plan := by
  cases n with
  | zero => exact ⟨0, by simpa using C.isPlan.empty_mem⟩
  | succ n =>
    obtain ⟨a, b, ha, -, -, hz, -, -⟩ := C.isPlan.pivot_pair (by simp)
    simp_all

/-- The one-point face at `a`. -/
def pointEmb (a : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => a, fun i j _ => Subsingleton.elim i j⟩

theorem pointEmb_fin_one (a : Fin 1) : pointEmb a = Function.Embedding.refl (Fin 1) :=
  Function.Embedding.ext fun _ => Subsingleton.elim _ _

/-- The one-point face at `a` factors through the second coatom of the canonical pair at
`(a, b')` (`Fin.succAbove_succAbove_predAbove`). -/
theorem pointEmb_eq_trans (a : Fin (n + 2)) (b' : Fin (n + 1)) :
    pointEmb a = (pointEmb (b'.predAbove a)).trans (Fin.succAboveEmb (a.succAbove b')) :=
  Function.Embedding.ext fun _ => (Fin.succAbove_succAbove_predAbove a b').symm

/-- The initial face `Fin.castSuccEmb` is the coatom omitting the last point. -/
theorem castSuccEmb_eq_succAboveEmb_last :
    (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) = Fin.succAboveEmb (Fin.last n) :=
  by aesop

/-- The empty face is visible in every plan. -/
theorem image_fin_zero_mem_plan (f : Fin 0 ↪ Fin n)
    (C : CellScheme (ι := Fin n) Finset.univ) : Finset.univ.image f ∈ C.plan := by
  simpa using C.isPlan.empty_mem

/-- **Finite joint amalgamation with a one-point type**: from the supply, for every point
`a : Fin (n+2)`, every `p : S α (n+1)` on the coatom omitting `a` and every one-point type
`r : S α 1`, there is `q : S α (n+2)` with `q ↾ (A∖{a}) = p`, `q ↾ {a} = r` and a maximal
full cell.  Induction on `n`; the second coatom is a pivot of `dom p`. -/
theorem exists_amalgam_point (H : MaximalCoatomAmalgamationSupply α) :
    ∀ (n : ℕ) (a : Fin (n + 2)) (p : S α (n + 1)) (r : S α 1),
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

/-- Every `r : S α 1` is a coface of the unique `p : S α 0`. -/
theorem isCoface_zero (p : S α 0) (r : S α 1) : IsCoface p r := by
  rw [IsCoface, typeMap_eq_some _ r (image_fin_zero_mem_plan _ _)]
  exact congrArg some (Subsingleton.elim _ _)

/-- A one-point type's cells have grade `1`. -/
theorem grade_eq_one (r : S α 1) (Sig : Cell r.scheme.scheme) :
    r.scheme.scheme.grade Sig = 1 := by
  have h₁ := r.scheme.scheme.grade_pos Sig
  have h₂ := r.scheme.scheme.grade_le_card_scope Sig
  have h₃ : (r.scheme.scheme.scope Sig).card ≤ 1 :=
    (Finset.card_le_univ _).trans (by simp)
  omega

/-- A label of the `{a}`-face of `q` is a label of `q`: the amalgam's cells include the cells
of its one-point face, with the same labels (`restrictFace_label`). -/
theorem exists_label_eq_of_typeMap_point {q : S α (n + 2)} {a : Fin (n + 2)} {r : S α 1}
    (h : typeMap (pointEmb a) q = some r) (Sig : Cell r.scheme.scheme) :
    ∃ d : Cell q.scheme.scheme, q.label d = r.label Sig := by
  have hvis : Finset.univ.image (pointEmb a) ∈ q.scheme.scheme.plan :=
    (typeMap_isSome_iff _ q).mp (by simp_all)
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
    rwa [IsCoface, castSuccEmb_eq_succAboveEmb_last]

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
    refine ⟨q, ⟨Ξ, hΞ, by grind⟩, ?_⟩
    rwa [IsCoface, castSuccEmb_eq_succAboveEmb_last]

end VaughtConjecture.Knight
