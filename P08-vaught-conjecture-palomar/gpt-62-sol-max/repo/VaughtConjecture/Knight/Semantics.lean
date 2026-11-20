/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Cell
public import VaughtConjecture.Knight.Transform

@[expose] public section

namespace VaughtConjecture.Knight

open Transform

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- A semantics on a cell scheme `D` (Knight, Def. 2.5.3, lightweight version): for each cell
`Sig`, the **semantic row** `E Sig` is a labelling of the cells below `Sig`, orderly at their
grades. -/
structure Semantics (D : CellScheme A) where
  /-- The semantic row of each cell, a labelling of the cells below it. -/
  E : (Sig : Cell D) → (D.below (D.cell Sig) → ExtOrd)
  /-- Each semantic row is orderly at the grades of its cells. -/
  orderly : ∀ Sig : Cell D,
    IsOrderly (fun d : D.below (D.cell Sig) => D.grade d.1) (E Sig)

variable {D : CellScheme A}

/-- Extensionality: two semantics on the same scheme are equal when their rows agree
(`orderly` is a proof). -/
@[ext]
theorem Semantics.ext {s₁ s₂ : Semantics D} (h_E : s₁.E = s₂.E) : s₁ = s₂ := by
  obtain ⟨E₁, _⟩ := s₁
  obtain ⟨E₂, _⟩ := s₂
  subst h_E; rfl

/-- A labelling `p` of the cells **respects** the semantics `sem` (Knight, Def. 2.5.4, all
clauses): `p` is orderly; **locality** — for every cell `Sig` the semantic row `sem.E Sig`
transforms (Def. 2.3.9) to the labelling `d ↦ min (p d) (p Sig)` of the cells below `Sig`;
**availability** — whenever `Sig` and `Xi₀` are cells with `D.scope Sig ⊆ D.scope Xi₀` and the
same grade (so `Xi₀` witnesses that `D^{scope Xi₀, grade Sig}` is non-empty), some cell `Xi`
with the graded index of `Xi₀` has `p Sig ≤ p Xi`. -/
structure RespectsSemantics (sem : Semantics D) (p : Cell D → ExtOrd) : Prop where
  /-- `p` is orderly on the whole scheme. -/
  orderly : IsOrderly D.grade p
  /-- Locality (Def. 2.5.4(1)): each semantic row transforms to `p` below `Sig`, capped by
  `p Sig`. -/
  locality :
    ∀ Sig : Cell D,
      TransformsTo (fun d : D.below (D.cell Sig) => D.grade d.1)
        (sem.E Sig)
        (fun d => min (p d.1) (p Sig))
  /-- Availability (Def. 2.5.4(2)): a label at scope `C` and grade `i` is dominated by a label
  at every larger scope `B ⊇ C` (in the plan) at which grade `i` occurs. -/
  availability :
    ∀ Sig Xi₀ : Cell D, D.scope Sig ⊆ D.scope Xi₀ → D.grade Sig = D.grade Xi₀ →
      ∃ Xi : Cell D, D.cell Xi = D.cell Xi₀ ∧ p Sig ≤ p Xi

/-- The identically bottom labelling respects every semantics. -/
theorem RespectsSemantics.bot {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) : RespectsSemantics sem (fun _ => ⊥) where
  orderly _ := (Value.extVisibilityReplace_bot _ _).symm
  locality c := TransformsTo.to_bot (sem.E c)
  availability _ Xi₀ _ _ := ⟨Xi₀, rfl, le_rfl⟩

/-- The row of `sem` at a cell `Sig` of the lower set `D.below BJ` has domain
`D.below (D.cell Sig)`, which embeds in `D.below BJ` (`GradedLe.trans`): this is the
restricted scheme's own "below" of `Sig`, `D⟨B,j⟩⟨Sig⟩ = D⟨Sig⟩`. -/
def CellScheme.below.incl {BJ : Finset ι × ℕ} (Sig : D.below BJ)
    (d : D.below (D.cell Sig.1)) : D.below BJ :=
  ⟨d.1, d.2.trans Sig.2⟩

/-- A labelling `r` of the lower set `D.below BJ` respects the **restricted semantics**
`E⟨B,j⟩` of `D⟨B,j⟩` (Knight, Def. 2.5.4 applied to the restricted scheme `D⟨B,j⟩`, whose
cells are `D.below BJ` and whose rows are the rows of `sem` at those cells): `r` is orderly
at the grades; locality — for each `Sig` below `BJ`, the row `sem.E Sig` transforms to
`d ↦ min (r d) (r Sig)` on `D.below (D.cell Sig)`; availability within `D.below BJ`. -/
structure RespectsSemanticsBelow (sem : Semantics D) (BJ : Finset ι × ℕ)
    (r : D.below BJ → ExtOrd) : Prop where
  /-- `r` is orderly on the lower set. -/
  orderly : IsOrderly (fun d : D.below BJ => D.grade d.1) r
  /-- Locality in the restricted scheme. -/
  locality :
    ∀ Sig : D.below BJ,
      TransformsTo (fun d : D.below (D.cell Sig.1) => D.grade d.1)
        (sem.E Sig.1)
        (fun d => min (r (CellScheme.below.incl Sig d)) (r Sig))
  /-- Availability in the restricted scheme. -/
  availability :
    ∀ Sig Xi₀ : D.below BJ, D.scope Sig.1 ⊆ D.scope Xi₀.1 → D.grade Sig.1 = D.grade Xi₀.1 →
      ∃ Xi : D.below BJ, D.cell Xi.1 = D.cell Xi₀.1 ∧ r Sig ≤ r Xi

/-- A labelling respecting the semantics of the whole scheme (Def. 2.5.4) respects the
restricted semantics `E⟨B,j⟩` on every lower set (the converse of
`RespectsSemanticsBelow.toRespects`, with no hypothesis on `BJ`): locality and orderliness
are read off the underlying cells, and the availability witness — which has the graded index of
`Xi₀` — lies in the lower set. -/
theorem RespectsSemantics.toBelow {sem : Semantics D} {p : Cell D → ExtOrd}
    (h : RespectsSemantics sem p) (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow sem BJ (fun d => p d.1) where
  orderly d := h.orderly d.1
  locality Sig := h.locality Sig.1
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := h.availability Sig.1 Xi₀.1 hs hg
    exact ⟨⟨Xi, hc ▸ Xi₀.2⟩, hc, hle⟩

/-- A labelling of a lower set containing every cell respects the semantics (Def. 2.5.4) as a
labelling of the whole scheme when it respects the restricted semantics `E⟨B,j⟩`
(`RespectsSemanticsBelow`).  This is the case `D⟨A,|A|⟩ = D` used by Prop. 4.3.24. -/
theorem RespectsSemanticsBelow.toRespects {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r)
    (hall : ∀ d : Cell D, GradedLe (D.cell d) BJ) :
    RespectsSemantics sem (fun d => r ⟨d, hall d⟩) where
  orderly d := h.orderly ⟨d, hall d⟩
  locality Sig := h.locality ⟨Sig, hall Sig⟩
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := h.availability ⟨Sig, hall Sig⟩ ⟨Xi₀, hall Xi₀⟩ hs hg
    tauto

/-- Checking the section at each row's own lower domain suffices. -/
theorem RespectsSemanticsBelow.of_local {sem : Semantics D} {J : Finset ι × ℕ}
    {p : D.below J → ExtOrd}
    (h : ∀ c : D.below J, RespectsSemanticsBelow sem (D.cell c.1) (p ∘ c.incl)) :
    RespectsSemanticsBelow sem J p where
  orderly c := (h c).orderly ⟨c.1, GradedLe.refl _⟩
  locality c := (h c).locality ⟨c.1, GradedLe.refl _⟩
  availability c t hs hg := by
    obtain ⟨w, hw, hv⟩ := (h t).availability ⟨c.1, hs, hg.le⟩ ⟨t.1, GradedLe.refl _⟩ hs hg
    exact ⟨t.incl w, hw, hv⟩

theorem RespectsSemantics.of_local {sem : Semantics D} {p : Cell D → ExtOrd}
    (h : ∀ c, RespectsSemanticsBelow sem (D.cell c) (fun d => p d.1)) :
    RespectsSemantics sem p :=
  (RespectsSemanticsBelow.of_local (J := (A, A.card)) (p := fun d => p d.1) (fun c => h c.1)).toRespects
    (fun d => ⟨D.scope_subset d, (D.grade_le_card_scope d).trans (Finset.card_le_card (D.scope_subset d))⟩)

/-- Change the index of a lawful lower section along an equality. -/
theorem RespectsSemanticsBelow.cast_index {sem : Semantics D} {J K : Finset ι × ℕ}
    {p : D.below J → ExtOrd} (hp : RespectsSemanticsBelow sem J p) (h : J = K) :
    RespectsSemanticsBelow sem K (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := by aesop

/-- The all-bottom labelling is lawful on every lower set of any semantics. -/
theorem RespectsSemanticsBelow.bot (sem : Semantics D) (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => ⊥) :=
  (RespectsSemantics.bot sem).toBelow BJ

/-- A bottom diagonal forces a bottom label, regardless of the other rows. -/
theorem RespectsSemanticsBelow.eq_bot_of_diagonal {sem : Semantics D} {BJ : Finset ι × ℕ}
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r) (c : D.below BJ)
    (hc : sem.E c.1 ⟨c.1, GradedLe.refl _⟩ = ⊥) : r c = ⊥ := by
  obtain ⟨g, σ, _, _, hbot, _, _, heq⟩ := h.locality c
  have hread := heq ⟨c.1, GradedLe.refl _⟩
  change min (r c) (r c) = min (σ (sem.E c.1 ⟨c.1, GradedLe.refl _⟩)) _ at hread
  grind

/-- A semantics is **consistent** (Knight, Def. 2.5.12): for every cell `Sig` with graded
index `(B, j)`, the row `E Sig`, a labelling of `D⟨B,j⟩ = D.below (D.cell Sig)`, respects the
restricted semantics `E⟨B,j⟩` (`RespectsSemanticsBelow`).  (Orderliness of the row is already
`sem.orderly Sig`.) -/
def Semantics.IsConsistent (sem : Semantics D) : Prop :=
  ∀ Sig : Cell D, RespectsSemanticsBelow sem (D.cell Sig) (sem.E Sig)

/-- Two values of a semantic row at propositionally equal indices are equal (Knight-VC
`sem_E_congr`; the index of `E` is dependent, so this is stated with both equalities). -/
theorem Semantics.E_congr (sem : Semantics D) {a b : Cell D} (hab : a = b) {c d : Cell D}
    {hc : GradedLe (D.cell c) (D.cell a)} {hd : GradedLe (D.cell d) (D.cell b)} (hcd : c = d) :
    sem.E a ⟨c, hc⟩ = sem.E b ⟨d, hd⟩ := by aesop

/-- Faithful respect of semantics is preserved by the strict vertical truncation of the
labelling at a limit stage `α`, **with the semantics fixed** (the reduction half of
Lemma 3.1.3, rows kept as in the paper): if `p` respects `sem` then so does `truncExt α ∘ p`.
Orderliness is `truncExt_preserves_selfVis`; locality is `TransformsTo.truncExt_target`
(the truncated labelling below `Sig` capped at the truncated `p Sig` is the truncation of the
capped labelling, `truncExt_min`); availability is monotonicity of `truncExt α`. -/
theorem RespectsSemantics.truncate {sem : Semantics D} {p : Cell D → ExtOrd}
    {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) (h : RespectsSemantics sem p) :
    RespectsSemantics sem (Value.truncExt α ∘ p) where
  orderly d := (Value.truncExt_preserves_selfVis α (p d) (D.grade d) (h.orderly d).symm).symm
  locality Sig := by
    have key := (h.locality Sig).truncExt_target hα
    have heq : Value.truncExt α ∘ (fun d : D.below (D.cell Sig) => min (p d.1) (p Sig)) =
        fun d => min ((Value.truncExt α ∘ p) d.1) ((Value.truncExt α ∘ p) Sig) := by
      funext d
      simp only [Function.comp_apply, Value.truncExt_min]
    simp_all
  availability Sig Xi₀ hscope hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hscope hgrade
    exact ⟨Xi, hcell, Value.truncExt_mono α hle⟩

section RestrictFace

open CellScheme.restrictFace (toCell belowMap)

variable {m n : ℕ} {D : CellScheme (ι := Fin n) Finset.univ} {f : Fin m ↪ Fin n}
  {hr : Finset.univ.image f ∈ D.plan}

/-- The rows of `D` restricted to the face `f`: the row of a restricted cell `Sig` is the row
of its underlying cell `toCell Sig`, read at the underlying cells (Knight, Def. 3.1.5; the
row part of Knight-VC `typeMap`). -/
noncomputable def Semantics.restrictFace (sem : Semantics D) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ D.plan) : Semantics (D.restrictFace f hr) where
  E Sig d := sem.E (toCell D f hr Sig) (belowMap D f hr Sig d)
  orderly Sig d := sem.orderly (toCell D f hr Sig) (belowMap D f hr Sig d)

@[simp] theorem Semantics.restrictFace_E (sem : Semantics D) (Sig : Cell (D.restrictFace f hr))
    (d : (D.restrictFace f hr).below ((D.restrictFace f hr).cell Sig)) :
    (sem.restrictFace f hr).E Sig d = sem.E (toCell D f hr Sig) (belowMap D f hr Sig d) := rfl

end RestrictFace

/-- `TransformsTo` is invariant under propositional equality of its three functions. -/
theorem transformsTo_congr {D : Type*} {g g' : D → ℕ} {p p' q q' : D → ExtOrd} (hg : g = g')
    (hp : p = p') (hq : q = q') (h : TransformsTo g p q) : TransformsTo g' p' q' := by lia

section Transport

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {sem' : Semantics D'}

/-- The graded order is reflected and preserved by a bijection preserving scopes and grades. -/
theorem gradedLe_iff_of_equiv {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (a b : D'.below BJ) :
    GradedLe (D'.cell a.1) (D'.cell b.1) ↔ GradedLe (D.cell (e a).1) (D.cell (e b).1) := by
  change (D'.scope a.1 ⊆ D'.scope b.1 ∧ D'.grade a.1 ≤ D'.grade b.1) ↔
    (D.scope (e a).1 ⊆ D.scope (e b).1 ∧ D.grade (e a).1 ≤ D.grade (e b).1)
  rw [hscope, hgrade a, hgrade b]

/-- **Respect transports along a bijection of lower sets with agreeing rows.** -/
theorem RespectsSemanticsBelow.of_equiv {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (hrows : ∀ (Sig : D'.below BJ) (d : D'.below (D'.cell Sig.1))
      (hd : GradedLe (D.cell (e ⟨d.1, d.2.trans Sig.2⟩).1) (D.cell (e Sig).1)),
      sem'.E Sig.1 d = sem.E (e Sig).1 ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩)
    {q : D.below BJ' → ExtOrd} (hq : RespectsSemanticsBelow sem BJ' q) :
    RespectsSemanticsBelow sem' BJ (fun a => q (e a)) where
  orderly a := by
    have := hq.orderly (e a)
    grind
  locality Sig := by
    let φ : D'.below (D'.cell Sig.1) → D.below (D.cell (e Sig).1) := fun d =>
      ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, (gradedLe_iff_of_equiv e hgrade hscope _ _).mp d.2⟩
    have key := (hq.locality (e Sig)).reindex φ
    refine transformsTo_congr ?_ ?_ ?_ key
    · funext d
      exact (hgrade ⟨d.1, d.2.trans Sig.2⟩).symm
    · funext d
      exact (hrows Sig d _).symm
    · funext d
      rfl
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hcell, hle⟩ := hq.availability (e Sig) (e Xi₀) ((hscope _ _).mp hs)
      (by rw [← hgrade, ← hgrade]; exact hg)
    refine ⟨e.symm Xi, ?_, ?_⟩
    · apply GradedLe.antisymm'
      · rw [gradedLe_iff_of_equiv e hgrade hscope, e.apply_symm_apply, hcell]
        trivial
      · rw [gradedLe_iff_of_equiv e hgrade hscope, e.apply_symm_apply, hcell]
        trivial
    simp_all

end Transport

section Transport2

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} {sem : Semantics D} {sem' : Semantics D'}

/-- **Respect transports both ways** along a bijection with agreeing rows. -/
theorem respects_iff_of_equiv {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}
    (e : D'.below BJ ≃ D.below BJ') (hgrade : ∀ a, D'.grade a.1 = D.grade (e a).1)
    (hscope : ∀ a b, D'.scope a.1 ⊆ D'.scope b.1 ↔ D.scope (e a).1 ⊆ D.scope (e b).1)
    (hrows : ∀ (Sig : D'.below BJ) (d : D'.below (D'.cell Sig.1))
      (hd : GradedLe (D.cell (e ⟨d.1, d.2.trans Sig.2⟩).1) (D.cell (e Sig).1)),
      sem'.E Sig.1 d = sem.E (e Sig).1 ⟨(e ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩)
    (q : D'.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem' BJ q ↔ RespectsSemanticsBelow sem BJ' (q ∘ e.symm) := by
  constructor
  · intro hq
    refine RespectsSemanticsBelow.of_equiv (sem := sem') (sem' := sem) e.symm
      (fun b => by rw [hgrade (e.symm b), e.apply_symm_apply])
      (fun a b => by rw [hscope (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply])
      ?_ hq
    intro Sig d hd
    have hv1 : (e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1 = d.1 :=
      congrArg Subtype.val (e.apply_symm_apply ⟨d.1, d.2.trans Sig.2⟩)
    have hv2 : (e (e.symm Sig)).1 = Sig.1 := congrArg Subtype.val (e.apply_symm_apply Sig)
    have hd0 : GradedLe (D.cell (e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1)
        (D.cell (e (e.symm Sig)).1) := by
      rw [hv1, hv2]; exact d.2
    have h1 := hrows (e.symm Sig) ⟨(e.symm ⟨d.1, d.2.trans Sig.2⟩).1, hd⟩ hd0
    have h2 : sem.E Sig.1 d =
        sem.E (e (e.symm Sig)).1 ⟨(e (e.symm ⟨d.1, d.2.trans Sig.2⟩)).1, hd0⟩ :=
      sem.E_congr hv2.symm hv1.symm
    exact h2.trans h1.symm
  · intro hq
    have := RespectsSemanticsBelow.of_equiv e hgrade hscope hrows hq
    convert this using 1
    funext a
    change q a = q (e.symm (e a))
    rw [e.symm_apply_apply]

end Transport2

/-- When the cell indices are literal, grade and inclusion transport are automatic. -/
theorem respects_iff_of_index_equiv {ι : Type*} [DecidableEq ι] {A B : Finset ι}
    {D : CellScheme A} {E : CellScheme B} {rd : Semantics D} {re : Semantics E}
    {I J : Finset ι × ℕ} (e : D.below I ≃ E.below J)
    (index : ∀ d, E.cell (e d).1 = D.cell d.1)
    (rows : ∀ (c : D.below I) (d : D.below (D.cell c.1))
      (h : GradedLe (E.cell (e ⟨d.1, d.2.trans c.2⟩).1) (E.cell (e c).1)),
      rd.E c.1 d = re.E (e c).1 ⟨(e ⟨d.1, d.2.trans c.2⟩).1, h⟩)
    (p : D.below I → ExtOrd) :
    RespectsSemanticsBelow rd I p ↔ RespectsSemanticsBelow re J (p ∘ e.symm) :=
  respects_iff_of_equiv e (fun d => (congrArg Prod.snd (index d)).symm)
    (fun d f => by simp only [CellScheme.scope, index]) rows p

/-- Exchange a pullback equivalence for the inverse pullback equivalence. -/
theorem iff_comp_symm {α β γ : Type*} (e : α ≃ β)
    {P : (β → γ) → Prop} {Q : (α → γ) → Prop}
    (h : ∀ p, P p ↔ Q (p ∘ e)) (q : α → γ) : Q q ↔ P (q ∘ e.symm) := by
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using (h (q ∘ e.symm)).symm

end VaughtConjecture.Knight
