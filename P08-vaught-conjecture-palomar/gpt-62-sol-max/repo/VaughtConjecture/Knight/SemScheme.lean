/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Semantics

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The inclusion of lower sets along the graded preorder: `D.below X ⊆ D.below Y` when
`X ≤ Y` (the paper's `D⟨C,i⟩ ⊆ D⟨B,j⟩` for `⟨C,i⟩ ≤ ⟨B,j⟩`). -/
def CellScheme.below.mono {X Y : Finset ι × ℕ} (h : GradedLe X Y) (d : D.below X) :
    D.below Y :=
  ⟨d.1, d.2.trans h⟩

/-- **Restriction of respect**: a labelling respecting the restricted semantics `E⟨B,j⟩` restricts
along `D⟨C,i⟩ ⊆ D⟨B,j⟩` to one respecting `E⟨C,i⟩`.  Availability restricts because the ambient
witness has exactly the graded index of the request, hence lies in the smaller lower set. -/
theorem RespectsSemanticsBelow.mono {sem : Semantics D} {CI BJ : Finset ι × ℕ} (h : GradedLe CI BJ)
    {q : D.below BJ → ExtOrd} (hq : RespectsSemanticsBelow sem BJ q) :
    RespectsSemanticsBelow sem CI (fun d => q (CellScheme.below.mono h d)) where
  orderly d := hq.orderly (CellScheme.below.mono h d)
  locality d := hq.locality (CellScheme.below.mono h d)
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, he, hv⟩ :=
      hq.availability (CellScheme.below.mono h Sig) (CellScheme.below.mono h Xi₀) hs hg
    have hm : GradedLe (D.cell Xi.1) CI := by rw [he]; exact Xi₀.2
    exact ⟨⟨Xi.1, hm⟩, he, hv⟩

/-- A semantics is **bountiful** (Knight, Def. 2.5.14; stated for a consistent semantics):
whenever `⟨C,i⟩ ≺ ⟨B,j⟩` in `P̂`, `p` is a labelling of `D⟨C,i⟩` respecting `E⟨C,i⟩`, `q` a
labelling of `D⟨B,j⟩` respecting `E⟨B,j⟩`, `γ` a label with `γ = γ ⊔⁺_j j`, and
`(q ∧ γ) ↾ D⟨C,i⟩ = p ∧ γ`, then there is `q'` on `D⟨B,j⟩` respecting `E⟨B,j⟩` with
`q' ∧ γ = q ∧ γ` and `q' ↾ D⟨C,i⟩ = p`.  Here `D⟨B,j⟩ = D.below BJ`, the inclusion is
`below.mono`, respect of `E⟨B,j⟩` is `RespectsSemanticsBelow`, and `∧ γ` is the pointwise
`min · γ`; the pairs range over the graded plan `P̂`. -/
def Semantics.IsBountiful (sem : Semantics D) : Prop :=
  ∀ (CI BJ : Finset ι × ℕ), CI ∈ Plan.gradedPlan D.plan → BJ ∈ Plan.gradedPlan D.plan →
    (h : GradedLe CI BJ) → CI ≠ BJ →
    ∀ (p : D.below CI → ExtOrd) (q : D.below BJ → ExtOrd) (γ : ExtOrd),
      RespectsSemanticsBelow sem CI p → RespectsSemanticsBelow sem BJ q →
      extVisibilityReplace γ BJ.2 BJ.2 = γ →
      (∀ d : D.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
      ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
        (∀ d : D.below BJ, min (q' d) γ = min (q d) γ) ∧
        (∀ d : D.below CI, q' (CellScheme.below.mono h d) = p d)

/-- A cell scheme is **complete** (Knight, Def. 2.5.15): every graded pair `⟨B,j⟩ ∈ P̂` is
the graded index of some cell (`D^{B,j} ≠ ∅`). -/
def CellScheme.IsComplete (D : CellScheme A) : Prop :=
  ∀ BJ ∈ Plan.gradedPlan D.plan, ∃ d : Cell D, D.cell d = BJ

/-- A label is **coded at grade `k`** (the coding convention of Knight, Lemma 2.5.13 /
Def. 2.6): it is `⊥` or an ordinal `ω·i + j` with `j ≤ k + 1` (no `⊤`). -/
def ExtOrd.IsCodedLabel (k : ℕ) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ ∃ i j : ℕ, j ≤ k + 1 ∧ x = ofOrd (Ordinal.omega0 * i + j)

/-- The set of all coded labels (at any grade): `⊥` and the ordinals `ω·i + j`. -/
def ExtOrd.codedLabels : Set ExtOrd :=
  insert ⊥ (Set.range fun ij : ℕ × ℕ => ofOrd (Ordinal.omega0 * ij.1 + ij.2))

theorem ExtOrd.codedLabels_countable : ExtOrd.codedLabels.Countable :=
  (Set.countable_range _).insert _

theorem ExtOrd.IsCodedLabel.mem_codedLabels {k : ℕ} {x : ExtOrd} (h : IsCodedLabel k x) :
    x ∈ codedLabels := by
  rcases h with rfl | ⟨i, j, -, rfl⟩
  all_goals tauto

/-- A semantics is **coded** (Knight, Lemma 2.5.13: "if `a(Σ) = k`, the range of `E(Σ)` is
contained in `{−∞} ∪ {ωi + j : i ∈ ω, 0 ≤ j ≤ k+1}`"): every value of the row of a cell `Sig`
is a coded label at the grade of `Sig`. -/
def Semantics.IsCoded (sem : Semantics D) : Prop :=
  ∀ (Sig : Cell D) (d : D.below (D.cell Sig)), ExtOrd.IsCodedLabel (D.grade Sig) (sem.E Sig d)

/-- A *domain with its associated semantics* (Knight, Def. 2.6.1) in record form: a cell
scheme over `Fin n` that **owns its rows** — coded (Lemma 2.5.13), consistent (Def. 2.5.12),
bountiful (Def. 2.5.14), the scheme complete (Def. 2.5.15).  Association is by representation
(the semantics is a field of the scheme, and a cell is carried dependently with its scheme),
not by the paper's literal coding theorem Prop. 2.6.3(2).  Only the empty scheme is constructed
in this file (`emptyType` at arity 0, `Knight.Type`); positive-arity domains (mute domains and
their one-point extension, `SemScheme.nonempty`) are in `Knight.Domain` (#41 (1/3)), amalgams
are not on the runway (#41 PR 2 is the fixed-domain coface experiment; the non-mute domain
producer is #106).  Inhabitants of `S α n` at every arity and limit stage are `StageType.nonempty`
(`Knight.Domain`). -/
structure SemScheme (n : ℕ) where
  /-- The cell scheme. -/
  scheme : CellScheme (ι := Fin n) Finset.univ
  /-- The associated semantics: the rows of the scheme. -/
  rows : Semantics scheme
  /-- The rows are coded (Lemma 2.5.13). -/
  rows_coded : rows.IsCoded
  /-- The rows are consistent (Def. 2.5.12). -/
  consistent : rows.IsConsistent
  /-- The rows are bountiful (Def. 2.5.14). -/
  bountiful : rows.IsBountiful
  /-- The scheme is complete (Def. 2.5.15). -/
  complete : scheme.IsComplete

namespace SemScheme

variable {n : ℕ}

/-- There are countably many domains with associated semantics (Knight, Prop. 2.6.3(4)):
a domain is its (countable, `CellScheme.countable_fin`) scheme together with finitely many
row values in the countable set of coded labels (`ExtOrd.codedLabels_countable`).  No stage
bound is involved. -/
instance countable : Countable (SemScheme n) := by
  have := ExtOrd.codedLabels_countable.to_subtype
  let g : SemScheme n → Σ D : CellScheme (ι := Fin n) Finset.univ,
      (Sig : Cell D) → D.below (D.cell Sig) → ExtOrd.codedLabels :=
    fun X => ⟨X.scheme, fun Sig d => ⟨X.rows.E Sig d, (X.rows_coded Sig d).mem_codedLabels⟩⟩
  have hinj : Function.Injective g := by
    rintro ⟨s₁, r₁, _, _, _, _⟩ ⟨s₂, r₂, _, _, _, _⟩ h
    obtain rfl : s₁ = s₂ := congrArg Sigma.fst h
    rw [Sigma.mk.injEq, heq_eq_eq] at h
    obtain rfl : r₁ = r₂ := Semantics.ext
      (funext fun Sig => funext fun d => congrArg Subtype.val (congrFun (congrFun h.2 Sig) d))
    rfl
  exact hinj.countable

end SemScheme

namespace CellScheme.restrictFace

variable {m n : ℕ} (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)
  (hr : Finset.univ.image f ∈ D.plan)

/-- The push-forward of a graded pair of `Fin m` along `f`: `(B', j) ↦ (f[B'], j)`. -/
def pushGraded (BJ' : Finset (Fin m) × ℕ) : Finset (Fin n) × ℕ := (BJ'.1.image f, BJ'.2)

theorem pushGraded_injective : Function.Injective (pushGraded f) := by
  rintro ⟨B, j⟩ ⟨C, k⟩ h
  simp only [pushGraded, Prod.mk.injEq] at h
  obtain ⟨hB, rfl⟩ := h
  rw [Finset.image_injective f.injective hB]

theorem gradedLe_pushGraded_iff {X Y : Finset (Fin m) × ℕ} :
    GradedLe (pushGraded f X) (pushGraded f Y) ↔ GradedLe X Y := by simp [GradedLe, pushGraded, Finset.image_subset_image_iff f.injective]

/-- The graded index of a restricted cell pushes forward to that of the underlying cell. -/
theorem pushGraded_cell (i : Cell (D.restrictFace f hr)) :
    pushGraded f ((D.restrictFace f hr).cell i) = D.cell (toCell D f hr i) :=
  Prod.ext (image_scope_restrictFace D f hr i) rfl

/-- Membership in the graded plan of the restriction: `BJ' ∈ P̂'` iff its push-forward is
in `P̂`. -/
theorem mem_gradedPlan_restrictFace {BJ' : Finset (Fin m) × ℕ} :
    BJ' ∈ Plan.gradedPlan (D.restrictFace f hr).plan ↔
      pushGraded f BJ' ∈ Plan.gradedPlan D.plan := by simp [Plan.mem_gradedPlan, Plan.MemGraded, pushGraded, mem_restrictFace_plan,
    Finset.card_image_of_injective _ f.injective]

/-- A restricted cell lies below `BJ'` iff its underlying cell lies below the push-forward
of `BJ'`. -/
theorem gradedLe_cell_pushGraded_iff {BJ' : Finset (Fin m) × ℕ}
    (i : Cell (D.restrictFace f hr)) :
    GradedLe ((D.restrictFace f hr).cell i) BJ' ↔
      GradedLe (D.cell (toCell D f hr i)) (pushGraded f BJ') := by
  rw [← pushGraded_cell, gradedLe_pushGraded_iff]

variable {BJ' : Finset (Fin m) × ℕ} {BJ : Finset (Fin n) × ℕ}

/-- The lower set below `BJ'` in the restriction maps into the lower set below the
push-forward `BJ` of `BJ'` in `D`, by the cell map `toCell` (the general form of `belowMap`;
the target index is any `BJ` propositionally equal to the push-forward, so that `belowMap`
itself is the instance `BJ = D.cell (toCell Sig)`, `pushGraded_cell`). -/
noncomputable def belowMapGraded (hBJ : pushGraded f BJ' = BJ)
    (d : (D.restrictFace f hr).below BJ') : D.below BJ :=
  ⟨toCell D f hr d.1, hBJ ▸ (gradedLe_cell_pushGraded_iff D f hr d.1).mp d.2⟩

@[simp] theorem belowMapGraded_val (hBJ : pushGraded f BJ' = BJ)
    (d : (D.restrictFace f hr).below BJ') :
    (belowMapGraded D f hr hBJ d).1 = toCell D f hr d.1 := rfl

theorem belowMapGraded_injective (hBJ : pushGraded f BJ' = BJ) :
    Function.Injective (belowMapGraded D f hr hBJ) := fun a b h => by
  have h' := congrArg Subtype.val h
  simp only [belowMapGraded_val] at h'
  exact Subtype.ext (toCell_injective D f hr h')

/-- Every cell of `D` below `(f[B'], j)` is visible, hence comes from a restricted cell below
`BJ'`. -/
theorem belowMapGraded_surjective (hBJ : pushGraded f BJ' = BJ) :
    Function.Surjective (belowMapGraded D f hr hBJ) := by
  subst hBJ
  rintro ⟨e, he⟩
  have hvis : D.scope e ⊆ Finset.univ.image f :=
    he.1.trans (Finset.image_subset_image (Finset.subset_univ _))
  obtain ⟨i, rfl⟩ := exists_toCell_eq D f hr hvis
  exact ⟨⟨i, (gradedLe_cell_pushGraded_iff D f hr i).mpr he⟩, rfl⟩

theorem belowMapGraded_bijective (hBJ : pushGraded f BJ' = BJ) :
    Function.Bijective (belowMapGraded D f hr hBJ) :=
  (by solve_by_elim [belowMapGraded_injective, belowMapGraded_surjective])

/-- The lower set below `BJ'` in the restriction is **in bijection** with the lower set
below its push-forward `(f[B'], j)` in `D` (Prop. 2.6.3(3): the restriction is isomorphic to
the original on every `D⟨B,j⟩` with `B ⊆ range f`).  The forward map is `toCell` on
underlying cells; at `BJ = D.cell (toCell Sig)` (`pushGraded_cell`) it is `belowMap`. -/
noncomputable def belowEquiv (hBJ : pushGraded f BJ' = BJ) :
    (D.restrictFace f hr).below BJ' ≃ D.below BJ :=
  Equiv.ofBijective _ (belowMapGraded_bijective D f hr hBJ)

@[simp] theorem belowEquiv_apply_val (hBJ : pushGraded f BJ' = BJ)
    (d : (D.restrictFace f hr).below BJ') :
    (belowEquiv D f hr hBJ d).1 = toCell D f hr d.1 := rfl

/-- `belowMap` is the bijection `belowEquiv` at the index of the underlying cell. -/
theorem toCell_belowEquiv_symm_val (hBJ : pushGraded f BJ' = BJ) (e : D.below BJ) :
    toCell D f hr ((belowEquiv D f hr hBJ).symm e).1 = e.1 :=
  congrArg Subtype.val ((belowEquiv D f hr hBJ).apply_symm_apply e)

theorem belowEquiv_symm_mk (hBJ : pushGraded f BJ' = BJ) (c : Cell (D.restrictFace f hr))
    (hc : GradedLe (D.cell (toCell D f hr c)) BJ) :
    (belowEquiv D f hr hBJ).symm ⟨toCell D f hr c, hc⟩ =
      ⟨c, (gradedLe_cell_pushGraded_iff D f hr c).mpr (hBJ ▸ hc)⟩ :=
  (belowEquiv D f hr hBJ).symm_apply_eq.mpr rfl

/-- The bijections commute with the inclusions of lower sets. -/
theorem belowEquiv_mono {X Y : Finset (Fin m) × ℕ} (h : GradedLe X Y)
    (d : (D.restrictFace f hr).below X) :
    belowEquiv D f hr (BJ' := Y) rfl (CellScheme.below.mono h d) =
      CellScheme.below.mono ((gradedLe_pushGraded_iff f).mpr h)
        (belowEquiv D f hr (BJ' := X) rfl d) :=
  rfl

theorem belowEquiv_symm_mono {X Y : Finset (Fin m) × ℕ} (h : GradedLe X Y)
    (e : D.below (pushGraded f X)) :
    (belowEquiv D f hr (BJ' := Y) rfl).symm
        (CellScheme.below.mono ((gradedLe_pushGraded_iff f).mpr h) e) =
      CellScheme.below.mono h ((belowEquiv D f hr (BJ' := X) rfl).symm e) := by
  apply (belowEquiv D f hr (BJ' := Y) rfl).injective
  rw [Equiv.apply_symm_apply, belowEquiv_mono, Equiv.apply_symm_apply]

end CellScheme.restrictFace

section RestrictFace

open CellScheme.restrictFace

variable {m n : ℕ} {D : CellScheme (ι := Fin n) Finset.univ} {f : Fin m ↪ Fin n}
  {hr : Finset.univ.image f ∈ D.plan} {BJ' : Finset (Fin m) × ℕ} {BJ : Finset (Fin n) × ℕ}

/-- A literal face restriction is a row-preserving bijection on each lower set. -/
theorem RespectsSemanticsBelow.restrictFace_iff {sem : Semantics D}
    (hBJ : pushGraded f BJ' = BJ) (r : (D.restrictFace f hr).below BJ' → ExtOrd) :
    RespectsSemanticsBelow (sem.restrictFace f hr) BJ' r ↔
      RespectsSemanticsBelow sem BJ (r ∘ (belowEquiv D f hr hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D f hr hBJ) (fun _ => rfl) (fun a b => by
    change _ ↔ D.scope (toCell D f hr a.1) ⊆ D.scope (toCell D f hr b.1)
    rw [← image_scope_restrictFace D f hr a.1, ← image_scope_restrictFace D f hr b.1,
      Finset.image_subset_image_iff f.injective]) (fun _ _ _ => rfl) r

/-- Transport a lawful lower section into the literal restriction. -/
theorem RespectsSemanticsBelow.restrictFace {sem : Semantics D} (hBJ : pushGraded f BJ' = BJ)
    {r : D.below BJ → ExtOrd} (h : RespectsSemanticsBelow sem BJ r) :
    RespectsSemanticsBelow (sem.restrictFace f hr) BJ' (r ∘ belowEquiv D f hr hBJ) :=
  (iff_comp_symm (belowEquiv D f hr hBJ).symm (restrictFace_iff hBJ) r).mp h

/-- Transport a lawful lower section out of the literal restriction. -/
theorem RespectsSemanticsBelow.of_restrictFace {sem : Semantics D} (hBJ : pushGraded f BJ' = BJ)
    {r : (D.restrictFace f hr).below BJ' → ExtOrd} (h : RespectsSemanticsBelow (sem.restrictFace f hr) BJ' r) :
    RespectsSemanticsBelow sem BJ (r ∘ (belowEquiv D f hr hBJ).symm) :=
  (restrictFace_iff hBJ r).mp h

/-- Restrict a lawful section to a visible face. -/
theorem RespectsSemantics.restrictFace {sem : Semantics D} {p : Cell D → ExtOrd}
    (h : RespectsSemantics sem p) (f : Fin m ↪ Fin n) (hr : Finset.univ.image f ∈ D.plan) :
    RespectsSemantics (sem.restrictFace f hr) (fun i => p (toCell D f hr i)) :=
  ((h.toBelow (pushGraded f (Finset.univ, m))).restrictFace rfl).toRespects
    (fun d => ⟨Finset.subset_univ _, ((D.restrictFace f hr).grade_le_card_scope d).trans
      (by simpa using Finset.card_le_univ ((D.restrictFace f hr).scope d))⟩)

end RestrictFace

namespace SemScheme

open CellScheme.restrictFace

variable {m n : ℕ}

/-- Horizontal restriction of a domain with its associated semantics to a visible face
(Knight, Prop. 2.6.3(3)/(5); Def. 3.1.5): the face restriction of the scheme with the rows
read at the underlying visible cells (`Semantics.restrictFace`).  Coding is read off the
underlying cells (grades are preserved); completeness lifts a graded pair through
`pushGraded` and `exists_toCell_eq`; consistency and bountifulness are statements about lower
sets and transport along the bijections `belowEquiv`
(`RespectsSemanticsBelow.restrictFace` / `.of_restrictFace`). -/
noncomputable def restrictFace (X : SemScheme n) (f : Fin m ↪ Fin n)
    (hr : Finset.univ.image f ∈ X.scheme.plan) : SemScheme m where
  scheme := X.scheme.restrictFace f hr
  rows := X.rows.restrictFace f hr
  rows_coded Sig d := X.rows_coded (toCell X.scheme f hr Sig) (belowMap X.scheme f hr Sig d)
  consistent Sig :=
    (X.consistent (toCell X.scheme f hr Sig)).restrictFace (pushGraded_cell X.scheme f hr Sig)
  bountiful CI' BJ' hCI' hBJ' h hne p' q' γ hp' hq' hγ hagree := by
    obtain ⟨q₀, hq₀, hq₀γ, hq₀p⟩ := X.bountiful (pushGraded f CI') (pushGraded f BJ')
      ((mem_gradedPlan_restrictFace X.scheme f hr).mp hCI')
      ((mem_gradedPlan_restrictFace X.scheme f hr).mp hBJ')
      ((gradedLe_pushGraded_iff f).mpr h) (fun e => hne (pushGraded_injective f e))
      (p' ∘ (belowEquiv X.scheme f hr rfl).symm) (q' ∘ (belowEquiv X.scheme f hr rfl).symm) γ
      (hp'.of_restrictFace rfl) (hq'.of_restrictFace rfl) hγ
      (fun e => by
        rw [Function.comp_apply, Function.comp_apply, belowEquiv_symm_mono]
        all_goals simp_all)
    refine ⟨q₀ ∘ belowEquiv X.scheme f hr rfl, hq₀.restrictFace rfl, fun d => ?_, fun d => ?_⟩
    · simp_all
    · rw [Function.comp_apply, belowEquiv_mono, hq₀p, Function.comp_apply,
        Equiv.symm_apply_apply]
  complete BJ' hBJ' := by
    obtain ⟨d, hd⟩ := X.complete _ ((mem_gradedPlan_restrictFace X.scheme f hr).mp hBJ')
    have hvis : X.scheme.scope d ⊆ Finset.univ.image f := by
      change (X.scheme.cell d).1 ⊆ _
      rw [hd]
      exact Finset.image_subset_image (Finset.subset_univ _)
    obtain ⟨i, rfl⟩ := exists_toCell_eq X.scheme f hr hvis
    exact ⟨i, pushGraded_injective f ((pushGraded_cell X.scheme f hr i).trans hd)⟩

end SemScheme

end VaughtConjecture.Knight
