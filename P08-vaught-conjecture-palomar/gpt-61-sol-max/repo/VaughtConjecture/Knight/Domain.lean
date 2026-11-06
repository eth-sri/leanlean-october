import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.Model

/-! # Positive-arity domains: mute schemes and their one-point extension

PR 1 of #41.  `Knight.SemScheme` defines domains with their associated semantics (Def. 2.6.1)
but constructs only the empty one (`StageType.emptySemScheme`, arity 0).  This module builds
domains on plans of **every** arity, with a one-point extension whose face equation is the one
`Knight.Model` consumes (`ExtendsDomain`, `IsCoface`).

## The construction

* **Plans.**  `Plan.extendOnePlan P` is a plan on `Fin (n+1)` in which the initial segment
  `ι_{n,n+1} = Fin.castSuccEmb` is visible and whose restriction to it is `P`
  (`Plan.isPlan_extend_one`, transported to `Fin`; the face equation on plans is
  `Plan.image_castSucc_mem_extendOnePlan_iff`).
* **Cell schemes.**  `CellScheme.extendOne C` is the scheme on that plan whose cells are the
  cells of `C` (scopes pushed along `castSucc`; indices `Fin.castAdd`) followed by **one new
  cell for every graded pair `⟨B,j⟩ ∈ P̂'` with `n ∈ B`** (indices `Fin.natAdd`).  The old cells
  are exactly the cells visible through the initial face, in order, so the face restriction is
  `C` again — `CellScheme.restrictFace_extendOne`, a propositional equality proved by
  components (`CellScheme.ext_of_components`; no `HEq` receipts) — and completeness is
  preserved (`CellScheme.IsComplete.extendOne`).
* **Rows.**  The rows of the new cells are the crux of Knight's §4.3 ("how do we extend a
  bountiful semantics for which all sets `D^{A,k}` are empty to one in which they are not?",
  Defs 4.3.3–4.3.6: standard functions and efficient stacks, Lemma 4.3.20), and for a general
  `D` no cheap choice works: bountifulness (Def. 2.5.14) at `γ = −∞` demands that *every*
  labelling respecting `E⟨C,i⟩` extend to one respecting `E⟨B,j⟩` for `⟨C,i⟩ ≺ ⟨B,j⟩`, so the
  new cells must carry enough rows to accommodate every respecting labelling of the old ones
  — Knight's stacks are the paper's known route.  In particular the naive choice "new rows `−∞`"
  is **refuted** for every non-mute `D` (a prose argument recorded here, not a compiled theorem): a cell whose row is `−∞` on its own diagonal is forced to the label `−∞` by
  locality (`RespectsSemanticsBelow.eq_bot_of_mute`), and availability (Def. 2.5.4(2)) at
  the new scope `B ∋ n` then forces every old cell below `⟨B,j⟩` to `−∞` as well, so a non-`⊥`
  respecting labelling of `D⟨C,i⟩` has no extension.
  What is built here is therefore the **mute** semantics (`Semantics.mute`: every row
  constantly `−∞`, the last clause of Knight's Lemma 4.2.2 at every arity): its only respecting
  labelling is `−∞` (`RespectsSemantics.eq_bot_of_mute`), hence it is coded, consistent and
  bountiful for free (`SemScheme.mute`), and the mute one-point extension
  `SemScheme.muteExtendOne` of a mute domain is again mute with the face equation
  `SemScheme.restrictFace_muteExtendOne`: `D.muteExtendOne.restrictFace Fin.castSuccEmb _ = D` —
  the relation `ExtendsDomain p D` of `Knight.Model` asks for.  (For a non-mute `D`,
  `muteExtendOne` discards the old semantics and is *not* an extension of `D`; hence the name.)
  Precisely what is shown: **the all-`⊥` new-row construction cannot extend a non-mute domain.**
  Knight's stacks (§4.3) are the paper's known solution for the rows of the new cells; the
  obstruction does not show that stacks are the only possible solution.
* **Existence.**  `SemScheme.muteChain n` is the chain `D₀ ⊂ D₁ ⊂ ⋯` of mute domains from the
  empty one, so `Nonempty (SemScheme n)` for every `n` (`SemScheme.nonempty`).

## Stage types

* `StageType.ofScheme` is Knight's Prop. 4.3.24 in full generality: **every** domain `D` on
  `Fin (n+1)` carries a stage type at every limit stage `α` — the row of a full-grade cell
  `Σ ∈ D^{A,|A|}` (completeness), which respects `E⟨A,|A|⟩ = E` by consistency
  (`RespectsSemanticsBelow.toRespects`), reduced to stage `α` (`RespectsSemantics.truncate`).
  Hence `Nonempty (S α n)` for every `n` at every limit stage (`StageType.nonempty`).
* `StageType.mute` is the (unique) stage type on a mute domain at any stage, and
  `StageType.exists_isCoface_of_isMute`: every stage type on a mute domain has a coface
  (Def. 3.2.1(4)), on the one-point extension of its domain; hence an extension domain in the
  sense of `ExtendsDomain` (`StageType.exists_extendsDomain_of_isMute`).  The coface for a
  stage type on a **general** domain is Knight's Prop. 4.3.23, which rests on Cor. 4.3.22 /
  Lemma 4.3.21 / Lemma 4.3.19 (the §4.3 completion; Lemma 4.3.19 is a recorded proof-gap,
  `docs/CONCORDANCE.md` §4) — not built here, and not obtainable by any choice of `−∞` rows
  on the new cells (see above). -/

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap)

/-! ### Extensionality by components -/

/-- Two cell schemes are equal when their plans, sizes and cells agree, the cells of the
first read through `Fin.cast` (so no `HEq` on the cell function). -/
theorem CellScheme.ext_of_components {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D₁ D₂ : CellScheme A} (h_plan : D₁.plan = D₂.plan) (h_card : D₁.card = D₂.card)
    (h_cell : ∀ i, D₁.cell (Fin.cast h_card.symm i) = D₂.cell i) : D₁ = D₂ := by
  obtain ⟨P₁, ip₁, c₁, cl₁, cm₁⟩ := D₁
  obtain ⟨P₂, ip₂, c₂, cl₂, cm₂⟩ := D₂
  dsimp only at h_plan h_card h_cell
  subst h_plan h_card
  simp   at h_cell
  obtain rfl := funext h_cell
  rfl

/-- The cells of propositionally equal schemes correspond along `Fin.cast`. -/
theorem CellScheme.cell_cast_of_eq {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D₁ D₂ : CellScheme A} (h : D₁ = D₂) (i : Cell D₂) :
    D₁.cell (Fin.cast (congrArg CellScheme.card h).symm i) = D₂.cell i := by
  subst h; rfl

/-- Two domains with associated semantics are equal when their plans, sizes, cells and rows
agree, the components of the first read through `Fin.cast` (the analogue of
`StageType.ext_of_components`; no `HEq`). -/
theorem SemScheme.ext_of_components {n} {D₁ D₂ : SemScheme n}
    (h_plan : D₁.scheme.plan = D₂.scheme.plan) (h_card : D₁.scheme.card = D₂.scheme.card)
    (h_cell : ∀ i, D₁.scheme.cell (Fin.cast h_card.symm i) = D₂.scheme.cell i)
    (h_row : ∀ Sig d,
      D₁.rows.E (Fin.cast h_card.symm Sig)
        ⟨Fin.cast h_card.symm d.1, by rw [h_cell d.1, h_cell Sig]; exact d.2⟩ =
      D₂.rows.E Sig d) :
    D₁ = D₂ := by
  obtain ⟨⟨P₁, ip₁, c₁, cl₁, cm₁⟩, s₁, _, _, _, _⟩ := D₁
  obtain ⟨⟨P₂, ip₂, c₂, cl₂, cm₂⟩, s₂, _, _, _, _⟩ := D₂
  dsimp only at h_plan h_card h_cell h_row
  subst h_plan h_card
  simp only [Fin.cast_eq_self] at h_cell h_row
  obtain rfl := funext h_cell
  obtain rfl : s₁ = s₂ := Semantics.ext (funext fun Sig => funext fun d => h_row Sig d)
  rfl

/-! ### One-point extension of a plan on `Fin n` -/

end VaughtConjecture.Knight

namespace VaughtConjecture.AmalgamationPlan.Plan

variable {n : ℕ}

/-- One-point extension of a plan on `Fin n` to `Fin (n+1)` (Knight, Def. 2.1.1 step at the
new point; `Plan.isPlan_extend_one` transported to `Fin`): a plan on `Fin (n+1)` in which the
initial segment `ι_{n,n+1}[Fin n]` is visible and the visible faces inside it are exactly the
pushed-forward faces of `P`. -/
theorem exists_extendOne_fin {P} (hP : IsPlan Finset.univ P) :
    ∃ Q , IsPlan Finset.univ Q ∧
      Finset.univ.image Fin.castSuccEmb ∈ Q ∧
      ∀ C : VaughtConjecture.Knight.FiniteScope n, C.image Fin.castSuccEmb ∈ Q ↔ C ∈ P := by
  set A : Finset (Fin (n + 1)) := Finset.univ.image Fin.castSuccEmb with hA
  have hx : Fin.last n ∉ A := by
    simp_all
  have hP₀ : IsPlan A (P.image (Finset.image Fin.castSuccEmb)) := isPlan_image _ hP
  obtain ⟨Q, hQ, hAQ, hres⟩ := isPlan_extend_one hx hP₀
  have huniv : A ∪ {Fin.last n} = Finset.univ := by
    simp_all
  refine ⟨Q, huniv ▸ hQ, hAQ, fun C => ?_⟩
  have hsub : C.image Fin.castSuccEmb ⊆ A :=
    Finset.image_subset_image (Finset.subset_univ _)
  constructor
  · intro hC
    have hmem : C.image Fin.castSuccEmb ∈ restrictPlan Q A :=
      Finset.mem_inter.mpr ⟨hC, Finset.mem_powerset.mpr hsub⟩
    rw [hres, Finset.mem_image] at hmem
    obtain ⟨B, hB, hBC⟩ := hmem
    rwa [← Finset.image_injective Fin.castSuccEmb.injective hBC]
  · intro hC
    have hmem : C.image Fin.castSuccEmb ∈ restrictPlan Q A := by
      aesop
    exact (Finset.mem_inter.mp hmem).1

/-- A chosen one-point extension of a plan on `Fin n` to `Fin (n+1)`. -/
noncomputable def extendOnePlan (P : VaughtConjecture.AmalgamationPlan.SupportFamily (Fin n)) (hP : IsPlan Finset.univ P) :=
  (exists_extendOne_fin hP).choose

variable (P : VaughtConjecture.AmalgamationPlan.SupportFamily (Fin n)) (hP : IsPlan Finset.univ P)

theorem extendOnePlan_isPlan : IsPlan Finset.univ (extendOnePlan P hP) :=
  (exists_extendOne_fin hP).choose_spec.1

/-- The face equation on plans: a face of `Fin n` is visible in `P` iff its push-forward is
visible in the extension. -/
theorem image_castSucc_mem_extendOnePlan_iff (C : VaughtConjecture.Knight.FiniteScope n) :
    C.image Fin.castSuccEmb ∈ extendOnePlan P hP ↔ C ∈ P :=
  (exists_extendOne_fin hP).choose_spec.2.2 C

end VaughtConjecture.AmalgamationPlan.Plan

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan
open Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap)

/-! ### One-point extension of a cell scheme -/

namespace CellScheme

open CellScheme.restrictFace (pushGraded)

variable {n : ℕ} (C : CellScheme (ι := Fin n) Finset.univ)

/-- The **new graded pairs** of the one-point extension: the pairs `⟨B,j⟩ ∈ P̂'` of the
extended plan whose scope contains the new point `n`. -/
noncomputable def newPairs :=
  (Plan.gradedPlan (Plan.extendOnePlan C.plan C.isPlan)).filter (fun BJ => Fin.last n ∈ BJ.1)

/-- The **one-point extension** of a cell scheme on `Fin n` to `Fin (n+1)`: the extended plan
`Plan.extendOnePlan`, the old cells with their scopes pushed along `castSucc` (indices
`Fin.castAdd`), and one new cell for every new graded pair (indices `Fin.natAdd`). -/
noncomputable def extendOne : CellScheme (ι := Fin (n + 1)) Finset.univ where
  plan := Plan.extendOnePlan C.plan C.isPlan
  isPlan := Plan.extendOnePlan_isPlan _ _
  card := C.card + C.newPairs.card
  cell := Fin.append (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => (C.newPairs.equivFin.symm j).1)
  cell_mem i := by
    induction i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      have h := Plan.mem_gradedPlan.mp (C.cell_mem i)
      refine Plan.mem_gradedPlan.mpr ⟨?_, h.2.1, ?_⟩
      · exact (Plan.image_castSucc_mem_extendOnePlan_iff C.plan C.isPlan _).mpr h.1
      · show (C.cell i).2 ≤ ((C.cell i).1.image Fin.castSuccEmb).card
        rw [Finset.card_image_of_injective _ Fin.castSuccEmb.injective]
        exact h.2.2
    | right j =>
      rw [Fin.append_right]
      exact (Finset.mem_filter.mp (C.newPairs.equivFin.symm j).2).1

@[simp] theorem extendOne_cell_castAdd i :
    C.extendOne.cell (Fin.castAdd C.newPairs.card i) = pushGraded Fin.castSuccEmb (C.cell i) :=
  Fin.append_left (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => (C.newPairs.equivFin.symm j).1) i

@[simp] theorem extendOne_cell_natAdd j :
    C.extendOne.cell (Fin.natAdd C.card j) = (C.newPairs.equivFin.symm j).1 :=
  Fin.append_right (fun i => pushGraded Fin.castSuccEmb (C.cell i))
    (fun j => (C.newPairs.equivFin.symm j).1) j

/-- The one-point extension of a complete scheme is complete (Def. 2.5.15): a graded pair
seeing the new point has its new cell; one inside the initial segment is the push-forward of a
graded pair of `P̂`, which has a cell in `C`. -/
theorem IsComplete.extendOne (hC : C.IsComplete) : C.extendOne.IsComplete := by
  intro BJ hBJ
  by_cases hlast : Fin.last n ∈ BJ.1
  · refine ⟨Fin.natAdd C.card (C.newPairs.equivFin ⟨BJ, Finset.mem_filter.mpr ⟨hBJ, hlast⟩⟩), ?_⟩
    rw [extendOne_cell_natAdd, Equiv.symm_apply_apply]
  · -- the scope lies in the initial segment: pull it back
    set C₀ : VaughtConjecture.Knight.FiniteScope n := Finset.univ.filter (fun x => Fin.castSucc x ∈ BJ.1) with hC₀
    have himg : C₀.image Fin.castSuccEmb = BJ.1 := by
      ext y
      simp only [Finset.mem_image, hC₀, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      refine ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ hx, fun hy => ?_⟩
      rcases Fin.eq_castSucc_or_eq_last y with ⟨x, rfl⟩ | rfl
      · exact ⟨x, hy, rfl⟩
      · exact absurd hy hlast
    have h := Plan.mem_gradedPlan.mp hBJ
    have hmem : (C₀, BJ.2) ∈ Plan.gradedPlan C.plan := by
      refine Plan.mem_gradedPlan.mpr ⟨?_, h.2.1, ?_⟩
      · exact (Plan.image_castSucc_mem_extendOnePlan_iff C.plan C.isPlan C₀).mp
          (by rw [himg]; exact h.1)
      · show BJ.2 ≤ C₀.card
        rw [← Finset.card_image_of_injective C₀ Fin.castSuccEmb.injective, himg]
        exact h.2.2
    obtain ⟨d, hd⟩ := hC _ hmem
    refine ⟨Fin.castAdd C.newPairs.card d, ?_⟩
    rw [extendOne_cell_castAdd, hd]
    exact Prod.ext himg rfl

end CellScheme

/-! ### The mute semantics -/

section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The **mute semantics** on a cell scheme: every row is constantly `−∞` (Knight, Lemma 4.2.2,
last clause — "assigning the value `−∞` to `E(Σ)(Σ)`" — at every cell).  Orderliness is
`−∞ = −∞ ⊔⁺_k k`. -/
def Semantics.mute (D : CellScheme A) : Semantics D where
  E _ _ := ⊥
  orderly _ _ := (extVisibilityReplace_bot _ _).symm

/-- The constantly-`−∞` labelling of a lower set respects the mute semantics there. -/
theorem RespectsSemanticsBelow.mute BJ :
    RespectsSemanticsBelow (Semantics.mute D) BJ (fun _ => ⊥) :=
  RespectsSemanticsBelow.bot _ _

/-- A cell whose row is `−∞` on its own diagonal is forced to the label `−∞`: locality at the
cell itself reads `min (r Σ) (r Σ) = min (σ ⊥) (g _) = ⊥`.  So the only labelling of a lower set
respecting the mute semantics is `−∞`. -/
def RespectsSemanticsBelow.eq_bot_of_mute {BJ} {r}
    (h : RespectsSemanticsBelow (Semantics.mute D) BJ r) d :=
  h.eq_bot_of_diagonal d rfl

end

/-! ### Mute domains and their one-point extension -/

namespace SemScheme

variable {n : ℕ}

/-- The **mute domain** on a complete cell scheme: the scheme with the mute semantics.  Coding:
`−∞` is coded at every grade; consistency: every row is the `−∞` labelling, which respects the
mute semantics of its lower set; bountifulness (Def. 2.5.14): the only respecting labellings
are `−∞`, so `q' = −∞` always works. -/
noncomputable def mute (C : CellScheme (ι := Fin n) Finset.univ) (hC : C.IsComplete) :
    SemScheme n where
  scheme := C
  rows := Semantics.mute C
  rows_coded _ _ := Or.inl rfl
  consistent _ := RespectsSemanticsBelow.mute _
  bountiful _ _ _ _ _ _ p q _ hp hq _ _ :=
    ⟨fun _ => ⊥, RespectsSemanticsBelow.mute _, fun d => by rw [hq.eq_bot_of_mute d],
      fun d => (hp.eq_bot_of_mute d).symm⟩
  complete := hC

/-- **One-point extension**: the mute domain on the one-point extension of the cell scheme of
`D` (`CellScheme.extendOne`).  It is a domain on `n+1` whose face restriction along the initial
segment is the mute domain on `D`'s scheme — so it extends `D` itself (`ExtendsDomain`) exactly
when `D` is mute (`restrictFace_muteExtendOne`); for a non-mute `D` it discards the old semantics
and is not an extension.  For a general `D` the rows of the new cells must accommodate every
respecting labelling of the old ones; all-`⊥` new rows are refuted (module docstring), and Knight's
§4.3 completion (stacks) is the paper's known — not necessarily the only — solution. -/
noncomputable def muteExtendOne (D : SemScheme n) :=
  mute D.scheme.extendOne (D.complete.extendOne)

variable (D : SemScheme n)

/-- The chain of mute domains `D₀ ⊂ D₁ ⊂ ⋯`: the empty domain, extended one point at a
time. -/
noncomputable def muteChain : (n : ℕ) → SemScheme n
  | 0 => StageType.emptySemScheme
  | n + 1 => (muteChain n).muteExtendOne

end SemScheme

/-! ### Stage types on every domain, and cofaces over mute domains -/

namespace StageType

variable {α : Ordinal₀} {n : ℕ}

/-- Every cell of a scheme on `Fin (n+1)` lies below the full-grade pair `(univ, n+1)`. -/
theorem gradedLe_univ_succ (C : CellScheme (ι := Fin (n + 1)) Finset.univ) d :
    GradedLe (C.cell d) (Finset.univ, n + 1) :=
  ⟨Finset.subset_univ _, (C.grade_le_card_scope d).trans
    (by simpa using Finset.card_le_univ (C.scope d))⟩

/-- The full-grade pair `(univ, n+1)` lies in the graded plan of every scheme on `Fin (n+1)`. -/
theorem univ_succ_mem_gradedPlan (C : CellScheme (ι := Fin (n + 1)) Finset.univ) :
    (Finset.univ, n + 1) ∈ Plan.gradedPlan C.plan :=
  Plan.mem_gradedPlan.mpr ⟨C.isPlan.domain_mem, Nat.succ_pos _, by simp⟩

/-- **Every domain carries a stage type** (Knight, Prop. 4.3.24): for a domain `D` on
`Fin (n+1)` and a limit stage `α`, the row `E(Σ)` of a full-grade cell `Σ ∈ D^{A,|A|}` (which
exists by completeness) is a labelling of `D⟨A,|A|⟩ = D` respecting `E` (consistency,
Def. 2.5.12, read through `RespectsSemanticsBelow.toRespects`); its reduction to stage `α`
(`truncExt α`, Def. 3.1.2) respects `E` at stage `α` (`RespectsSemantics.truncate`). -/
noncomputable def ofScheme (hα : Order.IsSuccLimit α) (D : SemScheme (n + 1)) : S α (n + 1) :=
  let Sig := (D.complete _ (univ_succ_mem_gradedPlan D.scheme)).choose
  have hSig : D.scheme.cell Sig = (Finset.univ, n + 1) :=
    (D.complete _ (univ_succ_mem_gradedPlan D.scheme)).choose_spec
  have hall : ∀ d , GradedLe (D.scheme.cell d) (D.scheme.cell Sig) :=
    fun d => hSig ▸ gradedLe_univ_succ D.scheme d
  { scheme := D
    label := fun d => truncExt α (D.rows.E Sig ⟨d, hall d⟩)
    label_bound := fun _ => truncExt_bound
    respects := ((D.consistent Sig).toRespects hall).truncate hα }

/-- The stage types of every arity are nonempty at every limit stage: `emptyType` at arity 0,
`ofScheme` on the mute domain `SemScheme.muteChain` beyond. -/
theorem nonempty (hα : Order.IsSuccLimit α) n : Nonempty (S α n) := by
  cases n with
  | zero => exact ⟨emptyType⟩
  | succ n => exact ⟨ofScheme hα (SemScheme.muteChain (n + 1))⟩


