/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderTableDecode
public import VaughtConjecture.Knight.RecursiveRungRendering
public import VaughtConjecture.Knight.ReceivingCatalogueRanks
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Padded towers over a finite catalogue at each grade -/

@[expose] public section

namespace VaughtConjecture.Knight.PaddedTower
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison
open RecursiveRungRendering (grid ceiling)
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [Fintype X] {A : Finset ι} {D : CellScheme A}
  {Q : ℕ → Type*} [∀ j, Fintype (Q j)]

/-- Scalar data used by the installer. A member is admitted at its native grade;
only a restriction to the *immediately preceding* grade is ever needed. -/
structure System (D : CellScheme A) (X : Type*) [Fintype X] (Q : ℕ → Type*) where
  sem : Semantics D
  consistent : sem.IsConsistent
  positive : 0 < A.card
  proper : ∀ d, D.scope d ≠ A
  field : Cell D → X
  values : ∀ {j}, Q j → X → ExtOrd
  canonical : ∀ {j} (a : Q j), values a ∈ CanonicalPairedProfiles.inventory X j
  visible : ∀ {j}, 1 ≤ j → ∀ (a : Q j) x, SelfVis 1 (values a x)
  lawful : ∀ {j} (a : Q j), RespectsSemanticsBelow sem (A, j) (fun d => values a (field d.1))
  member : ∀ j, 1 ≤ j → Q j
  lower : ∀ {j}, 1 ≤ j → Q (j + 1) → Q j
  restricts : ∀ {j} (hj) (a : Q (j + 1)), values (lower hj a) = PairedSlotEncoding.normalize j (values a)

namespace System
variable (F : System D X Q)

abbrev base := RelativeLadderLayer.carrier D F.positive (X := X) (Q := Q 1)
abbrev baseRows := RelativeLadderLayer.rows D F.sem F.positive F.field (@F.values 1) F.proper
abbrev table {j} (b : Q 1) (a : Q j) := RelativeLadderLayer.renderWith D F.positive F.field
  (@F.values 1) b (F.values a) (ceiling X j)

theorem full_grade (c : Cell F.base) (hc : F.base.scope c = A) : F.base.grade c = 1 := by
  rcases RelativeLadderLayer.cell_cases D F.positive c with ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exact (F.proper d ((congrArg Prod.fst (RelativeLadderLayer.old_index D F.positive d)).symm.trans hc)).elim
  · exact congrArg Prod.snd (RelativeLadderLayer.added_index D F.positive v)

theorem bounded {j} (a : Q j) (x) : F.values a x ≤ ceiling X j := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ (F.canonical a) x).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

abbrev ranks (b : Q 1) := RelativeLadderLayer.ranks (@F.values 1) b

theorem lower_ranks (a : Q 2) (x) : F.ranks (F.lower le_rfl a) x = LadderScalarRendering.fieldRank (F.values a) x := by
  change LadderScalarRendering.fieldRank (F.values (F.lower _ a)) _ = _
  rw [F.restricts]
  exact ReceivingCatalogueRanks.fieldRank_normalize 1 _ (F.canonical a).2 x

theorem table_lawful {j} (hj : 1 ≤ j) (b : Q 1) (a : Q j)
    (hr : ∀ x, F.ranks b x = LadderScalarRendering.fieldRank (F.values a) x) :
    RespectsSemanticsBelow F.baseRows (A,j) (fun d => F.table b a d.1) :=
  RelativeLadderLayer.renderWith_respects D F.sem F.positive F.field _ F.proper b _ hr
    (F.bounded a) (F.visible hj a) ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono hj) (F.lawful a)
end System

variable (F : System D X Q)

/-- At height `k` keep the base rows and the incoming profiles for `k+1`.
There is no need to render arbitrary external grids, ceilings or states. -/
structure Layer (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  consistent : rows.IsConsistent
  baseMap : Cell F.base → Cell carrier
  base_mono : StrictMono baseMap
  base_index : ∀ c, carrier.cell (baseMap c) = F.base.cell c
  base_row : ∀ c (d : F.base.below
      (F.base.cell c)),
    rows.E (baseMap c) ⟨baseMap d.1, by simpa only [base_index] using d.2⟩ =
      F.baseRows.E c d
  base_respects : ∀ c (p : Cell carrier → ExtOrd),
    RespectsSemanticsBelow rows (carrier.cell (baseMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow F.baseRows
        (F.base.cell c) (fun d => p (baseMap d.1))
  cases : ∀ d, (∃ c, d = baseMap c) ∨
    carrier.scope d = A ∧ 2 ≤ carrier.grade d ∧ carrier.grade d ≤ k
  higher_short : ∀ c, carrier.scope c = A → 2 ≤ carrier.grade c →
    ∀ d : carrier.below (carrier.cell c), Short (carrier.grade c) (rows.E c d)
  selected : Q (k + 1) → Cell carrier → ExtOrd
  birth : Q (k + 1) → Q 1
  birth_ranks : ∀ a x, F.ranks (birth a) x = LadderScalarRendering.fieldRank (F.values a) x
  render_base : ∀ a d, selected a (baseMap d) = F.table (birth a) a d
  lawful : ∀ a, RespectsSemanticsBelow rows (A, k + 1) (fun d => selected a d.1)
  bound : ∀ a d, selected a d ≤ ceiling X (k + 1)
  supported : ∀ a d, OrbitPrefixSupport.Supported (k + 1) (grid X (k + 1) : Set ExtOrd)
    (F.values a) (selected a d)
  agreement : ∀ a b {h}, h ∈ grid X (k + 1) → Agree (F.values a) (F.values b) h →
    Agree (selected a) (selected b) h
  ceiling_at : ∀ a i, 1 ≤ i → i ≤ k → ∃ c, carrier.cell c = (A, i) ∧ selected a c = ceiling X (k + 1)

namespace Layer
variable {F} {k : ℕ} (P : Layer F k)
theorem full_grade (hk : 1 ≤ k) (d : Cell P.carrier) (hd : P.carrier.scope d = A) :
    P.carrier.grade d ≤ k := by
  rcases P.cases d with ⟨c, rfl⟩ | ⟨_, _, hg⟩
  · have hs : F.base.scope c = A :=
      (congrArg Prod.fst (P.base_index c)).symm.trans hd
    exact (congrArg Prod.snd (P.base_index c)).le.trans
      ((F.full_grade c hs).le.trans hk)
  · exact hg

theorem separated (hk : 1 ≤ k) (d : Cell P.carrier) :
    ¬ GradedLe (A, k + 1) (P.carrier.cell d) := by
  intro hd
  have hs := Finset.Subset.antisymm
    (P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan d)) hd.1
  have hg := P.full_grade hk d hs
  have hk' : k + 1 ≤ P.carrier.grade d := hd.2
  omega

theorem original_readback (a : Q (k + 1)) (d : Cell D) :
    P.selected a (P.baseMap (RelativeLadderLayer.old D F.positive d)) = F.values a (F.field d) := by
  rw [P.render_base]
  exact RelativeLadderLayer.renderWith_old _ _ _ _ _ _ _ (P.birth_ranks a) d
theorem occupied (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) : ∃ c, P.carrier.cell c = (A,i) := by
  obtain ⟨c, hc, _⟩ := P.ceiling_at (F.member _ (Nat.succ_pos _)) i hi hik
  exact ⟨c, hc⟩
end Layer

/-- The retained grade-one rank table is itself the initial layer. -/
def seed : Layer F 1 where
  carrier := F.base
  rows := F.baseRows
  consistent := RelativeLadderLayer.consistent _ _ _ _ _ _ F.consistent F.lawful
  baseMap := id
  base_mono := strictMono_id
  base_index _ := rfl
  base_row _ _ := rfl
  base_respects _ _ := Iff.rfl
  cases d := Or.inl ⟨d, rfl⟩
  higher_short c hc hg := by have := F.full_grade c hc; omega
  selected a := F.table (F.lower le_rfl a) a
  birth := F.lower le_rfl
  birth_ranks := F.lower_ranks
  render_base _ _ := rfl
  lawful a := F.table_lawful (by decide) _ _ (F.lower_ranks a)
  bound a := RelativeLadderLayer.renderWith_bound _ _ _ _ _ _ (F.bounded a)
  supported a d := by
    unfold System.table
    rcases RelativeLadderLayer.renderWith_supported D F.positive F.field (@F.values 1)
      (F.lower le_rfl a) (F.values a) (ceiling X 2) d with he | ⟨x, he⟩ | he
    · exact Or.inl he
    · exact he.symm ▸ PairedSlotDecoder.supported_boundary x
    · exact Or.inr (Or.inl (he.symm ▸ sourceGrid_endpoint le_rfl))
  agreement a b {h} hh hab := RelativeLadderLayer.renderWith_agreement _ _ _ _ (F.lower_ranks a)
    (F.lower_ranks b) (F.bounded a) (F.bounded b) (CanonicalFieldLayer.grid_bound _ _ hh) hab
  ceiling_at a i hi hi' := by
    obtain rfl : i = 1 := by omega
    let b := F.lower le_rfl a
    let v := SupportLadderRows.leaf (H := RelativeLadderLayer.rungs (X := X))
      (X := X) (Nat.succ_pos _) b
    refine ⟨_, RelativeLadderLayer.added_index D F.positive v, ?_⟩
    change LadderScalarRendering.level (LadderScalarRendering.values (F.values a)) _
      (RelativeLadderLayer.rankIndex D F.positive F.field (@F.values 1) b _) = _
    dsimp only [v]
    erw [RelativeLadderLayer.rankIndex_added, SupportLadderRows.index_leaf, FiniteProfileControllers.cut_refl]
    exact ite_eq_left (by have := LadderScalarRendering.values_card_le (F.values a); unfold RelativeLadderLayer.rungs; omega)

end
end VaughtConjecture.Knight.PaddedTower
