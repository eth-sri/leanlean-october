/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedRendering

/-! # The retained-padded growth row-and-rendering invariant

The base rows stay literal, including long grade-one tips and proper original
owners of arbitrary grade. Only higher full-scope rows are required short at
their own grade. This is an invariant of a constructed semantic layer, not a
lifting or bountifulness hypothesis. The contract and its constructed seed
follow the checked LOW renderer, instantiated here with growth admission.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedContract
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthHigherSources SourcePrefixRows SharpWitnessComposition PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev base := (GrowthPaddedSuccessor.input I X attach hA hB hC).lower
abbrev baseRows := (GrowthPaddedSuccessor.input I X attach hA hB hC).lowerRows

local notation "bse" => base I X attach hA hB hC
local notation "Bcell" => CellScheme.cell (base I X attach hA hB hC)

theorem base_full_grade (c : Cell bse) (hc : CellScheme.scope bse c = A) :
    CellScheme.grade bse c = 1 := by
  rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) c with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exact False.elim (proper I hB hC d
      ((congrArg Prod.fst (RelativeLadderLayer.old_index I.boundary (by omega) d)).symm.trans hc))
  · exact congrArg Prod.snd (RelativeLadderLayer.added_index I.boundary (by omega) v)

structure Layer (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  consistent : rows.IsConsistent
  baseMap : Cell bse → Cell carrier
  base_mono : StrictMono baseMap
  base_index : ∀ c, carrier.cell (baseMap c) = Bcell c
  base_row : ∀ c (d : CellScheme.below bse (Bcell c)),
    rows.E (baseMap c) ⟨baseMap d.1, by simpa only [base_index] using d.2⟩ =
      (baseRows I X attach hA hB hC).E c d
  base_respects : ∀ c (p : Cell carrier → ExtOrd),
    RespectsSemanticsBelow rows (carrier.cell (baseMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow (baseRows I X attach hA hB hC) (Bcell c) (fun d => p (baseMap d.1))
  cases : ∀ d, (∃ c, d = baseMap c) ∨
    carrier.scope d = A ∧ 2 ≤ carrier.grade d ∧ carrier.grade d ≤ k
  higher_short : ∀ c, carrier.scope c = A → 2 ≤ carrier.grade c →
    ∀ d : carrier.below (carrier.cell c), Short (carrier.grade c) (rows.E c d)
  render : ∀ {j : ℕ}, k ≤ j → ∀ S : State I.right.scheme I.left.scheme,
    Admitted X j S → (∀ d, S.profile d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  birth : ∀ {j : ℕ} (_hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (_hS : Admitted X j S) (_hp : ∀ d, S.profile d ≠ ⊤), Catalogue X 1
  birth_ranks : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) d,
    RelativeLadderLayer.ranks (fields X 1) (birth hj S hS hp) d =
      LadderScalarRendering.fieldRank S.profile d
  render_base : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) → ∀ d,
    render hj S hS hp G H (baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth hj S hS hp) S.profile H d
  lawful : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) →
      RespectsSemanticsBelow rows (A, j) (fun d => render hj S hS hp G H d.1)
  bound : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    SelfVis k H → (∀ d, S.profile d ≤ H) → ∀ d, render hj S hS hp G H d ≤ H
  supported : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G : Finset ExtOrd} {H : ExtOrd} {l : ℕ},
    k ≤ l → H ∈ G → ∀ d,
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile (render hj S hS hp G H d)
  agreement : ∀ {j} (hj : k ≤ j) (S T) (hS) (hT) (hp) (ht) {G H h},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → h ∈ G → h ≤ H →
    Agree S.profile T.profile h → Agree (render hj S hS hp G H) (render hj T hT ht G H) h
  ceiling_at : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, S.profile d ≤ H) →
    ∀ i, 1 ≤ i → i ≤ k → ∃ c, carrier.cell c = (A, i) ∧ render hj S hS hp G H c = H

namespace Layer
variable {k : ℕ} (P : Layer I X attach hA hB hC k)

theorem separated (hk : 1 ≤ k) (d : Cell P.carrier) :
    ¬ GradedLe (A, k + 1) (P.carrier.cell d) := by
  intro hd
  have hs := Finset.Subset.antisymm
    (P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan d)) hd.1
  have hk' : k + 1 ≤ P.carrier.grade d := hd.2
  rcases P.cases d with ⟨c, rfl⟩ | ⟨_, _, hg⟩
  · have hb := base_full_grade I X attach hA hB hC c
      ((congrArg Prod.fst (P.base_index c)).symm.trans hs)
    have hi : P.carrier.grade (P.baseMap c) = CellScheme.grade bse c :=
      congrArg Prod.snd (P.base_index c)
    omega
  · omega

theorem original_readback {j : ℕ} (hj : k ≤ j) (S : State I.right.scheme I.left.scheme)
    (hS : Admitted X j S) (hp : ∀ d, S.profile d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hb : ∀ d, S.profile d ≤ H)
    (d : Cell I.boundary) :
    P.render hj S hS hp G H (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d)) =
      S.profile (field I d) := by
  rw [P.render_base hj S hS hp hG hH hb]
  exact RelativeLadderLayer.renderWith_old I.boundary (by omega) (field I) (fields X 1)
    _ _ _ (P.birth_ranks hj S hS hp) d
end Layer

open GrowthPaddedSuccessor GrowthPaddedRendering in
def initial : Layer I X attach hA hB hC 2 where
  carrier := carrier I X attach hA hB hC
  rows := rows I X attach hA hB hC
  consistent := consistent I X attach hA hB hC
  baseMap := old I X attach hA hB hC
  base_mono := SourceLayerCarrier.old_order _ _ _ _ _
  base_index _ := SourceLayerCarrier.cell_toCell _ _ _ _ _ _
  base_row := inherited_row I X attach hA hB hC
  base_respects c p := by
    let J := input I X attach hA hB hC
    rw [WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
      (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation c)]
    exact SeparatedSourceLayerCarrier.base_respects_iff J.lower
      (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
      2 (by decide) hA J.separation J.lowerRows c _
  cases d := by
    rcases GrowthPaddedSuccessor.cell_cases I X attach hA hB hC d with h | ⟨a, rfl⟩
    · exact Or.inl h
    · have hl := leaf_index I X attach hA hB hC a
      exact Or.inr ⟨congrArg Prod.fst hl, (congrArg Prod.snd hl).ge, (congrArg Prod.snd hl).le⟩
  higher_short c hc hg d := by
    rcases GrowthPaddedSuccessor.cell_cases I X attach hA hB hC c with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · have hi := SourceLayerCarrier.cell_toCell bse
        (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
        2 (by decide) hA (.inl b)
      have hb := base_full_grade I X attach hA hB hC b ((congrArg Prod.fst hi).symm.trans hc)
      have he : (carrier I X attach hA hB hC).grade (old I X attach hA hB hC b) = 1 :=
        (congrArg Prod.snd hi).trans hb
      omega
    · simpa only [CellScheme.grade, leaf_index, leaf_row] using
        source_short I X attach hA hB hC a d.1
  render := render I X attach hA hB hC
  birth {j} hj S hS hp := baseAnchor X (anchor I X hj S hS hp)
  birth_ranks := birth_ranks I X
  render_base := render_old I X attach hA hB hC
  lawful := render_lawful I X attach hA hB hC
  bound := render_bound I X attach hA hB hC
  supported := render_supported I X attach hA hB hC
  agreement {j} hj S T hS hT hp ht := render_prefix I X attach hA hB hC hj S hS hp hT ht
  ceiling_at {j} hj S hS hp {G H} hG hH hb i hi hik := by
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · exact render_base_ceiling I X attach hA hB hC hj S hS hp hG hH hb
    · exact ⟨_, leaf_index I X attach hA hB hC _,
        render_ceiling I X attach hA hB hC hj S hS hp hH hb⟩
