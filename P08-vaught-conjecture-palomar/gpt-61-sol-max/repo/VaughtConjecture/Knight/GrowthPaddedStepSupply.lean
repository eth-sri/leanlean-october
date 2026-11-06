/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedStepDecode
import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Literal-top section supply on the recursive padded growth rows

Terminal insertion supplies finite bottom reflection on the complete field
vector. The exact padded-base table then transports long-row lawfulness;
higher full-scope rows use short-row composition. No positive external cap,
predecessor lift or bountifulness of the new output is assumed.
-/

/- The owner-by-owner argument adapts LowOnlyPaddedStepSupply; all scalar
admission, terminal insertion, and boundary lawfulness are growth results. -/

namespace VaughtConjecture.Knight.GrowthPaddedStepSupply
open     Growth GrowthOrderedBase
open GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
open GrowthPaddedStepRendering SharpWitnessComposition GrowthHigherSources

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {T : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "Catalogue₀" => Catalogue X (k + 1)

def birth a :=
  P.birth (Nat.le_succ k) (state X a) (state_admitted X) (state_proper X a)

local notation "fields₀" => fields X (k + 1)

theorem birth_ranks a d :
    RelativeLadderLayer.ranks (fields X 1) (birth P a) d =
      LadderScalarRendering.fieldRank (fields₀ a) d := by
  rw [birth, P.birth_ranks, state_profile]

local notation "base₀" => base I X T hA hB hC

local notation "source₀" => source P hk hnext

theorem source_base a d :
    source₀ a (baseMap P hnext d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth P a) (fields₀ a) (ceiling P) d := by
  rw [ source_old]
  have he := P.render_base (Nat.le_succ k) (state X a) (state_admitted X)
    (state_proper X a) (G := grid P) (H := ceiling P)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by simp_all [state_profile, anchor_bound]) d
  simpa only [selected, birth, state_profile] using he

local notation "RespectsSemanticsBelow₀₀" => RespectsSemanticsBelow I.rows (A, k + 1)

theorem decoded_base (a : Catalogue₀) {δ}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow₀₀
      (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (baseRows T hA hB hC) (A, k + 1)
      (fun d => δ (source₀ a (baseMap P hnext d.1))) := by
  simp only [source_base]
  by_cases hz : δ (ceiling P) = ⊥
  · have he (d : Cell base₀) :
        δ (RelativeLadderLayer.renderWith I.boundary (by omega) (field I) (fields X 1)
          (birth P a) (fields₀ a) (ceiling P) d) = ⊥ := by
      rw [← source_base P hk hnext a d]
      exact le_bot_iff.mp ((hδ.mono (source_bound P hk hnext a _)).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot,
      fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level
      (LadderScalarRendering.values (fields₀ a)) (ceiling P) i)
    apply RelativeLadderLayer.image_respects I.boundary I.rows (by omega : 0 < A.card)
      (field I) (fields X 1) (proper hB hC) (birth P a) f
      (hδ.mono.comp (LadderScalarRendering.level_mono
        (LadderScalarRendering.values_bound (anchor_bound X a))))
      (by simp only [f, LadderScalarRendering.level_zero, hδ.bot])
    · intro i
      have hv := LadderScalarRendering.level_visible (C := ceiling P)
        (anchor_visible_one X a)
        ((PairedSlotComparison.sourceGrid_visible
          (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.succ_pos k)) i
      have he := hδ.clause5
        (LadderScalarRendering.level (LadderScalarRendering.values (fields₀ a))
          (ceiling P) i) 1
        (by rw [gTop_of_le (Nat.succ_pos k)]; exact le_top) 1 le_rfl
      change SelfVis 1 (δ _)
      rw [hv] at he
      exact he.symm
    · intro i hi _
      have hp := LadderScalarRendering.level_pos
        (LadderScalarRendering.bot_not_values)
        (LadderScalarRendering.values_bound (anchor_bound X a))
        (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported
          (LadderScalarRendering.values (fields₀ a)) (ceiling P) i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        intro h
        have hb := hreflect x ((congrArg δ hx).trans h)
        exact hp (hx.symm.trans hb)
      · exact fun h => hz (he ▸ h)
    · simpa only [f, birth_ranks, LadderScalarRendering.field_readback,
        GrowthHigherSources.fields] using horiginal

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)

def decoded_lawful (a : Catalogue₀) {δ}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow₀₀
      (fun d => δ (a.val (field I d.1)))) := by
  have hs := source_lawful P hk hnext a
  have hl := decoded_base P hk hnext a hδ hreflect horiginal
  apply map_respects_of_short_or_local hs (fun d => d.2.2) hδ
  intro c
  rcases GrowthPaddedStepRendering.cell_cases P hk hnext c.1 with
    ⟨b, he⟩ | ⟨hscope, hgrade, _⟩
  · right
    have hb : GradedLe ((base₀).cell b) (A, k + 1) := by
      simpa only [he, base_index] using c.2
    have hr  :=
      (base_respects P hk hnext b (fun d => δ (source₀ a d))).mpr (hl.mono hb)
    rcases c with ⟨c, hc⟩
    dsimp only at he
    subst c
    exact hr.locality ⟨_, GradedLe.refl _⟩
  · exact Or.inl (higher_short P hk hnext c.1 hscope hgrade)

/-- Independent native physical supply, including literal top. -/
theorem exists_section {S}
    (hS : Admitted X (k + 1) S) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨original P hnext d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (Nat.succ_pos k) hS
  dsimp  [ Function.comp_def] at hread
  let a : Catalogue₀ := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow₀₀
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1))) := by
    simpa only [a, hread] using boundary_lawful_at I X T hS
  refine ⟨_, decoded_lawful P hk hnext a hδ hreflect horiginal, ?_⟩
  intro d
  
  rw [source_original]
  exact hread _

/-- Independent bottom-cap private supply, allowing literal top. -/
theorem private_bottom_supply
    {p}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      ∀ d, w (privateAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.scope_subset _, ?_⟩
    exact (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private T hS d.1).trans (hr d))

/-- Donor supply uses the pre-activation donor fibre, independently of any
positive-cap transport or symmetry assertion about growth admission. -/
theorem donor_bottom_supply (hN : k + 1 < X.req.N)
    {p}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      ∀ d, w (donorAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.scope_subset _, ?_⟩
    exact (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I).trans (hr d))


