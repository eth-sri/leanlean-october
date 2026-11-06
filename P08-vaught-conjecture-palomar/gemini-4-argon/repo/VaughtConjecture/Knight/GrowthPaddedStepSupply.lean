/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepDecode
public import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Literal-top section supply on the recursive padded growth rows

Terminal insertion supplies finite bottom reflection on the complete field
vector. The exact padded-base table then transports long-row lawfulness;
higher full-scope rows use short-row composition. No positive external cap,
predecessor lift or bountifulness of the new output is assumed.
-/

/- The owner-by-owner argument adapts LowOnlyPaddedStepSupply; all scalar
admission, terminal insertion, and boundary lawfulness are growth results. -/
@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedStepSupply
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
open GrowthPaddedStepRendering SharpWitnessComposition GrowthHigherSources

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def birth (a : Catalogue X (k + 1)) : Catalogue X 1 :=
  P.birth (Nat.le_succ k) (state X a) (state_admitted X a) (state_proper X a)

theorem birth_ranks (a : Catalogue X (k + 1)) (d : Field I.right.scheme I.left.scheme) :
    RelativeLadderLayer.ranks (fields X 1) (birth P a) d =
      LadderScalarRendering.fieldRank (fields X (k + 1) a) d := by
  rw [birth, P.birth_ranks, state_profile]

theorem source_base (a : Catalogue X (k + 1)) (d : Cell (base I X T hA hB hC)) :
    source P hk hnext a (baseMap P hnext d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth P a) (fields X (k + 1) a) (ceiling P) d := by
  rw [baseMap, source_old]
  have he := P.render_base (Nat.le_succ k) (state X a) (state_admitted X a)
    (state_proper X a) (G := grid P) (H := ceiling P)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact anchor_bound X a f) d
  simpa only [selected, birth, state_profile] using he

theorem exists_section {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X (k + 1) S) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨original P hnext d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    Growth.exists_supported_decoder X (Nat.succ_pos k) hS
  let a : Catalogue X (k + 1) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have hl : RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, k + 1)
      (fun d => δ (source P hk hnext a (baseMap P hnext d.1))) := by
    simp only [source_base]
    exact RelativeLadderLayer.renderWith_decode_respects I.boundary I.rows (by omega)
      (field I) (fields X 1) (proper I hB hC) (Nat.succ_pos k) (birth P a) (fields X (k + 1) a)
      (birth_ranks P a) (anchor_bound X a) (anchor_visible_one X a)
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.succ_pos k))
      hδ hreflect (by simpa only [a, hread] using boundary_lawful_at I X T hS)
  refine ⟨fun d => δ (source P hk hnext a d.1),
    map_respects_of_short_or_local (source_lawful P hk hnext a) (fun d => d.2.2) hδ fun c => ?_,
    fun d => ?_⟩
  · rcases GrowthPaddedStepRendering.cell_cases P hk hnext c.1 with
      ⟨b, he⟩ | ⟨hscope, hgrade, _⟩
    · have hb : GradedLe ((base I X T hA hB hC).cell b) (A, k + 1) := by
        simpa only [he, base_index] using c.2
      have hr := (base_respects P hk hnext b (fun d => δ (source P hk hnext a d))).mpr (hl.mono hb)
      rcases c with ⟨c, hc⟩; dsimp only at he; subst c
      exact Or.inr (hr.locality ⟨_, GradedLe.refl _⟩)
    · exact Or.inl (higher_short P hk hnext c.1 hscope hgrade)
  · change δ (source P hk hnext a (original P hnext d.1)) = _
    rw [source_original]; exact hread _

theorem private_bottom_supply
    {p : I.right.scheme.below (Finset.univ, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d, w (privateAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, k + 1) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private I X T hS d.1).trans (hr d))

theorem donor_bottom_supply (hN : k + 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d, w (donorAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := T.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, k + 1) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I S d.1).trans (hr d))
