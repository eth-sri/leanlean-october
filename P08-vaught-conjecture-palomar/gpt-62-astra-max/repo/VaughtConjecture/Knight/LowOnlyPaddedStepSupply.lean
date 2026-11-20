/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode

/-! # Literal-top section supply on the recursive padded LOW rows

Terminal insertion supplies finite bottom reflection on the complete field
vector. The exact padded-base table then transports long-row lawfulness;
higher full-scope rows use short-row composition. No positive external cap,
predecessor lift or bountifulness of the new output is assumed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepSupply
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract PaddedTower.Step LowOnlyPaddedStepDecode
open PaddedTower.Step SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {frame : I.LowFrame F} {k : ℕ}
  (P : Layer frame k) (hk : 1 ≤ k) (hnext : k + 1 ≤ A.card)

/-- Native section supply for every admitted state, with literal-top fields.
No external positive cap or lower-layer lifting theorem is used. -/
theorem exists_section {S} (hS : F.Admissible (k + 1) S) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨original P hnext d.1, by rw [original_index]; exact d.2⟩ =
          S.profile (field I d.1) := by
  obtain ⟨Q,hQ,hcanon,δ,hδ,hread,hreflect,_⟩ := ProfileCatalogue.supported_decoder (LowOnly.Family.profileFamily F (k+1)) (Nat.succ_pos k) hS
  change ∀ f, δ (Q.profile f) = S.profile f at hread
  let a : F.Anchor (k+1) := ⟨Q.profile,hcanon,Q,hQ,rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (field I d.1))) := by
    simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F frame.attachment (k + 1) S hS
  refine ⟨_, decoded_lawful P hk hnext a hδ hreflect horiginal, ?_⟩
  intro d
  change δ (source P hk hnext a (original P hnext d.1)) = _
  rw [source_original]
  exact hread _

theorem private_bottom_supply
    {p}
    (hp : I.right.rows.Lawful p) :
    ∃ w, (rows P hk hnext).Lawful w ∧
      ∀ d, w (privateAt P hnext d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.private_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))
  exact (hread ⟨_, hd⟩).trans
    ((field_private I F frame.attachment
      (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d.1).trans
      (congrFun hr d))

theorem donor_bottom_supply
    {p}
    (hp : I.left.rows.Lawful p) :
    ∃ w, (rows P hk hnext).Lawful w ∧
      ∀ d, w (donorAt P hnext d) = p d := by
  obtain ⟨S, hS, hr, _, _⟩ := F.donor_bottom_supply hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))
  exact (hread ⟨_, hd⟩).trans ((field_read I S (I.leftFace.map d.1)).trans
    ((I.paste_left S.u S.v d.1).trans (congrFun hr d)))

end
end VaughtConjecture.Knight.LowOnlyPaddedStepSupply
