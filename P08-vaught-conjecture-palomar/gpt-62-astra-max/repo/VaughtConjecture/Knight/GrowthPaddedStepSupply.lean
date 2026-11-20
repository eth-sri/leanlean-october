/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthPaddedStepDecode

/-! # Literal-top section supply on the recursive padded growth rows

Terminal insertion supplies finite bottom reflection on the complete field
vector. The exact padded-base table then transports long-row lawfulness;
higher full-scope rows use short-row composition. No positive external cap,
predecessor lift or bountifulness of the new output is assumed.
-/

/- The owner-by-owner argument adapts LowOnlyPaddedStepSupply; all scalar
admission, terminal insertion, and boundary lawfulness are growth results. -/
@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedStepSupply
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase
open GrowthPaddedContract PaddedTower.Step GrowthPaddedStepDecode
open PaddedTower.Step SharpWitnessComposition GrowthHigherSources
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {frame : I.GrowthFrame X} {k : ℕ}
  (P : Layer frame k) (hk : 1 ≤ k) (hnext : k + 1 ≤ A.card)

theorem exists_section {S}
    (hS : Admitted X (k + 1) S) :
    ∃ w, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨original P hnext d.1, by rw [original_index]; grind⟩ =
          S.profile (GrowthOrderedBase.field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    ProfileCatalogue.supported_decoder (Growth.profileFamily X (k+1)) (Nat.succ_pos k) hS
  change ∀ f, δ (Q.profile f) = S.profile f at hread
  let a : Catalogue X (k + 1) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  have horiginal : RespectsSemanticsBelow I.rows (A, k + 1)
      (fun d => δ (a.val (GrowthOrderedBase.field I d.1))) := by
    simpa [a, hread] using boundary_lawful_at I X frame.attachment hS
  refine ⟨_, decoded_lawful P hk hnext a hδ hreflect horiginal, ?_⟩
  intro d
  rw [source_original]
  grind

/-- Independent bottom-cap private supply, allowing literal top. -/
theorem private_bottom_supply
    {p}
    (hp : I.right.rows.Lawful p) :
    ∃ w, (rows P hk hnext).Lawful w ∧
      ∀ d, w (privateAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := frame.attachment.private_bottom_state hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.rightFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    exact (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans
    ((GrowthOrderedBase.field_private I X frame.attachment hS d.1).trans (hr d))

/-- Donor supply uses the pre-activation donor fibre, independently of any
positive-cap transport or symmetry assertion about growth admission. -/
theorem donor_bottom_supply (hN : k + 1 < X.req.N)
    {p}
    (hp : I.left.rows.Lawful p) :
    ∃ w, (rows P hk hnext).Lawful w ∧
      ∀ d, w (donorAt P hnext d) = p d := by
  obtain ⟨S, hS, hr⟩ := frame.attachment.donor_bottom_state hN hp
  obtain ⟨w, hw, hread⟩ := exists_section P hk hnext hS
  refine ⟨w, hw, fun d => ?_⟩
  have hd : GradedLe (I.boundary.cell (I.leftFace.map d.1)) (A, k + 1) := by
    refine ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _), ?_⟩
    exact (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2
  exact (hread ⟨_, hd⟩).trans ((GrowthOrderedBase.field_donor I S d.1).trans (hr d))

end
end VaughtConjecture.Knight.GrowthPaddedStepSupply
