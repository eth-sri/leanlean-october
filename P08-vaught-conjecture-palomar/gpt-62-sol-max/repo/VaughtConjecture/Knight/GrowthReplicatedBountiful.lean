/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedExtension
public import VaughtConjecture.Knight.GrowthMixedGradeOne
public import VaughtConjecture.Knight.GrowthPaddedFibre
public import VaughtConjecture.Knight.EffectiveGradeLifting

@[expose] public section

namespace VaughtConjecture.Knight.GrowthReplicatedBountiful

open AmalgamationPlan Transform Value ExtOrd Growth CoatomBoundaryExtension

open GrowthHigherMixed

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "Rows" => rows G

/-- Extend the actual mixed-target ambient, use the constructed original-face
lift at full scope, and restrict back. This includes source grade changes. -/
theorem original_to_mixed (hsmall : n + 1 < G.X.req.N)
    {S V : Finset ι} {i j : ℕ} (hS : (S, i) ∈ Plan.gradedPlan R)
    (hV : V ∈ R) (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
    (hv : j ≤ V.card) (hjt : j ≤ G.depth + 2)
    (h : GradedLe (S, i) (V, j)) (hs : S ⊆ B ∨ S ⊆ C) :
    CappedLift Rows h := by
  have hVA : V ⊆ A := G.I.isPlan.subset_of_mem hV
  have hj0 : 1 ≤ j := (Plan.mem_gradedPlan.mp hS).2.1.trans_le h.2
  have hfull : CappedLift Rows
      (show GradedLe (S, i) (A, j) from ⟨h.1.trans hVA, h.2⟩) :=
    GrowthReplicatedRows.lift_to_full G.tower _ hs (GrowthPaddedFibre.subface G hsmall hS hs h.2 hjt)
  intro p q γ hp hq hγ hag
  let hvA : GradedLe (V, j) (A, j) := ⟨hVA, le_rfl⟩
  let W : Cut G := ⟨V, j, hV, hmV, hv, hj0, hjt⟩
  obtain ⟨q', hq', hqeq⟩ := lawfulExtension W A hVA q hq
  obtain ⟨r, hr, hcap, hread⟩ := hfull p q' γ hp hq' hγ (fun d =>
    (congrArg (fun z => min z γ) (hqeq (CellScheme.below.mono h d))).trans (hag d))
  refine ⟨fun d => r (CellScheme.below.mono hvA d), hr.mono hvA, ?_, fun d => hread d⟩
  aesop

/-- Every same-grade pair at an installed cutoff on one fixed carrier.
The strict arity hypothesis is used only for the donor-original direction. -/
theorem same_grade (hsmall : n + 1 < G.X.req.N) (S V : Finset ι) (j : ℕ)
    (hS : (S, j) ∈ Plan.gradedPlan R) (hV : (V, j) ∈ Plan.gradedPlan R)
    (hjt : j ≤ G.depth + 2) (hSV : S ⊆ V) :
    CappedLift Rows (show GradedLe (S, j) (V, j) from ⟨hSV, le_rfl⟩) := by
  by_cases htarget : V ⊆ B ∨ V ⊆ C
  · exact GrowthReplicatedRows.inherited_lift G hS hV _ htarget
  have hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V := Or.inr
    ⟨by lia, by lia⟩
  by_cases hs : S ⊆ B ∨ S ⊆ C
  · exact original_to_mixed G hsmall hS
      (Plan.mem_gradedPlan.mp hV).1 hmV (Plan.mem_gradedPlan.mp hV).2.2 hjt ⟨hSV, le_rfl⟩ hs
  · obtain ⟨hm, hp, hc⟩ := Plan.mem_gradedPlan.mp hS
    exact cappedLift (G := G) ⟨S, j, hm, Or.inr ⟨by lia, by lia⟩, hc, hp, hjt⟩
      V (Plan.mem_gradedPlan.mp hV).1 hmV hSV


variable (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData) (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Full" => GrowthPaddedIteration.BuildContext.full I X T hA hB hC

/-- The unchanged replicated growth rows are bountiful at full height.
Literal top, bottom caps, arbitrary lawful local ambients and all individual
auxiliary caps are included in the repository's `IsBountiful` conclusion. -/
theorem bountiful (hsmall : n + 1 < X.req.N) :
    (rows Full).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_same_grade
  intro S V j hS hV hSV
  have hp : (carrier Full).plan = R :=
    GrowthPaddedIteration.build_plan I X T hA hB hC (A.card - 2) (by omega)
  have hS' : (S, j) ∈ Plan.gradedPlan R := by rwa [hp] at hS
  have hV' : (V, j) ∈ Plan.gradedPlan R := by rwa [hp] at hV
  have hj := (Plan.mem_gradedPlan.mp hV').2.2
  have hc := Finset.card_le_card (I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1)
  exact same_grade Full hsmall S V j hS' hV'
    (by simpa only [GrowthPaddedIteration.BuildContext.full, Nat.sub_add_cancel hA] using hj.trans hc) hSV

end

end VaughtConjecture.Knight.GrowthReplicatedBountiful
