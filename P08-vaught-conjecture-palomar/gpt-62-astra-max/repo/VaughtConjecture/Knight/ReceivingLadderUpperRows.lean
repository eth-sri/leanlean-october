/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderSources
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Weighted rows on actual receiving upper domains

Every upper owner uses its complete constructed source, capped at its own
weight. The two mixed copies remain distinct. Orderliness, coding and every
upper-to-upper faithful incidence are proved on the actual lower domains.
Original-owner and ladder incidences remain separate from these results.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open Transform Value ExtOrd

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

@[simp] theorem upper_grade (b : Bool) (a : U) (node : Bool) :
    (D).grade (added C hC (.upper b a node)) = 2 :=
  congrArg Prod.snd (added_index C hC (.upper b a node))

end VaughtConjecture.Knight.ReceivingLadderCarrier

namespace VaughtConjecture.Knight.ReceivingLadderUpperRows

open Transform Value ExtOrd ReceivingLadderCarrier LadderScalarRendering
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request high : X) (profile : Q → X → ℕ)
  (fields : U → X → ExtOrd) (anchor : U → Q) (G : Finset ExtOrd) (H : ExtOrd)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "src" =>
  ReceivingLadderSources.source (L := L) C hC field request high profile fields anchor G H

def weight (a : U) (node : Bool) : ExtOrd := if node then fields a high else H

/-- The new owner's actual row, not a source vector supplied by a completion hypothesis. -/
def row (a : U) (node : Bool) (d : Cell D) : ExtOrd :=
  min (src a d) (weight high fields H a node)

local notation "row₀" => row (L := L) C hC field request high profile fields anchor G H

omit [Fintype X] [Fintype U] in
theorem weight_visible (hhigh : ∀ a, SelfVis 2 (fields a high)) (hH : SelfVis 2 H)
    (a : U) (node : Bool) : SelfVis 2 (weight high fields H a node) := by
  cases node
  · exact hH
  · exact hhigh a

theorem source_visible (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h)
    (hH : SelfVis 2 H) (hfields : ∀ a x, SelfVis 1 (fields a x))
    (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
    (hhigh : ∀ a, SelfVis 2 (fields a high)) (a : U) (d : Cell D) :
    SelfVis ((D).grade d) (src a d) := by
  rcases ReceivingLadderCarrier.cell_cases C hC d with ⟨c, rfl⟩ | ⟨z, rfl⟩
  · rw [ReceivingLadderSources.source_old]
    simpa only [CellScheme.grade, old_index] using hold a c
  · cases z with
    | request =>
        rw [ReceivingLadderSources.source_request]
        simpa only [CellScheme.grade, added_index, newIndex] using hfields a request
    | ladder b v =>
        rw [ReceivingLadderSources.source_ladder, ladder_grade]
        exact level_visible (hfields a) (hH.mono (by decide)) _
    | upper b c node =>
        rw [ReceivingLadderSources.source_upper, upper_grade]
        exact selfVis_min (hG _ (SourcePrefixRows.cut_mem hbot _ _))
          (weight_visible high fields H hhigh hH c node)
    | apex => simpa only [ReceivingLadderSources.source, view_added] using
        (selfVis_bot ((D).grade (added C hC .apex)))

theorem row_orderly (hbot : ⊥ ∈ G) (hG : ∀ h ∈ G, SelfVis 2 h)
    (hH : SelfVis 2 H) (hfields : ∀ a x, SelfVis 1 (fields a x))
    (hold : ∀ a c, SelfVis (C.grade c) (fields a (field c)))
    (hhigh : ∀ a, SelfVis 2 (fields a high)) (b : Bool) (a : U) (node : Bool) :
    IsOrderly (fun d : (D).below ((D).cell (added C hC (.upper b a node))) =>
      (D).grade d.1) (fun d => row₀ a node d.1) := by
  intro d
  apply (selfVis_min
    (source_visible C hC field request high profile fields anchor G H
      hbot hG hH hfields hold hhigh a d.1) ?_).symm
  apply (weight_visible high fields H hhigh hH a node).mono
  simpa only [CellScheme.grade, added_index, newIndex] using d.2.2

end
end VaughtConjecture.Knight.ReceivingLadderUpperRows
