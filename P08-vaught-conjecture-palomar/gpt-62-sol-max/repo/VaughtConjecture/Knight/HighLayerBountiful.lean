/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.EffectiveGradeLifting

@[expose] public section

namespace VaughtConjecture.Knight.HighLayerBountiful

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan SourceLayerCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q : Type*) [Fintype Q] (l : ℕ) (hl : 0 < l) (hlA : l ≤ A.card)

abbrev old (d : Cell D) := toCell D Q l hl hlA (.inl d)

variable (K : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K) (hKl : K < l)

include hK hKl in
theorem separated (d : Cell D) : ¬ GradedLe (A, l) (D.cell d) :=
  fun h => (not_le_of_gt hKl) (h.2.trans (hK d))

end

end VaughtConjecture.Knight.HighLayerBountiful

namespace VaughtConjecture.Knight

open Transform Value ExtOrd CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- Proper-to-full lifting above an effective prescribed grade ceiling.
The lower lift is an actual already-proved clause, not a new-output completion
assumption. Every old prescribed value, including top, remains literal. -/
theorem cappedLift_of_prescribed_grade_bound {C B : Finset ι} {i n : ℕ}
    (hCB : C ⊆ B) (hin : i ≤ n)
    (hbound : ∀ d : D.below (C, n), D.grade d.1 ≤ i)
    (hlower : CappedLift sem (show GradedLe (C, i) (B, i) from ⟨hCB, le_rfl⟩)) :
    CappedLift sem (show GradedLe (C, n) (B, n) from ⟨hCB, le_rfl⟩) := by
  intro p q γ hp hq hγ hag
  let hCi : GradedLe (C, i) (C, n) := ⟨Finset.Subset.refl _, hin⟩
  let hBi : GradedLe (B, i) (B, n) := ⟨Finset.Subset.refl _, hin⟩
  let hlow : GradedLe (C, i) (B, i) := ⟨hCB, le_rfl⟩
  obtain ⟨u, hu, hucap, huread⟩ := hlower
    (p ∘ CellScheme.below.mono hCi) (q ∘ CellScheme.below.mono hBi) γ
    (hp.mono hCi) (hq.mono hBi) (hγ.mono hin) (fun d => hag (CellScheme.below.mono hCi d))
  obtain ⟨r, hr, hcap, hread⟩ := bountiful_same_scope sem hBi u q γ hu hq hγ
    (fun d => (hucap d).symm)
  refine ⟨r, hr, hcap, fun d => ?_⟩
  let e : D.below (C, i) := ⟨d.1, d.2.1, hbound d⟩
  exact (hread (CellScheme.below.mono hlow e)).trans (huread e)

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.HighLayerBountiful

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan SourceLayerCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (Q : Type*) [Fintype Q] (l : ℕ) (hl : 0 < l) (hlA : l ≤ A.card)

variable (K : ℕ) (hK : ∀ d : Cell D, D.grade d ≤ K) (hKl : K < l)

variable (sem : Semantics D) (out : Semantics (scheme D Q l hl hlA))

variable (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
  out.E (old D Q l hl hlA c)
    (SeparatedSourceLayerCarrier.ownerEquiv D Q l hl hlA (separated D l K hK hKl) c d) =
    sem.E c d)

include hrow in
/-- No condition on the new source profiles is needed for this lifting
reduction: their consistency is a separate construction theorem. -/
theorem bountiful (hpos : 0 < K) (hb : sem.IsBountiful) : out.IsBountiful := by
  have hmax (d : Cell (scheme D Q l hl hlA)) : (scheme D Q l hl hlA).grade d ≤ l := by
    rw [CellScheme.grade, cell_eq]
    cases toOcc D Q l hl hlA d with
    | inl x => exact (hK x).trans hKl.le
    | inr q => exact le_rfl
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade hmax hl
  intro C B n hC hB hn hCB
  change (C, n) ∈ Plan.gradedPlan D.plan at hC
  change (B, n) ∈ Plan.gradedPlan D.plan at hB
  by_cases hnew : GradedLe (A, l) (B, n)
  · have hBA : B = A := Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hB).1) hnew.1
    have hnl : n = l := le_antisymm hn hnew.2
    subst B; subst n
    by_cases hCA : C = A
    · subst C; exact lift_refl
    have hproper : ¬ A ⊆ C := by grind
    apply cappedLift_of_prescribed_grade_bound hCB hKl.le
    · intro d
      obtain ⟨c, hc⟩ := (inheritedEquiv D Q l hl hlA (C, l) (fun h => hproper h.1)).surjective d
      rw [← hc]
      change ((scheme D Q l hl hlA).cell _).2 ≤ K
      rw [inheritedEquiv_cell]
      exact hK c.1
    · apply SeparatedSourceLayerCarrier.lift D Q l hl hlA (separated D l K hK hKl) hrow
        (I := (C, K)) (J := (A, K)) ⟨hCB, le_rfl⟩
        (fun h => (not_le_of_gt hKl) h.2)
      apply lift_of_bountiful hb
      · exact Plan.mem_gradedPlan.mpr
          ⟨(Plan.mem_gradedPlan.mp hC).1, hpos, hKl.le.trans (Plan.mem_gradedPlan.mp hC).2.2⟩
      · exact Plan.mem_gradedPlan.mpr
          ⟨(Plan.mem_gradedPlan.mp hB).1, hpos, hKl.le.trans hlA⟩
  · exact SeparatedSourceLayerCarrier.lift D Q l hl hlA (separated D l K hK hKl) hrow
      (I := (C, n)) (J := (B, n)) ⟨hCB, le_rfl⟩ hnew
      (lift_of_bountiful hb hC hB ⟨hCB, le_rfl⟩)

end

end VaughtConjecture.Knight.HighLayerBountiful
