/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthPaddedDecode
import VaughtConjecture.Knight.GrowthGradeOneLift
import VaughtConjecture.Knight.PrivateRowFactorization
import VaughtConjecture.Knight.HighLayerBountiful

/-! # Actual charts and the literal lower domain of the padded successor

No shortness is imposed on inherited rows. The selected native source values
are short at grade two, including their readings at the retained long tips.
Adapted from `LowOnlyPaddedCharts` on the unchanged growth rows.
-/

namespace VaughtConjecture.Knight.GrowthPaddedCharts
open     Growth
open GrowthPaddedSuccessor 
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "carrier₀" => carrier I X T hA hB hC

local notation "source₀" => source I X T hA hB hC

theorem source_short a d :
    SharpWitnessComposition.Short 2 (source₀ a d) := by
  rcases source_supported a d with hz | hg | ⟨f, i, hi, he⟩
  · exact Or.inl hz
  · rcases Finset.mem_insert.mp hg with hz | hg
    · exact Or.inl hz
    · obtain ⟨b, _, he⟩ := Finset.mem_image.mp hg
      rw [← he]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
  · rw [he]
    exact PrivateRowFactorization.short_replace
      (CanonicalPairedProfiles.inventory_short a.property.1 f) le_rfl hi

local notation "input₀" => input I X T hA hB hC

local notation "rows₀" => rows I X T hA hB hC

/-- An arbitrary lawful ambient supplies an actual installed serving leaf.
The chart reads the complete physical vector, not just the original fields. -/
theorem exists_chart
    {q}
    (hq : RespectsSemanticsBelow (rows₀) (A, 2) q) :
    ∃ a , ∃ σ , ∃ M ,
      Witness (gTop 2) σ ∧
      (∀ d, (carrier₀).grade d.1 = 2 → q d ≤ M) ∧
      ∀ d, σ (source₀ a d.1) = min (q d) M := by
  let a₀ := Growth.zeroMember X 2 (by decide)
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨leaf I X T hA hB hC a₀, by rw [leaf_index]; exact GradedLe.refl _⟩,
      leaf_index a₀⟩
  obtain ⟨x, hx⟩ | ⟨a, ha⟩ := GrowthPaddedSuccessor.cell_cases H.owner.1
  · have he := H.index
    rw [hx, SourceLayerCarrier.cell_toCell] at he
    exact False.elim ((input₀).separation x
      (he.symm ▸ GradedLe.refl _))
  · refine ⟨a, H.shift, q H.owner, H.witness, H.dominates, ?_⟩
    intro d
    have hr := H.read_capped d d.2.2
    have he : (rows₀).E H.owner.1
        (H.occurrence d d.2.2) = source₀ a d.1 := by
      have hr' : ∀ e ,
          (rows₀).E H.owner.1 e =
            source₀ a e.1 := by
        rw [ha]
        exact leaf_row I X T hA hB hC a
      exact hr' _
    rwa [he] at hr

/-- Grade one contains precisely the unchanged padded predecessor. -/
def lowerEquiv : (input₀).lower.below (A, 1) ≃
    (carrier₀).below (A, 1) :=
  HighLayerBountiful.equiv (input₀).lower
    (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty))
    2 (by decide) hA (A, 1) (fun h => by have := h.2; omega)

variable {I X T hA hB hC} in
theorem lower_respects_iff p :
    RespectsSemanticsBelow (input₀).lowerRows (A, 1) p ↔
      RespectsSemanticsBelow (rows₀) (A, 1)
        (p ∘ (lowerEquiv I X T hA hB hC).symm) := by
  apply respects_iff_of_equiv (lowerEquiv I X T hA hB hC)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row I X T hA hB hC b.1 d).symm

