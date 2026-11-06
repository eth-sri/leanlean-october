/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.LowOnlyPaddedDecode
import VaughtConjecture.Knight.LowOnlyGradeOneSupply
import VaughtConjecture.Knight.PrivateRowFactorization
import VaughtConjecture.Knight.HighLayerBountiful

/-! # Actual charts and the literal lower domain of the padded successor

No shortness is imposed on inherited rows. The selected native source values
are short at grade two, including their readings at the retained long tips.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedCharts
open     LowOnly
open LowOnlyPaddedSuccessor 
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "carrier₀" => carrier I F hroot hA hB hC

local notation "source₀" => source I F hroot hA hB hC

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

local notation "input₀" => input I F hroot hA hB hC

local notation "rows₀" => rows I F hroot hA hB hC

/-- An arbitrary lawful ambient supplies an actual installed serving leaf.
The chart reads the complete physical vector, not just the original fields. -/
theorem exists_chart
    {q}
    (hq : RespectsSemanticsBelow (rows₀) (A, 2) q) :
    ∃ a , ∃ σ , ∃ M ,
      Witness (gTop 2) σ ∧
      (∀ d, (carrier₀).grade d.1 = 2 → q d ≤ M) ∧
      ∀ d, σ (source₀ a d.1) = min (q d) M := by
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor (by decide) (F.zero_admissible 2)
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨leaf I F hroot hA hB hC a₀, by rw [leaf_index]; exact GradedLe.refl _⟩,
      leaf_index a₀⟩
  obtain ⟨x, hx⟩ | ⟨a, ha⟩ := LowOnlyPaddedSuccessor.cell_cases H.owner.1
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
        exact leaf_row I F hroot hA hB hC a
      exact hr' _
    rwa [he] at hr

/-- Grade one contains precisely the unchanged padded predecessor. -/
def lowerEquiv : (input₀).lower.below (A, 1) ≃
    (carrier₀).below (A, 1) :=
  HighLayerBountiful.equiv (input₀).lower
    (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
    2 (by decide) hA (A, 1) (fun h => by have := h.2; omega)

variable {I F hroot hA hB hC} in
theorem lower_respects_iff p :
    RespectsSemanticsBelow (input₀).lowerRows (A, 1) p ↔
      RespectsSemanticsBelow (rows₀) (A, 1)
        (p ∘ (lowerEquiv I F hroot hA hB hC).symm) := by
  apply respects_iff_of_equiv (lowerEquiv I F hroot hA hB hC)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row I F hroot hA hB hC b.1 d).symm

