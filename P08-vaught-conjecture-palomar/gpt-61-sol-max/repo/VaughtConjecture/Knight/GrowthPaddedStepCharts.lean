/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthPaddedStepDecode
import VaughtConjecture.Knight.GrowthPaddedCharts

/-! # Actual serving charts on higher padded rows

Locality and availability select an installed native leaf from an arbitrary
lawful target-local ambient. Its chart reads every physical coordinate.
-/

/- Adapted from the corresponding LOW physical endgame; scalar admission
and source sections here are exclusively the growth producers. -/

namespace VaughtConjecture.Knight.GrowthPaddedStepCharts
open     Growth 
open GrowthPaddedContract GrowthPaddedStepRows 
open GrowthPaddedDecode (grid_fixed_below)

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {T : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- Locality and availability choose an actual installed native leaf. -/
theorem exists_chart
    {q}
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q) :
    ∃ a , ∃ σ , ∃ M ,
      Witness (gTop (k + 1)) σ ∧
      (∀ d, (carrier P hnext).grade d.1 = k + 1 → q d ≤ M) ∧
      ∀ d, σ (source P hk hnext a d.1) = min (q d) M := by
  let a₀ := Growth.zeroMember X (k + 1) (by omega)
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨(controller P hnext a₀).1, (controller P hnext a₀).2.symm ▸ GradedLe.refl _⟩,
      (controller P hnext a₀).2⟩
  let c : SourcePrefixLayer.Controller (carrier P hnext) (k + 1) := ⟨H.owner.1, H.index⟩
  let a := member P hk hnext c
  have ha : controller P hnext a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Catalogue X (k + 1))
      (k + 1) (Nat.succ_pos k) hnext
      (P.separated I X T hA hB hC (by omega))).apply_symm_apply c
  refine ⟨a, H.shift, q H.owner, H.witness, H.dominates, ?_⟩
  intro d
  have hr := H.read_capped d d.2.2
  have he : (rows P hk hnext).E H.owner.1 (H.occurrence d d.2.2) =
      source P hk hnext a d.1 := by
    change (data P hk hnext).rows.E c.1 _ = (data P hk hnext).profile _ _
    rw [ScopedSourcePrefixLayer.Data.row_new _ c]
    rw [ha]
    rfl
  rwa [he] at hr


