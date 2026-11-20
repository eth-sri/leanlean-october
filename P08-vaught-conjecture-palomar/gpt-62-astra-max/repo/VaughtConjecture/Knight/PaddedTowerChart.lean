/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedTowerIteration
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # A serving native chart for every lawful section -/

@[expose] public section

namespace VaughtConjecture.Knight.PaddedTower.Step
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [Fintype X] {A : Finset ι} {D : CellScheme A}
  {Q : ℕ → Type*} [∀ j, Fintype (Q j)]
variable {F : System D X Q} {k : ℕ} (P : Layer F k) (hk : 1 ≤ k) (hnext : k+1 ≤ A.card)

theorem exists_chart
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q) :
    ∃ a : Q (k + 1), ∃ σ : ExtOrd → ExtOrd, ∃ M : ExtOrd,
      Witness (gTop (k + 1)) σ ∧
      (∀ d, (carrier P hnext).grade d.1 = k + 1 → q d ≤ M) ∧
      ∀ d, σ (source P hk hnext a d.1) = min (q d) M := by
  let a₀ := F.member (k+1) (Nat.succ_pos _)
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨⟨(controller P hnext a₀).1, (controller P hnext a₀).2.symm ▸ GradedLe.refl _⟩,
      (controller P hnext a₀).2⟩
  let c : SourcePrefixLayer.Controller (carrier P hnext) (k + 1) := ⟨H.owner.1, H.index⟩
  let a := member P hk hnext c
  have ha : controller P hnext a = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Q (k + 1))
      (k + 1) (Nat.succ_pos k) hnext
      (P.separated hk)).apply_symm_apply c
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

theorem exists_top_chart {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    (htop : ∃ d, (carrier P hnext).grade d.1 = k + 1 ∧ q d = ⊤) :
    ∃ a : Q (k + 1), ∃ σ : ExtOrd → ExtOrd,
      Witness (gTop (k + 1)) σ ∧ ∀ d, σ (source P hk hnext a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := exists_chart P hk hnext hq
  obtain ⟨d, hd, htop⟩ := htop
  have hMt : M = ⊤ := top_le_iff.mp (htop ▸ hM d hd)
  exact ⟨a, σ, hσ, fun d => (hread d).trans (by rw [hMt, min_top_right])⟩

end
end VaughtConjecture.Knight.PaddedTower.Step
