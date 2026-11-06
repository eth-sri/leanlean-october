/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
public import VaughtConjecture.Knight.LowOnlyPaddedCharts

/-! # Arbitrary-section charts on the higher installed LOW rows

Availability and actual owner locality construct a serving catalogue member
and a faithful chart on the whole current lower set. No selected-display,
synchronization or supplied chart hypothesis is used. When a current-grade
coordinate is top the chart is uncapped everywhere in that lower set.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepChart
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyPaddedStepDecode
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def leafAt (a : F.Anchor (k + 1)) : (carrier P hnext).below (A, k + 1) :=
  ⟨(controller P hnext a).1, (controller P hnext a).2.symm ▸ GradedLe.refl _⟩

section
variable {q : (carrier P hnext).below (A, k + 1) → ExtOrd}

theorem exists_chart (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q) :
    ∃ a, ∃ σ, ∃ M,
      Witness (gTop (k + 1)) σ ∧
      (∀ d, (carrier P hnext).grade d.1 = k + 1 → q d ≤ M) ∧
      ∀ d, σ (source P hk hnext a d.1) = min (q d) M := by
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor (Nat.succ_pos k) (F.zero_admissible (k + 1))
  obtain ⟨H⟩ := AmbientGradeCharts.exists_chart hq
    ⟨leafAt P hnext a₀, (controller P hnext a₀).2⟩
  let a := member P hk hnext ⟨H.owner.1, H.index⟩
  have ha : (controller P hnext a).1 = H.owner.1 := congrArg Subtype.val
    ((SeparatedSourceLayerCarrier.controllerEquiv P.carrier (F.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext
      (P.separated I F hroot hA hB hC (by omega))).apply_symm_apply ⟨H.owner.1, H.index⟩)
  refine ⟨a, H.shift, q H.owner, H.witness, H.dominates, ?_⟩
  intro d
  have hr := H.read_capped d d.2.2
  have he : ∀ e,
      (rows P hk hnext).E H.owner.1 e = source P hk hnext a e.1 := by
    rw [← ha]
    exact leaf_row P hk hnext a
  rwa [he] at hr

theorem exists_top_chart (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    (htop : ∃ d, (carrier P hnext).grade d.1 = k + 1 ∧ q d = ⊤) :
    ∃ a, ∃ σ,
      Witness (gTop (k + 1)) σ ∧ ∀ d, σ (source P hk hnext a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := exists_chart P hk hnext hq
  obtain ⟨d, hd, htop⟩ := htop
  have hMt : M = ⊤ := top_le_iff.mp (htop ▸ hM d hd)
  exact ⟨a, σ, hσ, fun d => (hread d).trans (by rw [hMt, min_top_right])⟩

end

end
end VaughtConjecture.Knight.LowOnlyPaddedStepChart
