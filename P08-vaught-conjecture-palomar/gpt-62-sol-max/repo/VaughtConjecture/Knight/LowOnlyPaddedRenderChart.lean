/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedIteration

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedRenderChart

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open LowOnlyPaddedContract LowOnlyPaddedIteration

open SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (L : BuildContext A B C R m n K)

/-- A later raw source restricts to a decoded earlier source. Compose the decoder
introduced at each step, retaining the field and ceiling readings. -/
theorem source_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) (b : L.F.Anchor (t + r + 2)) :
    ∃ a : L.F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧
      (∀ f, σ (a.val f) = b.val f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field L.I.left L.I.right)) =
        CanonicalFieldLayer.ceiling (t + r + 2) (Field L.I.left L.I.right) ∧
      ∀ d : (L.tower t ht).carrier.below (A, t + 2),
        (L.tower (t + r) hr).source b
          (L.advance t ht r hr d).1 =
            σ ((L.tower t ht).source a d.1) := by
  induction r with
  | zero => exact ⟨b, id, ⟨rfl, monotone_id, fun _ _ _ _ _ => rfl⟩,
      fun _ => rfl, rfl, fun _ => rfl⟩
  | succ r ih =>
    let P := L.tower (t + r) (by omega)
    let S := state L.F b
    have hS := state_admissible L.F b
    have hp := state_proper L.F b
    let a₁ := L.spec.normalize (by omega : 1 ≤ t + r + 2) (Nat.le_succ _) S hS hp
    let G := Padded.StepRows.grid P
    let H := Padded.StepRows.ceiling P
    let δ := PairedSlotDecoder.decode (t + r + 2) (PairedSlotEncoding.values S.profile) G H
    have hG : ∀ z ∈ G, SelfVis (t + r + 2) z :=
      fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ _)
    have hH : SelfVis (t + r + 2) H :=
      hG H (sourceGrid_endpoint le_rfl)
    have hb : ∀ f, S.profile f ≤ H := by
      intro f
      rw [show S.profile = L.F.fields _ b from state_profile L.F b]
      exact LowOnlyRecursiveCharts.anchor_bound L.F b f
    have hfields (f : Field L.I.left L.I.right) : δ (a₁.val f) = b.val f := by
      have he := L.spec.normalize_fields (by omega : 1 ≤ t + r + 2) (Nat.le_succ _) S hS hp
      change δ (L.spec.fields (t + r + 2) a₁ f) = _
      rw [show L.spec.fields (t + r + 2) a₁ = _ from he]
      exact (PairedSlotDecoder.decode_normalize hG hH hp f).trans (congrFun (state_profile L.F b) f)
    obtain ⟨a, τ, hτ, hf, hc, hd⟩ := ih (by omega) a₁
    refine ⟨a, δ ∘ τ, (PairedSlotDecoder.decode_witness hG hH).bounded.comp hτ (by omega),
      fun f => (congrArg δ (hf f)).trans (hfields f),
      (congrArg δ hc).trans (decode_reserved_ceiling hH hb), ?_⟩
    intro d
    change Padded.StepRows.source P (by omega) (by omega) b
      (Padded.StepRows.old P (by omega) (L.advance t ht r (by omega) d).1) = _
    rw [Padded.StepRows.source_old]
    exact congrArg δ (hd d)

end

end VaughtConjecture.Knight.LowOnlyPaddedRenderChart
