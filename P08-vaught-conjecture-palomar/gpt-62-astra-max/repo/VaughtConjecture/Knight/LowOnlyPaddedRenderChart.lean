/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedRestriction

/-! # Native source charts through later selected LOW renderings

Later selected renderings need not restrict to independently selected earlier
renderings. They do restrict to a numerical image of one native source. The
composite map is proved bounded through that native grade; it is not asserted
to be a faithful witness on long rows. All complete fields and the reserved
ceiling are read through the same map.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedRenderChart
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedRestriction
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)

/-- The actual native source on the seed or a constructed successor. -/
def nativeSource (t : ℕ) (ht : t+2 ≤ A.card) :=
  PaddedTower.Step.source (before frame t (by omega)) (Nat.succ_pos _) ht

/-- The same chart for a later raw source, before its final decoder. -/
theorem source_chart (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ)
    (hr : t + r + 2 ≤ A.card) (b : F.Anchor (t + r + 2)) :
    ∃ a : F.Anchor (t + 2), ∃ σ : ExtOrd → ExtOrd,
      BoundedMap (t + 2) σ ∧
      (∀ f, σ (a.val f) = b.val f) ∧
      σ (CanonicalFieldLayer.ceiling (t + 2) (Field I.left I.right)) =
        CanonicalFieldLayer.ceiling (t + r + 2) (Field I.left I.right) ∧
      ∀ d : (build frame t ht).carrier.below (A, t + 2),
        nativeSource frame (t + r) hr b
          (belowEquiv frame t ht (A, t + 2) le_rfl r hr d).1 =
            σ (nativeSource frame t ht a d.1) := by
  induction r with
  | zero => exact ⟨b, id, ⟨rfl, monotone_id, fun _ _ _ _ _ => rfl⟩,
      fun _ => rfl, rfl, fun _ => rfl⟩
  | succ r ih =>
    let L := system frame
    let δ := L.decoder b
    obtain ⟨a, τ, hτ, hf, hc, hd⟩ := ih (by omega) (L.project b)
    have hδ := boundedMap_of_witness (L.decode_witness b)
    refine ⟨a, δ ∘ τ, ⟨by simp [Function.comp_apply, δ, hτ.bot, (L.decode_witness b).bot],
      hδ.mono.comp hτ.mono, fun x k i hk hi => ?_⟩, fun f =>
      (congrArg δ (hf f)).trans (L.decode_project b f), (congrArg δ hc).trans (L.decode_ceiling b), ?_⟩
    · simp only [Function.comp_apply, δ]
      rw [hτ.comm _ _ _ hk hi, hδ.comm _ _ _ (by omega) hi]
    · intro d
      change PaddedTower.Step.source (build frame (t+r) (by omega)) (by omega) hr b
        (PaddedTower.Step.old _ _ ((belowEquiv frame t ht (A,t+2) le_rfl r (by omega)) d).1) = _
      rw [PaddedTower.Step.source_old]
      exact congrArg δ (hd d)

end
end VaughtConjecture.Knight.LowOnlyPaddedRenderChart
