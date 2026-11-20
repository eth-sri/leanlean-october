/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice
public import VaughtConjecture.Knight.CoatomBoundaryExtension

@[expose] public section

namespace VaughtConjecture.Knight.CoatomBoundaryExtension

open Transform Value ExtOrd GradeTailRestoration CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

theorem LiftResult.lower_cap {sem : Semantics D} {I J : Finset ι × ℕ}
    {h : GradedLe I J} {p : D.below I → ExtOrd} {u q : D.below J → ExtOrd}
    {M γ : ExtOrd} (hr : LiftResult sem h p u M) (hγ : γ ≤ M)
    (hq : ∀ d, min (u d) γ = min (q d) γ) : LiftResult sem h p q γ := by
  obtain ⟨r, hl, hc, hf⟩ := hr
  exact ⟨r, hl, fun d => (cap_below (hc d) hγ).trans (hq d), hf⟩

end

end VaughtConjecture.Knight.CoatomBoundaryExtension

namespace VaughtConjecture.Knight.SingleFaceTailRestoration

open Transform Value ExtOrd GradeTailRestoration CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) {C B : Finset ι} {N : ℕ} (hCB : C ⊆ B)

/-- If the prescribed top-grade values are already below the cap, they are
read from the capped ambient. Only the predecessor grade needs a lift. -/
theorem lift
    (hlift : CappedLift sem (show GradedLe (C, N - 1) (B, N - 1) from ⟨hCB, le_rfl⟩))
    {p : D.below (C, N) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, N) p)
    {q : D.below (B, N) → ExtOrd} (hq : RespectsSemanticsBelow sem (B, N) q)
    {M : ExtOrd} (hM : SelfVis N M)
    (hag : ∀ e, min (q (CellScheme.below.mono
      (show GradedLe (C, N) (B, N) from ⟨hCB, le_rfl⟩) e)) M = min (p e) M)
    (hhigh : ∀ e : D.below (C, N), D.grade e.1 = N → p e ≤ M) :
    LiftResult sem (show GradedLe (C, N) (B, N) from ⟨hCB, le_rfl⟩) p q M := by
  let v := fun d => min (q d) M
  have hv : RespectsSemanticsBelow sem (B, N) v := hq.cap hM
  let hC : GradedLe (C, N - 1) (C, N) := ⟨Finset.Subset.refl _, Nat.sub_le _ _⟩
  let hB : GradedLe (B, N - 1) (B, N) := ⟨Finset.Subset.refl _, Nat.sub_le _ _⟩
  obtain ⟨w, hw, hwcap, hwread⟩ := hlift (p ∘ CellScheme.below.mono hC) (v ∘ CellScheme.below.mono hB)
    M (hp.mono hC) (hv.mono hB) (hM.mono (Nat.sub_le _ _))
    (fun d => by
      simpa only [v, Function.comp_apply, min_assoc, min_self] using! hag (CellScheme.below.mono hC d))
  refine ⟨splice v w, splice_respects (Nat.sub_le _ _) hv hw
    (fun _ _ => min_le_right _ _) hwcap, fun d => ?_, fun d => ?_⟩
  · simpa only [v, min_assoc, min_self] using! splice_cap (Nat.sub_le N 1) hwcap d
  · by_cases hd : D.grade d.1 ≤ N - 1
    · rw [splice_low v w _ hd]
      exact hwread ⟨d.1, d.2.1, hd⟩
    · rw [splice_high v w _ hd]
      have hle : D.grade d.1 ≤ N := d.2.2
      have hn : D.grade d.1 = N := by omega
      exact (hag d).trans (min_eq_left (hhigh d hn))

end

end VaughtConjecture.Knight.SingleFaceTailRestoration
