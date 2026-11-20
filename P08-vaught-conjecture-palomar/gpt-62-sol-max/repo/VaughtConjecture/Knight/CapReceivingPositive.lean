/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapReceivingModel

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCutReceiving

open TypeTower StageType KnightRealization Value ExtOrd CellScheme.restrictFace

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- Covering supplies a positive chart and thereby bootstraps empty-root receiving. -/
theorem of_positive (hne : Nonempty M) (hcons : R.IsExactParentConsistent)
    (hcover : R.IsInitialSegmentCovering)
    (hpos : ∀ {n : ℕ}, 0 < n → FiniteCutReceiving.At R n) :
    FiniteCutReceiving R := by
  intro n t p hp q hqp δ hδ hδα
  cases n with
  | succ n => exact hpos (Nat.succ_pos n) t p hp q hqp δ hδ hδα
  | zero =>
    obtain ⟨x⟩ := hne
    let t₁ : Fin 1 ↪ M := ⟨fun _ => x, fun a b _ => Subsingleton.elim a b⟩
    obtain ⟨m, s, -, hu⟩ := hcover t₁
    have hchart : ∃ (u : Fin (1 + m) ↪ M) (P : S α.1 (1 + m)), R.eval u = some P :=
      ⟨s, Option.isSome_iff_exists.mp hu⟩
    rw [Nat.add_comm 1 m] at hchart
    obtain ⟨u, P, hP⟩ := hchart
    obtain ⟨Q, hQP, hQq, _⟩ := exists_amalgam_point (CanonicalCoatomSupply.supply α.2)
      m (Fin.last (m + 1)) P q
    have hcof : IsCoface P Q := by
      change typeMap Fin.castSuccEmb Q = some P
      rw [castSuccEmb_eq_succAboveEmb_last]
      exact hQP
    obtain ⟨y, hy, r, hr, he, hcap⟩ := hpos (Nat.succ_pos m) u P hP Q hcof δ hδ hδα
    obtain ⟨rs, rl, rb, rr⟩ := r
    dsimp only at he
    subst rs
    let r : S α.1 (m + 2) := ⟨Q.scheme, rl, rb, rr⟩
    let f := pointEmb (Fin.last (m + 1))
    have hv : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
      (typeMap_isSome_iff f Q).mp (by rw [hQq]; rfl)
    have heq : Q.restrictFace f hv = q :=
      Option.some.inj ((typeMap_eq_some f Q hv).symm.trans hQq)
    have hy0 : y ∉ Set.range t := fun ⟨i, _⟩ => i.elim0
    have htup : f.trans (snoc u y hy) = snoc t y hy0 := by
      ext i
      obtain rfl : i = Fin.last 0 := Subsingleton.elim _ _
      change snoc u y hy (Fin.last (m + 1)) = snoc t y hy0 (Fin.last 0)
      simp only [snoc_apply_last]
    have hscheme := congrArg StageType.scheme heq
    change (r.restrictFace f hv).scheme = q.scheme at hscheme
    refine ⟨y, hy0, r.restrictFace f hv, ?_, hscheme, ?_⟩
    · rw [← htup, hcons _ r f hr]
      exact typeMap_eq_some f r hv
    · intro d
      exact (hcap (toCell Q.scheme.scheme f hv d)).trans
        (congrArg (min · δ) ((typeMap_eq_some_iff_labels f Q q hv hscheme).mp hQq d))

end VaughtConjecture.Knight.FiniteCutReceiving
