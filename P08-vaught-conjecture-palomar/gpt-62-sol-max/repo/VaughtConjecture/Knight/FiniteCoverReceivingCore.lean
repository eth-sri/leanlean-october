/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteCutReceiving
public import VaughtConjecture.Knight.StageCappedRepair
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.ReceiveCover
public import VaughtConjecture.Knight.CapObservation

@[expose] public section

namespace VaughtConjecture.Knight.FiniteCoverReceiving

open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CellScheme.restrictFace

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

private theorem castCell_comp {m : ℕ} {X Y Z : SemScheme m} (h : X = Y) (k : Y = Z)
    (d : Cell X.scheme) : SemScheme.castCell k (SemScheme.castCell h d) = SemScheme.castCell (h.trans k) d := by
  subst Y Z
  rfl

/-- At an auxiliary cap, each one-point repair preserves the capped donor. -/
theorem receive_cover_at_cap_of_receiving (hcons : R.IsExactParentConsistent)
    (hFC : FiniteCutReceiving R) {γ : ExtOrd} (hγbot : ⊥ < γ) (hγα : γ < ofOrd α.1)
    {n m : ℕ} (Q : S α.1 m) (hγ : SelfVis m γ) (f : Fin n ↪ Fin m)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : typeMap f Q = some p) (ht : R.eval t = some p) :
    ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ R.eval u = some Q' ∧
      ∃ h : Q'.scheme = Q.scheme, ∀ d, min (Q'.label d) γ = min (Q.label (SemScheme.castCell h d)) γ := by
  refine receiveCover hcons (Inv := fun {_ m} _ _ => SelfVis m γ)
    (Rel := fun Q' Q => ∃ h : Q'.scheme = Q.scheme,
      ∀ d, min (Q'.label d) γ = min (Q.label (SemScheme.castCell h d)) γ)
    (fun _ => ⟨rfl, fun _ => rfl⟩) ?_ ?_ Q f t p hp ht hγ
  · rintro m Q₁ Q₂ Q₃ ⟨h, h₁⟩ ⟨k, h₂⟩
    exact ⟨h.trans k, fun d => (h₁ d).trans (by rw [← castCell_comp h k]; exact h₂ _)⟩
  · intro n m Q g hg t p ht hγ hcof
    obtain ⟨y, hy, q', hq', h, hagree⟩ := hFC t p ht _ hcof γ hγbot hγα
    obtain ⟨⟨Ds, labels, bounds, lawful⟩, hDs, hQ₁g, hQ₁γ⟩ :=
      exists_stage_extends_capped_emb Q.scheme g hg q' h.symm Q.respects hγ hγα
        (fun i => (hagree (SemScheme.castCell h.symm i)).symm)
    dsimp only at hDs
    subst Ds
    exact ⟨snoc t y hy, ⟨Q.scheme, labels, bounds, lawful⟩, q',
      castSuccEmb_trans_snoc t y hy, hγ, ⟨rfl, hQ₁γ⟩, hQ₁g, hq'⟩

/-- **Finite-cover receiving.**  Over an exact realized root `t ↦ p`, every finite legal donor
`Q` whose face `f` is `p` is received below any proper cutoff `δ` below the stage: an actual
tuple `u` over `t` on `Q`'s exact scheme agrees with `Q` below `δ`.  No stage block is spent. -/
theorem finiteCoverReceiving_of_receiving (hcons : R.IsExactParentConsistent)
    (hFC : FiniteCutReceiving R) {n m : ℕ} (Q : S α.1 m) (f : Fin n ↪ Fin m)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : typeMap f Q = some p) (ht : R.eval t = some p)
    (δ : ExtOrd) (hδbot : ⊥ < δ) (hδα : δ < ofOrd α.1) :
    ∃ (u : Fin m ↪ M) (Q' : S α.1 m), f.trans u = t ∧ R.eval u = some Q' ∧
      ∃ h : Q'.scheme = Q.scheme,
        ∀ d, min (Q'.label d) δ = min (Q.label (SemScheme.castCell h d)) δ := by
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    all_goals simp_all
  obtain ⟨u, Q', hfu, hu, h, hagree⟩ :=
    receive_cover_at_cap_of_receiving hcons hFC (γ := ofOrd (ν + m))
      (bot_lt_ofOrd _) (ofOrd_lt_ofOrd.mpr (add_nat_lt_limitStage hν m)) Q
      (selfVis_ofOrd_add_nat ν m) f t p hp ht
  exact ⟨u, Q', hfu, hu, h, fun d => GradeTailRestoration.cap_below (hagree d)
    (ofOrd_le_ofOrd.mpr (le_add_nat ν m))⟩

end VaughtConjecture.Knight.FiniteCoverReceiving
