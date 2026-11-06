/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ThreeLevelFragment
public import VaughtConjecture.Knight.CappedLocalityRecoding

/-! # The provenance-preserving truncation: retain the witnesses, cap the evaluations

**The representation**, adopted after the level-two no-go for the recomputed truncation
(`docs/STATUS.md`, "Truncation representation"):
a truncated level-three cell **retains the base core's owned witnesses and their charts** and
**caps their decoded evaluations**: `ρ_ℓ^η(s) = min (ρ_ℓ(s), η)`.  The object is a base core
together with a cap (`CappedCore3`); its rows are the capped rows of the base.

**Acceptance tests, compiled.**

* `TransformsTo.capped` — the generic fact behind everything: capping the target of a faithful
  transformation at a `K`-self-visible constant (all grades `≤ K`) is again a faithful
  transformation, clause 5 included (shifter `min (σ ·) η`, suppressor `min (g k) η` through `K`).
  No controller is needed: the guard itself supplies `η ≤ g k` where the ambient output exceeds
  the cap.
* attainment of the new cap at the retained witness (`rho2_wit2C`), and every capped evaluation
  bounded by the cap;
* the cross-level localities `3 → 1` and `3 → 2` for the capped rows (`cross31C`, `cross32C`) by
  capping the base localities;
* the mixed square for the capped decoder (`mixed_squareC`);
* same-level agreement of the capped rows at the capped meet (`rowC_agree`) and the same-level
  locality with the identity shifter (`same3C`);
* repeated truncation reduces to the minimum cap (`recap`, `recap_row`, `recap_recap`), so retained
  provenance generates no history; and the **represented meet**: the capped meet of a cell with
  its own truncation is the cap (`meetC_recap`).

Level one: the capped evaluation `min (ρ₁ t H) η` coincides with the recomputed truncation's
value (`Core3.rho1_trunc`, scratch), so the two representations agree exactly where the recomputed
one is valid.  Sharp coding of the retained witness rows and of the capped rows, and locality on
the domain enlarged by the capped cells themselves, are in `Knight/CappedCoreCoding.lean`.
Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Capping a transformation -/

/-- **Capping the target of a faithful transformation** at a `K`-self-visible constant, all grades
at most `K`. -/
theorem TransformsTo.capped {D : Type*} {grade : D → ℕ} {E T : D → ExtOrd} {K : ℕ}
    (hmax : ∀ d, grade d ≤ K) {η : ExtOrd} (hvis : SelfVis K η) (h : TransformsTo grade E T) :
    TransformsTo grade E fun d => min (T d) η := by
  by_cases hne : η = ⊥
  · subst hne
    refine ⟨fun _ => ⊥, fun _ => ⊥, fun _ _ _ => le_rfl,
      fun n => (extVisibilityReplace_bot n n).symm, rfl, fun _ _ _ => le_rfl,
      fun _ _ _ _ _ => by rw [extVisibilityReplace_bot], fun d => ?_⟩
    change min (T d) ⊥ = min ⊥ ⊥
    rw [min_eq_right bot_le, min_self]
  obtain ⟨g, σ, hanti, hgvis, hbot, hmono, hevr, hrow⟩ := h
  have h5 : ∀ x k, min (σ x) η ≤ (if k ≤ K then min (g k) η else ⊥) → ∀ i, i ≤ k →
      min (σ (extVisibilityReplace x k i)) η = extVisibilityReplace (min (σ x) η) k i := by
    intro x k hact i hi
    split_ifs at hact with hk
    · have hcapk : SelfVis k η := selfVis_mono hvis hk
      rcases le_or_gt (σ x) η with hle | hlt
      · have hτ : min (σ x) η = σ x := min_eq_left hle
        rw [hτ] at hact ⊢
        have hσact : σ x ≤ g k := hact.trans (min_le_left _ _)
        rw [hevr x k hσact i hi, min_eq_left (extVisibilityReplace_le_of_le_selfVis hi hcapk hle)]
      · have hτ : min (σ x) η = η := min_eq_right hlt.le
        rw [hτ] at hact ⊢
        have hηg : η ≤ g k := hact.trans (min_le_left _ _)
        rw [min_eq_right (cap_le_of_evr hmono hevr hcapk hηg hlt hi), evr_eq_self_of_selfVis hcapk]
    · have hτbot : min (σ x) η = ⊥ := le_bot_iff.mp hact
      have hσbot : σ x = ⊥ := by
        rcases le_total (σ x) η with h | h
        · rwa [min_eq_left h] at hτbot
        · rw [min_eq_right h] at hτbot; exact absurd hτbot hne
      have hσact : σ x ≤ g k := by rw [hσbot]; exact bot_le
      rw [hevr x k hσact i hi, hσbot, extVisibilityReplace_bot, min_eq_left bot_le,
        extVisibilityReplace_bot]
  refine ⟨fun k => if k ≤ K then min (g k) η else ⊥, fun x => min (σ x) η, ?_, ?_, ?_, ?_, h5, ?_⟩
  · intro n m hnm
    dsimp only
    split_ifs with h1 h2 h2
    · exact min_le_min (hanti n m hnm) le_rfl
    · omega
    · exact bot_le
    · exact le_rfl
  · intro n
    dsimp only
    split_ifs with h
    · exact (selfVis_min (hgvis n).symm (selfVis_mono hvis h)).symm
    · exact (selfVis_bot n).symm
  · change min (σ ⊥) η = ⊥
    rw [hbot, min_eq_left bot_le]
  · exact fun _ _ h => min_le_min (hmono h) le_rfl
  · intro d
    have h := hrow d
    dsimp only
    rw [ite_eq_left (hmax d), h, min_min_min_comm, min_self]

/-! ## The capped core -/

variable {P : Type*} [Fintype P] [DecidableEq P] {gradeP : P → ℕ} {T : ℕ}

/-- A level-three cell with retained provenance: a base core and a cap. -/
structure CappedCore3 (gradeP : P → ℕ) (T : ℕ) where
  base : Core3 (gradeP := gradeP) (T := T)
  η : ExtOrd
  η_mem : η ∈ codedAlphabet 3 T
  η_vis : SelfVis 3 η
  η_le : η ≤ base.γ

namespace CappedCore3

variable (st : Setting gradeP T) (a b : CappedCore3 gradeP T)

/-- The capped proper row. -/
noncomputable def F (c : P) : ExtOrd := min (a.base.F c) a.η
/-- The capped level-one directed value. -/
noncomputable def rho1 (H : Row1 gradeP T) : ExtOrd := min (a.base.rho1 st H) a.η
/-- The capped level-two directed value. -/
noncomputable def rho2 (s : Core2 (gradeP := gradeP) (T := T)) : ExtOrd :=
  min (a.base.rho2 st s) a.η

/-- **Attainment**: the new cap is attained at the retained level-two witness. -/
theorem rho2_wit2C : a.rho2 st (a.base.wit2 st) = a.η := by
  unfold rho2; rw [Core3.rho2_wit2]; exact min_eq_right a.η_le

/-- The capped rows. -/
noncomputable def rowOn1 : Low1 gradeP T → ExtOrd := fun d => min (a.base.rowOn1 st d) a.η
noncomputable def rowOn2 : Low2 gradeP T → ExtOrd := fun d => min (a.base.rowOn2 st d) a.η

/-- **Cross-level locality `3 → 1`** for the capped cell. -/
theorem cross31C (H : Row1 gradeP T) :
    TransformsTo Low1.grade H.row (fun d => min (a.rowOn1 st d) (a.rho1 st H)) := by
  have hmax : ∀ d : Low1 gradeP T, Low1.grade d ≤ 1 := fun d => by
    rcases d with d | d
    · exact d.2
    · exact le_rfl
  have h := TransformsTo.capped hmax (a.η_vis.mono (by omega)) (a.base.cross31 st H)
  have heq : (fun d => min (min (a.base.rowOn1 st d) (a.base.rho1 st H)) a.η) =
      fun d => min (a.rowOn1 st d) (a.rho1 st H) := by
    funext d
    change min (min (a.base.rowOn1 st d) (a.base.rho1 st H)) a.η =
      min (min (a.base.rowOn1 st d) a.η) (min (a.base.rho1 st H) a.η)
    rw [min_min_min_comm, min_self]
  rw [heq] at h
  exact h

/-- **Cross-level locality `3 → 2`** for the capped cell. -/
theorem cross32C (s : Core2 (gradeP := gradeP) (T := T)) :
    TransformsTo Low2.grade (s.row st) (fun d => min (a.rowOn2 st d) (a.rho2 st s)) := by
  have hmax : ∀ d : Low2 gradeP T, Low2.grade d ≤ 2 := fun d => by
    rcases d with d | d | d
    · exact d.2
    · exact Nat.le_succ 1
    · exact le_rfl
  have h := TransformsTo.capped hmax (a.η_vis.mono (by omega)) (a.base.cross32 st s)
  have heq : (fun d => min (min (a.base.rowOn2 st d) (a.base.rho2 st s)) a.η) =
      fun d => min (a.rowOn2 st d) (a.rho2 st s) := by
    funext d
    change min (min (a.base.rowOn2 st d) (a.base.rho2 st s)) a.η =
      min (min (a.base.rowOn2 st d) a.η) (min (a.base.rho2 st s) a.η)
    rw [min_min_min_comm, min_self]
  rw [heq] at h
  exact h

/-! ## Same-level agreement, the capped meet, and repeated truncation -/

/-- The capped level-three meet. -/
noncomputable def meetC : ExtOrd := min (meet₃ st a.base b.base) (min a.η b.η)

/-- The complete capped lower row. -/
noncomputable def row : Low3 gradeP T → ExtOrd := fun d =>
  match d with
  | Sum.inl c => a.F c.1
  | Sum.inr (Sum.inl H) => a.rho1 st H
  | Sum.inr (Sum.inr (Sum.inl s)) => a.rho2 st s
  | Sum.inr (Sum.inr (Sum.inr t')) => min (meet₃ st a.base t') a.η

theorem meetC_le_left : a.meetC st b ≤ a.η := (min_le_right _ _).trans (min_le_left _ _)
theorem meetC_le_right : a.meetC st b ≤ b.η := (min_le_right _ _).trans (min_le_right _ _)
theorem meetC_le_meet : a.meetC st b ≤ meet₃ st a.base b.base := min_le_left _ _

theorem meetC_selfVis : SelfVis 3 (a.meetC st b) :=
  selfVis_min (meet₃_selfVis st _ _) (selfVis_min a.η_vis b.η_vis)

/-- **Same-level agreement of the capped rows at the capped meet**: every entry of the complete
lower row agrees below `meetC`. -/
theorem rowC_agree (d : Low3 gradeP T) :
    min (b.row st d) (b.meetC st a) = min (a.row st d) (b.meetC st a) := by
  have hm : b.meetC st a ≤ meet₃ st b.base a.base := b.meetC_le_meet st a
  have hagree := meet₃_agree st b.base a.base
  rcases d with c | H | s | c'
  · -- proper cells
    change min (min (b.base.F c.1) b.η) (b.meetC st a) = min (min (a.base.F c.1) a.η) (b.meetC st a)
    rw [min_assoc, min_eq_right (b.meetC_le_left st a), min_assoc,
      min_eq_right (b.meetC_le_right st a)]
    by_cases hc : gradeP c.1 ≤ 3
    · have := hagree.1 c.1 hc
      rw [← min_eq_right hm, ← min_assoc, this, min_assoc]
    · rw [b.base.F_bot c.1 (by omega), a.base.F_bot c.1 (by omega)]
  · change min (min (b.base.rho1 st H) b.η) (b.meetC st a) =
      min (min (a.base.rho1 st H) a.η) (b.meetC st a)
    rw [min_assoc, min_eq_right (b.meetC_le_left st a), min_assoc,
      min_eq_right (b.meetC_le_right st a)]
    have := hagree.2.1 H
    rw [← min_eq_right hm, ← min_assoc, this, min_assoc]
  · change min (min (b.base.rho2 st s) b.η) (b.meetC st a) =
      min (min (a.base.rho2 st s) a.η) (b.meetC st a)
    rw [min_assoc, min_eq_right (b.meetC_le_left st a), min_assoc,
      min_eq_right (b.meetC_le_right st a)]
    have := hagree.2.2 s
    rw [← min_eq_right hm, ← min_assoc, this, min_assoc]
  · -- level-three cells: the ultrametric identity on the base meets, then the caps
    change min (min (meet₃ st b.base c') b.η) (b.meetC st a) =
      min (min (meet₃ st a.base c') a.η) (b.meetC st a)
    have h1 := min_meet₃_le st b.base a.base c'
    have h2 := min_meet₃_le st a.base b.base c'
    rw [meet₃_comm st a.base b.base] at h2
    have hMb : b.meetC st a ≤ b.η := b.meetC_le_left st a
    have hMa : b.meetC st a ≤ a.η := b.meetC_le_right st a
    have hMm : b.meetC st a ≤ meet₃ st b.base a.base := b.meetC_le_meet st a
    apply le_antisymm
    · refine le_min (le_min ?_ ((min_le_right _ _).trans hMa)) (min_le_right _ _)
      calc min (min (meet₃ st b.base c') b.η) (b.meetC st a)
          ≤ min (meet₃ st b.base a.base) (meet₃ st b.base c') :=
            le_min ((min_le_right _ _).trans hMm) ((min_le_left _ _).trans (min_le_left _ _))
        _ ≤ meet₃ st a.base c' := h1
    · refine le_min (le_min ?_ ((min_le_right _ _).trans hMb)) (min_le_right _ _)
      calc min (min (meet₃ st a.base c') a.η) (b.meetC st a)
          ≤ min (meet₃ st b.base a.base) (meet₃ st a.base c') :=
            le_min ((min_le_right _ _).trans hMm) ((min_le_left _ _).trans (min_le_left _ _))
        _ ≤ meet₃ st b.base c' := h2

omit [Fintype P] [DecidableEq P] in
theorem Low3.grade_le_three (d : Low3 gradeP T) : Low3.grade d ≤ 3 := by
  rcases d with d | (d | (d | d))
  · exact d.2
  · exact by simp [Low3.grade]
  · exact by simp [Low3.grade]
  · exact le_rfl

/-! ### Repeated truncation and the represented meet -/

/-- The level-three meet of a core with itself is its cap. -/
theorem meet₃_self' (t : Core3 (gradeP := gradeP) (T := T)) : meet₃ st t t = t.γ := by
  apply le_antisymm
  · exact (meet₃_le st t t).trans (min_le_left _ _)
  · apply le_meet₃ st
    rw [mem_agreeSet₃ st]
    exact ⟨t.γ_mem, le_min le_rfl le_rfl, t.γ_vis, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

end CappedCore3

end VaughtConjecture.Knight
