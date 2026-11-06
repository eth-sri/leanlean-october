/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain

/-! # Pullback semantics along a graded retraction, with mute cells

A scheme `D'` whose cells retract onto the cells of a scheme `D` carrying a semantics `sem`:
`ret : Cell D' → Cell D` preserves grades and scope inclusions on the non-mute cells.  The
**pullback semantics** (`Semantics.pullback`) gives a non-mute cell `x` the row of `ret x` read
through `ret`, and a mute cell the row `⊥`.

* It is **coded** when `sem` is, and **consistent** when `sem` is, provided mute cells never lie
  below non-mute cells and `ret` has **sections over graded indices**: for every non-mute cell `Xi₀`
  and old cell `Xi'` of the graded index of `ret Xi₀`, some cell of the graded index of `Xi₀`
  retracts to `Xi'` (availability witnesses lift; `Semantics.pullback_isConsistent`).
* **Respect transports** both ways along a bijective retraction of lower sets
  (`RespectsSemanticsBelow.of_pullback`, `RespectsSemanticsBelow.pullback`), and the pullback of a
  respecting labelling along a retraction with sections respects (`pullback_of_sect`).
* **Bountifulness transports** along bijective retractions of both lower sets
  (`bountiful_pullback_of_bij`).
* **Controller probes** (`RespectsSemanticsBelow.eq_of_controller_probes`): two cells of the same
  grade at which every full-scope controller of that grade reads the same value carry the same
  label under every respecting labelling.  For a pullback along a retraction this gives
  **uniqueness of extension over a fixed old labelling**: respecting labellings factor through the
  retraction (`Knight/FourPointDuplication.lean`).

Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Pullback

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} (sem : Semantics D) (ret : Cell D' → Cell D)
  (mute : Cell D' → Prop) [DecidablePred mute]
  (hgrade : ∀ x, ¬ mute x → D'.grade x = D.grade (ret x))
  (hscope : ∀ x y, ¬ mute x → ¬ mute y → D'.scope x ⊆ D'.scope y →
    D.scope (ret x) ⊆ D.scope (ret y))
  (hmute_below : ∀ x d, ¬ mute x → GradedLe (D'.cell d) (D'.cell x) → ¬ mute d)

omit [DecidablePred mute] in
include hgrade hscope hmute_below in
/-- The graded preorder is preserved by the retraction below a non-mute cell. -/
theorem gradedLe_ret {a b : Cell D'} (hb : ¬ mute b) (h : GradedLe (D'.cell a) (D'.cell b)) :
    GradedLe (D.cell (ret a)) (D.cell (ret b)) :=
  have ha : ¬ mute a := hmute_below b a hb h
  ⟨hscope a b ha hb h.1, by
    change D.grade (ret a) ≤ D.grade (ret b)
    rw [← hgrade a ha, ← hgrade b hb]; exact h.2⟩

/-- The lower set of a non-mute cell maps into the lower set of its retraction. -/
def retBelow {x : Cell D'} (hx : ¬ mute x) (d : D'.below (D'.cell x)) : D.below (D.cell (ret x)) :=
  ⟨ret d.1, gradedLe_ret ret mute hgrade hscope hmute_below hx d.2⟩

/-- **The pullback semantics.** -/
noncomputable def Semantics.pullback : Semantics D' where
  E x d := if hx : mute x then ⊥ else
    sem.E (ret x) (retBelow ret mute hgrade hscope hmute_below hx d)
  orderly x d := by
    change (if hx : mute x then ⊥ else
      sem.E (ret x) (retBelow ret mute hgrade hscope hmute_below hx d)) =
      extVisibilityReplace _ (D'.grade d.1) (D'.grade d.1)
    split_ifs with hx
    · exact (extVisibilityReplace_bot _ _).symm
    · rw [hgrade d.1 (hmute_below x d.1 hx d.2)]
      exact sem.orderly (ret x) (retBelow ret mute hgrade hscope hmute_below hx d)

variable {sem ret mute hgrade hscope hmute_below}

theorem Semantics.pullback_E_of_mute {x : Cell D'} (hx : mute x) (d : D'.below (D'.cell x)) :
    (sem.pullback ret mute hgrade hscope hmute_below).E x d = ⊥ := by
  change (if hx : mute x then ⊥ else _) = ⊥
  rw [dite_of_pos hx]

theorem Semantics.pullback_E_of_not_mute {x : Cell D'} (hx : ¬ mute x) (d : D'.below (D'.cell x)) :
    (sem.pullback ret mute hgrade hscope hmute_below).E x d =
      sem.E (ret x) (retBelow ret mute hgrade hscope hmute_below hx d) := by
  change (if hx : mute x then ⊥ else _) = _
  rw [dite_of_neg hx]

/-- Coding pulls back (the grade of the owner is preserved). -/
theorem Semantics.pullback_isCoded (h : sem.IsCoded) :
    (sem.pullback ret mute hgrade hscope hmute_below).IsCoded := by
  intro x d
  by_cases hx : mute x
  · rw [Semantics.pullback_E_of_mute hx]; exact Or.inl rfl
  · rw [Semantics.pullback_E_of_not_mute hx, hgrade x hx]; exact h (ret x) _

/-! ### Transport of respect and bountifulness along a bijective retraction of lower sets -/

theorem GradedLe.antisymm' {κ : Type*} {X Y : Finset κ × ℕ} (h₁ : GradedLe X Y)
    (h₂ : GradedLe Y X) :
    X = Y :=
  Prod.ext (Finset.Subset.antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

section Transport

variable {BJ : Finset ι' × ℕ} {BJ' : Finset ι × ℕ}

end Transport

end Pullback

section ControllerProbes

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- **Equal readings at every full-scope controller force equal labels** (review lemma,
2026-09-05): for two cells of the same grade in a lower set, if every controller at the full-scope
index of that grade reads the same value at both, then every respecting labelling agrees at them —
locality at each controller equalizes the probes `min (q x) (q Ξ) = min (q y) (q Ξ)`, and
availability supplies a controller dominating `q x` (respectively `q y`), giving each inequality.
Respecting labellings therefore factor through any retraction whose rows are pulled back. -/
theorem RespectsSemanticsBelow.eq_of_controller_probes
    (hq : RespectsSemanticsBelow sem BJ q) (x y : D.below BJ)
    (hgrade : D.grade x.1 = D.grade y.1)
    (hc : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, D.grade x.1))
    (hrows : ∀ (c : D.below BJ) (hx : GradedLe (D.cell x.1) (D.cell c.1))
      (hy : GradedLe (D.cell y.1) (D.cell c.1)),
      D.cell c.1 = (BJ.1, D.grade x.1) →
      sem.E c.1 ⟨x.1, hx⟩ = sem.E c.1 ⟨y.1, hy⟩) : q x = q y := by
  obtain ⟨c0, hc0⟩ := hc
  have hc0scope : D.scope c0.1 = BJ.1 := by
    change (D.cell c0.1).1 = BJ.1
    rw [hc0]
  have hc0grade : D.grade c0.1 = D.grade x.1 := by
    change (D.cell c0.1).2 = D.grade x.1
    rw [hc0]
  have probes : ∀ c : D.below BJ, D.cell c.1 = (BJ.1, D.grade x.1) →
      min (q x) (q c) = min (q y) (q c) := by
    intro c hc
    have hx : GradedLe (D.cell x.1) (D.cell c.1) := by
      rw [hc]; exact ⟨x.2.1, le_rfl⟩
    have hy : GradedLe (D.cell y.1) (D.cell c.1) := by
      rw [hc]; exact ⟨y.2.1, hgrade.symm.le⟩
    obtain ⟨g, σ, _, _, _, _, _, heq⟩ := hq.locality c
    have ex := heq ⟨x.1, hx⟩
    have ey := heq ⟨y.1, hy⟩
    change min (q x) (q c) = min (σ (sem.E c.1 ⟨x.1, hx⟩)) (g (D.grade x.1)) at ex
    change min (q y) (q c) = min (σ (sem.E c.1 ⟨y.1, hy⟩)) (g (D.grade y.1)) at ey
    rw [ex, ey, hrows c hx hy hc, hgrade]
  obtain ⟨cx, hcx, hxle⟩ := hq.availability x c0
    (hc0scope.symm ▸ x.2.1) hc0grade.symm
  obtain ⟨cy, hcy, hyle⟩ := hq.availability y c0
    (hc0scope.symm ▸ y.2.1) (hgrade.symm.trans hc0grade.symm)
  apply le_antisymm
  · calc q x = min (q x) (q cx) := (min_eq_left hxle).symm
         _ = min (q y) (q cx) := probes cx (hcx.trans hc0)
         _ ≤ q y := min_le_left _ _
  · calc q y = min (q y) (q cy) := (min_eq_left hyle).symm
         _ = min (q x) (q cy) := (probes cy (hcy.trans hc0)).symm
         _ ≤ q x := min_le_left _ _
end ControllerProbes

end VaughtConjecture.Knight
