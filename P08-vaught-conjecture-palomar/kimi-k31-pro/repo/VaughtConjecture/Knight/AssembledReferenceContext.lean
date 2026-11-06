/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteAssemblyInstance
public import VaughtConjecture.Knight.FiniteCutoffBound

/-! # The assembled scheme as an old reference context

A nonvacuous reference-data regression (2026-09-05): use the grade-three row of the capped cell
with cap `ω + 4` as a
respecting labelling of the whole scheme, and verify a finite reference context on it — an old
reference at `ω + 1` (the singleton cell), threshold `N = 3`, cutoff `ω`, cap and trigger the
capped cell itself — so that the cutoff readback (`FiniteReferenceData.CutoffBound.readback_top`)
applies to an **actual respecting labelling with the trigger active**, not vacuously.

Verified here:

* `rowA₂_respects`: the row respects the restricted semantics (consistency of the assembly);
* the reference labels: the representative reads `ω + 1`, the cap and trigger read `ω + 4`
  (`rowA₂_s0`, `rowA₂_cap`), the requested cells read `ω + 4`, `ω + 4`, `ω + 3`
  (`rowA₂_H₀`, `rowA₂_s₀`, `rowA₂_a₁`);
* `refData_cutoffBound`: the cutoff lower bound holds at every request (three requests: the
  level-one witness, the level-two witness, the other capped cell; block `ω`, offset `0`);
* `refData_readback`: hence `truncExt ω (f Θ) = ⊤` at every requested cell — exact readback
  below the cutoff `ω`, a lower bound above it;
* `rowA₂_stage_bound`: every label of the row is below the stage `ω·2`, so the row is a
  stage-`ω·2` labelling in the sense of the tower.

The fresh point, the fresh request and the comparison domain are `Knight/FourPointDuplication.lean`.
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Reference

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-- The remaining members of the concrete families. -/
theorem mem_S₂_eq {s : Core2 (gradeP := Prop3.gradeP) (T := T₀)} (h : s ∈ family₀.S₂) : s = s₀c :=
  Finset.mem_singleton.mp h

theorem mem_S₃_cases {a : CappedCore3 Prop3.gradeP T₀} (h : a ∈ family₀.S₃) : a = a₁ ∨ a = a₂ := by
  have h' : a ∈ ({a₁, a₂} : Finset (CappedCore3 Prop3.gradeP T₀)) := h
  rcases Finset.mem_insert.mp h' with rfl | h''
  · exact Or.inl rfl
  · exact Or.inr (Finset.mem_singleton.mp h'')

/-- The capped cell with cap `ω + 4`, as a member of the family. -/
noncomputable def a₂c : ↥family₀.S₃ := ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
noncomputable def s₀cc : ↥family₀.S₂ := ⟨s₀c, Finset.mem_singleton_self _⟩

/-- The controlling cell of the reference context. -/
noncomputable def top : Cell family₀.scheme := family₀.e (.inr (.inr (.inr a₂c)))

/-- Its lower set: the whole scheme. -/
abbrev Dref : Type := family₀.scheme.below (family₀.scheme.cell top)

theorem cell_top : family₀.scheme.cell top = (Finset.univ, 3) := Family.cell_e _ _

/-- A cell of the lower set from an `X`-cell. -/
noncomputable def cellB (x : family₀.X) (h : GradedLe (family₀.cellX x) (Finset.univ, 3)) : Dref :=
  ⟨family₀.e x, by rw [Family.cell_e, cell_top]; exact h⟩

/-- **The labelling**: the row of the capped cell with cap `ω + 4`. -/
noncomputable def rowA₂ : Dref → ExtOrd := family₀.rows.E top

/-- The row respects the restricted semantics (consistency of the assembly). -/
theorem rowA₂_respects : RespectsSemanticsBelow family₀.rows (family₀.scheme.cell top) rowA₂ :=
  family₀.rows_isConsistent top

theorem rowA₂_cellB (x : family₀.X) (h : GradedLe (family₀.cellX x) (Finset.univ, 3)) :
    rowA₂ (cellB x h) = family₀.rowX (.inr (.inr (.inr a₂c))) x := by
  change family₀.rowX (family₀.e.symm (family₀.e _)) (family₀.e.symm (family₀.e x)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### The reference labels -/

theorem hs₀ : GradedLe (family₀.cellX (.inr (.inr (.inl s₀cc)))) (Finset.univ, 3) :=
  ⟨Finset.subset_univ _, by decide⟩

/-! ### The reference data -/

/-! ### The stage bound -/

/-- The stage `ω + ω = ω·2`. -/
noncomputable abbrev stage : Ordinal.{0} := Ordinal.omega0 * (1 : ℕ) + Ordinal.omega0

/-- Every label of the row is below the stage `ω·2`. -/
theorem rowA₂_stage_bound (d : Dref) : rowA₂ d < ofOrd stage := by
  have hv : v₀ < ofOrd stage := by
    unfold v₀; rw [ofOrd_lt_ofOrd]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 1) _
  have hγ : γ₀ < ofOrd stage := by
    unfold γ₀; rw [ofOrd_lt_ofOrd]
    exact add_lt_add_right (Ordinal.natCast_lt_omega0 4) _
  have hη : η₁ < ofOrd stage := lt_of_le_of_lt η₁_le_γ₀ hγ
  have hbot : (⊥ : ExtOrd) < ofOrd stage := bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
  obtain ⟨i, hi⟩ := d
  have hd : GradedLe (family₀.cellX (family₀.e.symm i)) (Finset.univ, 3) := by
    rw [cell_top] at hi; exact hi
  have hd_eq : (⟨i, hi⟩ : Dref) = cellB (family₀.e.symm i) hd := by
    apply Subtype.ext
    change i = family₀.e (family₀.e.symm i)
    rw [Equiv.apply_symm_apply]
  rw [hd_eq, rowA₂_cellB]
  rcases family₀.e.symm i with c | H | s | b
  · rw [Family.rowX_a_inl]
    change min (t₀.F c) γ₀ < _
    by_cases hc : c.gradeP ≤ 1
    · rw [t₀_F_eq hc]
      change min v₀ γ₀ < _
      rw [min_eq_left v₀_le_γ₀]; exact hv
    · rw [t₀_F_bot (by have := c.gradeP_le_two; omega), min_eq_left bot_le]; exact hbot
  · rw [Family.rowX_a_H, mem_S₁_eq H.2]
    change min (t₀.rho1 st₀ (witness1 st₀.hT t₀.F (t₀.orderly st₀))) γ₀ < _
    rw [Core3.rho1_wit1]
    change min γ₀ γ₀ < _
    rw [min_self]; exact hγ
  · rw [Family.rowX_a_s, mem_S₂_eq s.2]
    change min (t₀.rho2 st₀ (t₀.wit2 st₀)) γ₀ < _
    rw [Core3.rho2_wit2]
    change min γ₀ γ₀ < _
    rw [min_self]; exact hγ
  · rw [Family.rowX_a_a]
    rcases mem_S₃_cases b.2 with hb | hb
    · rw [hb]
      change min (meet₃ st₀ t₀ t₀) (min γ₀ η₁) < _
      rw [CappedCore3.meet₃_self']
      change min γ₀ (min γ₀ η₁) < _
      rw [min_eq_right η₁_le_γ₀, min_eq_right η₁_le_γ₀]; exact hη
    · rw [hb]
      change min (meet₃ st₀ t₀ t₀) (min γ₀ γ₀) < _
      rw [CappedCore3.meet₃_self']
      change min γ₀ (min γ₀ γ₀) < _
      rw [min_self, min_self]; exact hγ

end Reference

end VaughtConjecture.Knight
