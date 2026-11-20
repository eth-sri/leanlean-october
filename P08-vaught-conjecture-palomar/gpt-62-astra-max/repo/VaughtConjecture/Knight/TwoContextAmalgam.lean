/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FaceExtB

/-! # The labelled amalgam of the two contexts

**The unconditional glued domain** `glueDomain : SemScheme 4` (`semSchemeGlue'` with both face
obligations proved).

**Which pairs of input labellings are simultaneously realizable.**  Rigidity (`rigidity₂`)
forces every respecting labelling of the glued domain to agree at input A's level-one witness
`H₀` and at input B's copy of it.  Input A's specified labelling `p₀` (the row of its cap `ω+4`)
reads `ω+4` there, while input B's specified labelling `p₁` (the row of its cap `ω·2+3`) reads
`ω·2+3` there: the pair `(p₀, p₁)` is **not** simultaneously realizable (`not_realizable_p₀_p₁`).

**The amalgam.**  `Q : S stage₃ 4` labels the glued domain by input B's row pulled back along the
retraction.  Its initial face is literally the labelled type `pA` of `semScheme₀` (the coface
equation `isCoface_pA_Q`), whose labels are input B's row read at input A's cells — input A with
its witnesses raised to input B's cap (`ω·2+3` at `H₀`, `s₀`; `ω+4` at `a₂`; `ω+3` at `a₁`).  Its
fresh face carries input B's specified labelling `p₁` literally, cell by cell, through the copy
embedding `copyB` (`label_copyB`, `rows_copyB`, `cell_copyB`); `typeMap` along the fresh face is
defined (`typeMap_embB`), but its value is the restriction with the induced enumeration, which is
not input B's own enumeration (the copy embedding is not monotone in the cell indices).

Not claimed: any logical extension-spectrum distinction, or realization inside fixed models.
Construction-private (not root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section Amalgam

/-- **The glued domain, unconditional.** -/
noncomputable def glueDomain : SemScheme 4 := semSchemeGlue' faceExtA' faceExtB'

/-- The stage `ω·3`, above input B's cap. -/
noncomputable abbrev stage₃ : Ordinal.{0} := Ordinal.omega0 * (2 : ℕ) + Ordinal.omega0

theorem γ₁_lt_stage₃ : γ₁ < ofOrd stage₃ := by
  rw [γ₁_eq, ofOrd_lt_ofOrd]
  exact add_lt_add_right (Ordinal.natCast_lt_omega0 3) _

/-- Input B's row is bounded by its cap. -/
theorem rowX_b₁_le (x : family₂.X) : family₂.rowX b₁X x ≤ γ₁ := by
  rcases x with c | H | s | a
  · rw [rowX_b₁_inl]; exact (t₀.F_le c).trans γ₀_le_γ₁
  · rw [eq_H₀X, rowX_b₁_H]
  · rw [eq_s₀X, rowX_b₁_s]
  · have ha : a.1 ∈ ({a₁, a₂, b₁} : Finset (CappedCore3 Prop3.gradeP T₀)) := a.2
    rcases Finset.mem_insert.mp ha with h | h
    · have e : a = ⟨a₁, Finset.mem_insert_self _ _⟩ := Subtype.ext h
      rw [e]
      change family₂.rowX b₁X a₁X ≤ γ₁
      rw [rowX_b₁_a₁]; exact η₁_le_γ₀.trans γ₀_le_γ₁
    rcases Finset.mem_insert.mp h with h | h
    · have e : a = ⟨a₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩ := Subtype.ext h
      rw [e]
      change family₂.rowX b₁X a₂X ≤ γ₁
      rw [rowX_b₁_a₂]; exact γ₀_le_γ₁
    · have e : a = ⟨b₁, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))⟩ := Subtype.ext (Finset.mem_singleton.mp h)
      rw [e]
      change family₂.rowX b₁X b₁X ≤ γ₁
      rw [rowX_b₁_b₁]

/-! ### Input B's specified labelling: the row of its cap -/

noncomputable def top₁ : Cell C₁ := family₁.e b₁X₁

theorem cell_top₁ : C₁.cell top₁ = (Finset.univ, 3) := Family.cell_e _ _

theorem hall₁ (d : Cell C₁) : GradedLe (C₁.cell d) (C₁.cell top₁) := by
  rw [cell_top₁]; exact le_top₁ d

/-- **Input B labelled by the row of its cap `b₁`.** -/
noncomputable def p₁ : S stage₃ 3 where
  scheme := semScheme₁
  label d := family₁.rows.E top₁ ⟨d, hall₁ d⟩
  label_bound d := by
    left
    change family₁.rowX (family₁.e.symm (family₁.e b₁X₁)) (family₁.e.symm d) < _
    rw [Equiv.symm_apply_apply, rowX₁_eq, embX₁_b₁]
    exact lt_of_le_of_lt (rowX_b₁_le _) γ₁_lt_stage₃
  respects := (family₁.rows_isConsistent top₁).toRespects hall₁

/-! ### The amalgam's labelling: input B's row pulled back -/

theorem cell_e₂_b₁ : C₂.cell (family₂.e b₁X) = (Finset.univ, 3) := Family.cell_e _ _

theorem grade_le_three_of_not_mute {d : Cell D₂} (hd : ¬ mute₂ d) : D₂.grade d ≤ 3 := by
  by_contra h4
  rw [not_le] at h4
  have h := D₂.grade_le_card_scope d
  have hc : (D₂.scope d).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
  apply hd
  refine Prod.ext ?_ ?_
  · apply Finset.eq_univ_of_card; rw [Fintype.card_fin]; change (D₂.scope d).card = 4; omega
  · change D₂.grade d = 4; omega

theorem hret₂ {d : Cell D₂} (hd : ¬ mute₂ d) :
    GradedLe (C₂.cell (ret₂ d)) (C₂.cell (family₂.e b₁X)) := by
  rw [cell_e₂_b₁]
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₂.grade (ret₂ d) ≤ 3
  rw [← grade_ret₂ d hd]
  exact grade_le_three_of_not_mute hd

/-- **The labelling of the glued domain**: input B's row at the retraction, `⊥` at the mute cell. -/
noncomputable def labelQ (d : Cell D₂) : ExtOrd :=
  if hd : mute₂ d then ⊥ else family₂.rows.E (family₂.e b₁X) ⟨ret₂ d, hret₂ hd⟩

theorem labelQ_of_not_mute {d : Cell D₂} (hd : ¬ mute₂ d) :
    labelQ d = family₂.rows.E (family₂.e b₁X) ⟨ret₂ d, hret₂ hd⟩ := by
  unfold labelQ; rw [dite_of_neg hd]

theorem labelQ_of_mute {d : Cell D₂} (hd : mute₂ d) : labelQ d = ⊥ := by
  unfold labelQ; rw [dite_of_pos hd]

theorem labelQ_eq_rowX {d : Cell D₂} (hd : ¬ mute₂ d) :
    labelQ d = family₂.rowX b₁X (family₂.e.symm (ret₂ d)) := by
  rw [labelQ_of_not_mute hd]
  change family₂.rowX (family₂.e.symm (family₂.e b₁X)) _ = _
  rw [Equiv.symm_apply_apply]

theorem labelQ_lt_stage (d : Cell D₂) : labelQ d < ofOrd stage₃ := by
  by_cases hd : mute₂ d
  · rw [labelQ_of_mute hd]; exact bot_lt_ofOrd _
  · rw [labelQ_eq_rowX hd]; exact lt_of_le_of_lt (rowX_b₁_le _) γ₁_lt_stage₃

/-- The fresh copy of `b₁` at full scope: its row is the labelling. -/
noncomputable def ub₁ : Cell D₂ :=
  Fin.natAdd C₀.card ((Fintype.equivFin New₂) (.inr (.inl ⟨family₂.e b₁X, by
    change (C₂.cell (family₂.e b₁X)).1 = _; rw [cell_e₂_b₁]⟩)))

theorem cell_ub₁ : D₂.cell ub₁ = (Finset.univ, 3) := by
  unfold ub₁
  rw [D₂_cell_natAdd, Equiv.symm_apply_apply]
  change (Finset.univ, (C₂.cell (family₂.e b₁X)).2) = _
  rw [cell_e₂_b₁]

theorem ret₂_ub₁ : ret₂ ub₁ = family₂.e b₁X := by
  unfold ub₁; rw [ret₂_natAdd, Equiv.symm_apply_apply]; rfl

theorem not_mute_ub₁ : ¬ mute₂ ub₁ := by
  intro h
  change D₂.cell ub₁ = _ at h
  rw [cell_ub₁] at h
  exact absurd (congrArg Prod.snd h) (by decide)

theorem below_ub₁ {d : Cell D₂} (hd : ¬ mute₂ d) : GradedLe (D₂.cell d) (D₂.cell ub₁) := by
  rw [cell_ub₁]
  refine ⟨Finset.subset_univ _, ?_⟩
  change D₂.grade d ≤ 3
  rw [grade_ret₂ d hd]
  exact (hret₂ hd).2.trans (by rw [cell_e₂_b₁])

theorem rows₂_ub₁ (d : D₂.below (D₂.cell ub₁)) : rows₂.E ub₁ d = labelQ d.1 := by
  have hd : ¬ mute₂ d.1 := hmute_below₂ ub₁ d.1 not_mute_ub₁ d.2
  rw [rows₂_E_of_not_mute not_mute_ub₁, labelQ_of_not_mute hd]
  exact family₂.rows.E_congr' ret₂_ub₁ rfl

/-- **The labelled amalgam.** -/
noncomputable def Q : S stage₃ 4 where
  scheme := glueDomain
  label := labelQ
  label_bound d := Or.inl (labelQ_lt_stage d)
  respects := by
    have hu := rows₂_isConsistent ub₁
    refine ⟨?_, ?_, ?_⟩
    · intro d
      by_cases hd : mute₂ d
      · rw [labelQ_of_mute hd]; exact (extVisibilityReplace_bot _ _).symm
      · have := hu.orderly ⟨d, below_ub₁ hd⟩
        dsimp only at this
        erw [rows₂_ub₁] at this
        exact this
    · intro Sig
      by_cases hSig : mute₂ Sig
      · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
        funext d
        rw [labelQ_of_mute hSig, min_eq_right bot_le]
      · have key := hu.locality ⟨Sig, below_ub₁ hSig⟩
        refine transformsTo_congr rfl rfl ?_ key
        funext d
        erw [rows₂_ub₁, rows₂_ub₁]
        rfl
    · intro Sig Xi₀ hs hg
      by_cases hSig : mute₂ Sig
      · have hXi : mute₂ Xi₀ := by
          change D₂.cell Xi₀ = _
          change D₂.cell Sig = _ at hSig
          have hs' : Finset.univ ⊆ D₂.scope Xi₀ := by
            have := hs; change (D₂.cell Sig).1 ⊆ _ at this; rw [hSig] at this; exact this
          have hg' : D₂.grade Xi₀ = 4 := by
            have := hg; change (D₂.cell Sig).2 = _ at this; rw [hSig] at this; exact this.symm
          exact Prod.ext (Finset.univ_subset_iff.mp hs') hg'
        refine ⟨Xi₀, rfl, ?_⟩
        rw [labelQ_of_mute hSig]; exact bot_le
      · have hXi : ¬ mute₂ Xi₀ := by
          intro hXi
          apply hSig
          change D₂.cell Xi₀ = _ at hXi
          change D₂.cell Sig = _
          have hg' : D₂.grade Sig = 4 := by
            have := hg; change _ = (D₂.cell Xi₀).2 at this; rw [hXi] at this; exact this
          have hs' : D₂.scope Sig = Finset.univ := by
            apply Finset.eq_univ_of_card
            have := D₂.grade_le_card_scope Sig
            have h4' : (D₂.scope Sig).card ≤ 4 := (Finset.card_le_univ _).trans (by simp)
            rw [Fintype.card_fin]; omega
          exact Prod.ext hs' hg'
        obtain ⟨Xi, hcell, hle⟩ := hu.availability ⟨Sig, below_ub₁ hSig⟩ ⟨Xi₀, below_ub₁ hXi⟩ hs hg
        refine ⟨Xi.1, hcell, ?_⟩
        erw [rows₂_ub₁, rows₂_ub₁] at hle; exact hle

/-! ### The initial face: input A with its witnesses raised to input B's cap -/

/-! ### The fresh face: input B's specified labelling, cell by cell -/

/-! ### The specified pair `(p₀, p₁)` is not simultaneously realizable -/

end Amalgam

end VaughtConjecture.Knight
