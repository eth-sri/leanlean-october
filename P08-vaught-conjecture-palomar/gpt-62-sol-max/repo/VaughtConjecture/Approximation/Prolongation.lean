/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.Basic

@[expose] public section

namespace VaughtConjecture

universe u v w w'

namespace TypeTower.Realization

variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α β γ : Λ} {M : Type w}

section TargetClass

variable (C : ∀ {δ : Λ} {N : Type w}, T.Realization δ N → Prop)

/-- `R` prolongs to stage `β` **within the target class `C`**: some stage-`β` realization in `C`
reduces, up to isomorphism, to `R`.  With `C := IsModel` this is Knight-VC's
`PaperExactModelExpandsTo` (Knight's Def. 5.1.1 up to isomorphism of the source). -/
def ProlongsToIn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ∃ (N : Type w) (R' : T.Realization β N), C R' ∧ Nonempty ((R'.reduct hβ).Iso R)

/-- `R` prolongs to stage `β` within `C` **on its own carrier**: Knight's Def. 5.1.1 verbatim
when `C := IsModel`. -/
def ProlongsToOnIn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ∃ R' : T.Realization β M, C R' ∧ R'.reduct hβ = R

/-- No prolongation within `C` (Knight-VC `NoExpansionTo` / `FailsAtAlphaOmega` with the model
axioms, for `C := IsModel`). -/
def NoProlongationToIn (R : T.Realization α M) (hβ : α ≤ β) : Prop :=
  ¬ R.ProlongsToIn C hβ

variable {C}

theorem ProlongsToOnIn.prolongsToIn {R : T.Realization α M} {hβ : α ≤ β}
    (h : R.ProlongsToOnIn C hβ) : R.ProlongsToIn C hβ := by
  obtain ⟨R', hC, rfl⟩ := h
  exact ⟨M, R', hC, ⟨Iso.refl _⟩⟩

theorem ProlongsToIn.of_isIso {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) {hβ : α ≤ β} (h : R.ProlongsToIn C hβ) :
    R₂.ProlongsToIn C hβ := by
  obtain ⟨K, R', hC, ⟨i⟩⟩ := h
  exact ⟨K, R', hC, ⟨i.trans ⟨e, hi⟩⟩⟩

/-- **Isomorphism invariance** of prolongation within a target class — no hypothesis on `C`. -/
theorem IsIso.prolongsToIn_iff {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    {e : M ≃ N} (hi : R.IsIso R₂ e) (hβ : α ≤ β) :
    R.ProlongsToIn C hβ ↔ R₂.ProlongsToIn C hβ :=
  ⟨ProlongsToIn.of_isIso hi, ProlongsToIn.of_isIso (IsIso.symm hi)⟩

theorem Iso.prolongsToIn_iff {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    (i : R.Iso R₂) (hβ : α ≤ β) : R.ProlongsToIn C hβ ↔ R₂.ProlongsToIn C hβ :=
  IsIso.prolongsToIn_iff i.2 hβ

theorem prolongsToIn_iff_of_iso {N : Type w} {R : T.Realization α M} {R₂ : T.Realization α N}
    (h : Nonempty (R.Iso R₂)) (hβ : α ≤ β) : R.ProlongsToIn C hβ ↔ R₂.ProlongsToIn C hβ :=
  h.elim fun i => i.prolongsToIn_iff hβ

/-- If `C` is closed under push-forward along bijections of carriers, prolongation within `C` up
to isomorphism is literal prolongation within `C` on the carrier of the source. -/
theorem ProlongsToIn.prolongsToOnIn
    (hC : ∀ {δ : Λ} {N N' : Type w} (e : N ≃ N') (R' : T.Realization δ N), C R' → C (R'.map e))
    {R : T.Realization α M} {hβ : α ≤ β} (h : R.ProlongsToIn C hβ) : R.ProlongsToOnIn C hβ := by
  obtain ⟨N, R', hR', ⟨i⟩⟩ := h
  exact ⟨R'.map i.1, hC i.1 R' hR', by rw [reduct_map, IsIso.map_eq i.2]⟩

theorem prolongsToIn_iff_prolongsToOnIn
    (hC : ∀ {δ : Λ} {N N' : Type w} (e : N ≃ N') (R' : T.Realization δ N), C R' → C (R'.map e))
    (R : T.Realization α M) (hβ : α ≤ β) : R.ProlongsToIn C hβ ↔ R.ProlongsToOnIn C hβ :=
  ⟨ProlongsToIn.prolongsToOnIn hC, ProlongsToOnIn.prolongsToIn⟩

/-- If `C` is closed under reduction, prolongation within `C` is **downward closed** in the target
stage. -/
theorem ProlongsToIn.mono
    (hC : ∀ {δ δ' : Λ} (h : δ ≤ δ') {N : Type w} (R' : T.Realization δ' N),
      C R' → C (R'.reduct h))
    {R : T.Realization α M} {hβ : α ≤ β} (hβγ : β ≤ γ) (h : R.ProlongsToIn C (hβ.trans hβγ)) :
    R.ProlongsToIn C hβ := by
  obtain ⟨N, R', hR', ⟨i⟩⟩ := h
  exact ⟨N, R'.reduct hβγ, hC hβγ R' hR', ⟨by rw [reduct_reduct]; exact i⟩⟩

end TargetClass

end TypeTower.Realization

end VaughtConjecture
