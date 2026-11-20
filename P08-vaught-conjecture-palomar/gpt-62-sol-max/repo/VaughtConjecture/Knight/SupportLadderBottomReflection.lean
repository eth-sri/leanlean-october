/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ}

/-- **Lawfulness transports along a bounded map with finite bottom reflection**: if `ν` reflects
bottom on the values of a lawful section `r`, then `ν ∘ r` is lawful — the source-block bottom
law of `r` (long rows included) transfers by the same-pattern criterion. -/
theorem map_respects_of_bottom_reflection {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : BoundedMap K ν)
    (hbot : ∀ d, ν (r d) = ⊥ ↔ r d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) :=
  (map_respects_iff_rowBlockBottom hr hK hν).mpr
    (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hr) hbot)

end SharpWitnessComposition

namespace SupportLadderRows

open FiniteProfileControllers

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-- The rank cut of two profiles is positive iff they agree at rank one (the same field bottom
pattern). -/
theorem cut_pos_iff (hH : 0 < H) (a b : X → ℕ) : 0 < cut H a b ↔ Agree a b 1 :=
  ⟨fun h => (agree_cut H a b).mono h, fun h => le_cut hH h⟩

theorem agree_symm {a b : X → ℕ} {k : ℕ} (h : Agree a b k) : Agree b a k :=
  fun d => (h d).symm

theorem agree_trans {a b c : X → ℕ} {k : ℕ} (h₁ : Agree a b k) (h₂ : Agree b c k) :
    Agree a c k := fun d => (h₁ d).trans (h₂ d)

/-- The bottom-pattern component of an anchor: the ladder points at which its image is positive.
-/
def Component (profile : Q → X → ℕ) (a : Q) (v : Point H X Q) : Prop := index profile a v ≠ 0

theorem component_iff (hH : 0 < H) (a : Q) (v : Point H X Q) :
    Component profile a v ↔
      Agree (profile a) (profile (parent v)) 1 ∧ ceiling profile v ≠ 0 := by grind [Component, index, cut_pos_iff]

/-- Agreeing anchors have the same component. -/
theorem component_iff_of_agree (hH : 0 < H) {a b : Q} (h : Agree (profile a) (profile b) 1)
    (v : Point H X Q) : Component profile a v ↔ Component profile b v := by grind [component_iff, agree_trans, agree_symm]

/-- The image of an anchor under a positive scalar table is positive exactly on its component. -/
theorem image_ne_bot_iff (a : Q) {f : ℕ → ExtOrd} (h0 : f 0 = ⊥)
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) (v : Point H X Q) :
    image profile a f v ≠ ⊥ ↔ Component profile a v := by
  unfold image Component
  constructor
  · grind
  · intro hne
    exact hp _ (Nat.pos_of_ne_zero hne) (index_le a v)

variable [Finite X] [Finite Q]

/-- **Every nonzero lawful ladder section occupies one complete bottom-pattern component.** -/
theorem Lawful.support_component [Nonempty Q] {q : Point H X Q → ExtOrd}
    (hq : Lawful profile q) (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) :
    (∀ v, q v = ⊥) ∨ ∃ a : Q, ∀ v, q v ≠ ⊥ ↔ Component profile a v := by
  rcases (lawful_iff_shape hbound hH q).mp hq with hz | ⟨a, f, -, h0, -, hp, he⟩
  · exact Or.inl hz
  · refine Or.inr ⟨a, fun v => ?_⟩
    rw [he v]
    exact image_ne_bot_iff a h0 hp v

section Chart

variable [Nonempty Q] (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
  {p : Point H X Q → ExtOrd} (hp : Lawful profile p) (c : Point H X Q)
  {τ : ExtOrd → ExtOrd} (hτ : τ ⊥ = ⊥) {h : ExtOrd} (hh : h ≠ ⊥)
  (hread : ∀ v, τ (row profile c v) = min (p v) h) (hdiag : τ (row profile c c) = h)

include hbound hH hp hτ hh hread hdiag

omit [Finite X] [Finite Q] [Nonempty Q] hbound hH hp hdiag in
/-- Outside the row's component the ambient is bottom. -/
theorem ambient_bot_of_not_component (v : Point H X Q) (hv : ¬ Component profile (parent c) v) :
    p v = ⊥ := by
  have hz : index profile (parent c) v = 0 := not_not.mp hv
  have h1 := hread v
  rw [row, hz, source_zero, hτ] at h1
  grind

omit hτ in
/-- **The ambient and the source occupy the same component**: the ambient's support is exactly
the component of the row's anchor. -/
theorem Lawful.support_eq_of_chart (v : Point H X Q) :
    p v ≠ ⊥ ↔ Component profile (parent c) v := by
  rcases hp.support_component hbound hH with hz | ⟨b, hb⟩
  · grind
  -- the ambient's anchor agrees with the row's anchor at rank one
  grind [SourcePrefixRows.Agree, parent, component_iff, component_iff_of_agree]

omit [Finite X] [Finite Q] [Nonempty Q] hbound hH hp hread in
/-- The row's own ceiling is positive (its diagonal reads the positive height). -/
theorem ceiling_ne_zero : ceiling profile c ≠ 0 := by
  intro h0
  have h1 := hdiag
  rw [row, index, h0, Nat.min_zero, source_zero, hτ] at h1
  exact hh h1.symm

/-- **Finite bottom reflection on the tracked source values**: at every ladder point, the chart
reads bottom exactly at the bottom sources. -/
theorem bottom_reflection (v : Point H X Q) :
    τ (row profile c v) = ⊥ ↔ row profile c v = ⊥ := by
  have hc0 := ceiling_ne_zero c hτ hh hdiag
  rw [hread v, row, source_bot_iff, Nat.min_eq_zero_iff, or_iff_left hc0]
  constructor
  · intro h1
    by_contra hne
    have hv : Component profile (parent c) v := hne
    have hpv : p v ≠ ⊥ := (Lawful.support_eq_of_chart hbound hH hp c hh hread hdiag v).mpr hv
    grind
  · intro h1
    have hv : ¬ Component profile (parent c) v := fun hv => hv h1
    rw [ambient_bot_of_not_component c hτ hh hread v hv, min_bot_left]

end Chart

section Image

variable [Nonempty Q] (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
  {p : Point H X Q → ExtOrd} (hp : Lawful profile p) (a₀ : Q) {f : ℕ → ExtOrd} (h0 : f 0 = ⊥)
  (hf : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) {τ : ExtOrd → ExtOrd} {h : ExtOrd} (hh : h ≠ ⊥)
  (hread : ∀ v, τ (image profile a₀ f v) = min (p v) h) (hspare : τ (f H) = h)

include hbound hH hp h0 hf hh hread hspare

omit [Finite X] [Finite Q] [Nonempty Q] hbound hp h0 hf in
/-- The spare rung: the anchor's leaf reads the table's ceiling `f H`, hence the height. -/
theorem spare_ne_bot_image : p (leaf hH a₀) ≠ ⊥ := by
  have h1 := hread (leaf hH a₀)
  rw [image, index_leaf, cut_refl, hspare] at h1
  grind

omit h0 hf in
/-- **Same component**: the ambient's support is the anchor's component. -/
theorem support_eq_of_image_chart (v : Point H X Q) :
    p v ≠ ⊥ ↔ Component profile a₀ v := by
  rcases hp.support_component hbound hH with hz | ⟨b, hb⟩
  · exact absurd (hz _) (by solve_by_elim [spare_ne_bot_image])
  have hleaf : Component profile b (leaf hH a₀) :=
    (hb _).mp (by solve_by_elim [spare_ne_bot_image])
  rw [component_iff hH] at hleaf
  rw [hb v]
  exact component_iff_of_agree hH hleaf.1 v

/-- **Finite bottom reflection on the tracked values of any positive table.** -/
theorem bottom_reflection_image (v : Point H X Q) :
    τ (image profile a₀ f v) = ⊥ ↔ image profile a₀ f v = ⊥ := by
  rw [hread v]
  have hsup := support_eq_of_image_chart hbound hH hp a₀ hh hread hspare v
  have himg := image_ne_bot_iff (profile := profile) a₀ h0 hf v
  grind

end Image

end SupportLadderRows

end VaughtConjecture.Knight
