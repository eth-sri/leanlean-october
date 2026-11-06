/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows

/-! # Derived finite bottom reflection on the support ladder (newapproach7 new17 §5)

The bounded support theorem that the mixed-extension argument of new17 consumes, proved on the
actual support-ladder rows (`SupportLadderRows`, the reviewer's lane): finite bottom reflection of
an arbitrary ambient's chart on the tracked source values, **derived** from the ladder's exact
lawful shape (`lawful_iff_shape`) rather than assumed.

* **Components.**  The bottom-pattern component of an anchor `a` is the set of ladder points at
  which its image is positive: `index profile a v ≠ 0` (`Component`).  The rank cut is positive
  exactly when two profiles agree at rank one, i.e. have the same field bottom pattern
  (`cut_pos_iff`); so components of agreeing anchors coincide (`component_iff_of_agree`) and
  components of disagreeing anchors are disjoint (`component_disjoint`).
* **Every nonzero lawful ladder section occupies one complete component**
  (`Lawful.support_component`): by `lawful_iff_shape` it is the image of one anchor under a scalar
  table positive at every rank `1 … H`, so its support is exactly that anchor's component — unused
  ranks and rank-zero shadows included.
* **Same component from a positive chart** (`Lawful.support_eq_of_chart`): let `p` be an
  **arbitrary** lawful ladder section (not synchronized, no receiving gate) and `τ` a map fixing
  `⊥` that reads the ladder row of a point `c` as `p` capped at a positive height `h`, with the
  row's own diagonal read as `h`.  The actual spare rung — the parent's leaf, which reads the
  same source ceiling as the diagonal (`row_parent`) — is then positive in `p`, so `p` is nonzero
  and occupies one complete component; that component meets the row's component at the spare
  rung, hence equals it.  (`Agree` of the two anchors at rank one: `agree_of_chart`.)
* **Finite bottom reflection** (`bottom_reflection`): consequently, for every ladder point —
  every rung, used or unused, and every shadow, present or future —
  `τ (row profile c v) = ⊥ ↔ row profile c v = ⊥`.  This is bottom reflection of `τ` on the
  finitely many tracked source values only, not a global property of `τ`.  An all-bottom field
  vector is covered (its rungs are still positive sources).  Zero height is handled separately
  (`bottom_of_height_bot`: every read is `⊥`).
* **The locality corollary** (`SharpWitnessComposition.map_respects_of_bottom_reflection`): a
  bounded map with finite bottom reflection on the values of a lawful section transports its
  lawfulness — every source-block bottom implication, including those of long rows, transfers
  through the same-pattern criterion — with no positive cap and no global bottom reflection.

Nothing here constructs a physical probe or asserts that the installed rows have these charts;
the chart equations are hypotheses. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## The locality corollary -/

namespace SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ}

/-- **Lawfulness transports along a bounded map with finite bottom reflection**: if `ν` reflects
bottom on the values of a lawful section `r`, then `ν ∘ r` is lawful — the source-block bottom
law of `r` (long rows included) transfers by the same-pattern criterion. -/
theorem map_respects_of_bottom_reflection {r}
    (hr : RespectsSemanticsBelow sem BJ r) {K} {ν}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : BoundedMap K ν)
    (hbot : ∀ d, ν (r d) = ⊥ ↔ r d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) :=
  (map_respects_iff_rowBlockBottom hr hK hν).mpr
    (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hr) hbot)

end SharpWitnessComposition

namespace SupportLadderRows

open FiniteProfileControllers

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-! ## Components -/

/-- The rank cut of two profiles is positive iff they agree at rank one (the same field bottom
pattern). -/
theorem cut_pos_iff (hH : 0 < H) (a b : X → ℕ) : 0 < cut H a b ↔ Agree a b 1 :=
  ⟨fun h => (agree_cut H a b).mono h, fun h => le_cut hH h⟩

theorem agree_symm {a b : X → ℕ} {k} (h : Agree a b k) : Agree b a k :=
  fun d => (h d).symm

theorem agree_trans {a b c : X → ℕ} {k} (h₁ : Agree a b k) (h₂ : Agree b c k) :
    Agree a c k := fun d => (h₁ d).trans (h₂ d)

/-- The bottom-pattern component of an anchor: the ladder points at which its image is positive.
-/
def Component (profile : Q → X → ℕ) (a : Q) (v : Point H X Q) : Prop := index profile a v ≠ 0

theorem component_iff (hH : 0 < H) a (v : Point H X Q) :
    Component profile a v ↔
      Agree (profile a) (profile (parent v)) 1 ∧ ceiling profile v ≠ 0 := by
  unfold Component index
  rw [Ne, Nat.min_eq_zero_iff, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(cut_pos_iff hH _ _).mp (Nat.pos_of_ne_zero h1), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.pos_iff_ne_zero.mp ((cut_pos_iff hH _ _).mpr h1), h2⟩

/-- Agreeing anchors have the same component. -/
theorem component_iff_of_agree (hH : 0 < H) {a b : Q} (h : Agree (profile a) (profile b) 1)
    (v : Point H X Q) : Component profile a v ↔ Component profile b v := by
  rw [component_iff hH, component_iff hH]
  exact and_congr_left fun _ =>
    ⟨fun ha => agree_trans (agree_symm h) ha, fun hb => agree_trans h hb⟩

/-- The image of an anchor under a positive scalar table is positive exactly on its component. -/
theorem image_ne_bot_iff a {f} (h0 : f 0 = ⊥)
    (hp : ∀ i, 0 < i → i ≤ H → f i ≠ ⊥) (v : Point H X Q) :
    image profile a f v ≠ ⊥ ↔ Component profile a v := by
  unfold image Component
  constructor
  · grind
  · intro hne
    exact hp _ (Nat.pos_of_ne_zero hne) (index_le a v)

/-! ## Every nonzero lawful section occupies one complete component -/

variable [Finite X] [Finite Q]

/-- **Every nonzero lawful ladder section occupies one complete bottom-pattern component.** -/
theorem Lawful.support_component [Nonempty Q] {q : Point H X Q → ExtOrd}
    (hq : Lawful profile q) (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H) :
    (∀ v, q v = ⊥) ∨ ∃ a : Q, ∀ v, q v ≠ ⊥ ↔ Component profile a v := by
  rcases (lawful_iff_shape hbound hH q).mp hq with hz | ⟨a, f, -, h0, -, hp, he⟩
  · grind
  · refine Or.inr ⟨a, fun v => ?_⟩
    rw [he v]
    exact image_ne_bot_iff a h0 hp v

/-! ## The same component from a positive chart -/

section Chart

variable [Nonempty Q] (hbound : ∀ a d, profile a d ≤ H) (hH : 0 < H)
  {p : Point H X Q → ExtOrd} (hp : Lawful profile p) (c : Point H X Q)
  {τ : ExtOrd → ExtOrd} (hτ : τ ⊥ = ⊥) {h : ExtOrd} (hh : h ≠ ⊥)
  (hread : ∀ v, τ (row profile c v) = min (p v) h) (hdiag : τ (row profile c c) = h)

include hbound hH hp hτ hh hread hdiag

omit [Finite X] [Finite Q] [Nonempty Q] hp hτ in
/-- The actual spare rung — the parent's leaf, reading the source ceiling — is positive in the
ambient. -/
theorem spare_ne_bot : p (leaf hH (parent c)) ≠ ⊥ := by
  have h1 := hread (leaf hH (parent c))
  rw [row_parent hbound hH, hdiag] at h1
  grind

omit [Finite X] [Finite Q] [Nonempty Q] hbound hH hp hdiag in
/-- Outside the row's component the ambient is bottom. -/
theorem ambient_bot_of_not_component (v : Point H X Q) (hv : ¬ Component profile (parent c) v) :
    p v = ⊥ := by
  have hz := not_not.mp hv
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
  have hleaf :=
    (hb _).mp (spare_ne_bot hbound hH c hh hread hdiag)
  have hagree := by
    rw [component_iff hH] at hleaf
    exact hleaf.1
  rw [hb v]
  exact component_iff_of_agree hH hagree v

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

/-! ## The image form: any positive scalar table -/

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
  · exact absurd (hz _) (spare_ne_bot_image hH a₀ hh hread hspare)
  have hleaf :=
    (hb _).mp (spare_ne_bot_image hH a₀ hh hread hspare)
  rw [component_iff hH] at hleaf
  rw [hb v]
  exact component_iff_of_agree hH hleaf.1 v

/-- **Finite bottom reflection on the tracked values of any positive table.** -/
theorem bottom_reflection_image (v : Point H X Q) :
    τ (image profile a₀ f v) = ⊥ ↔ image profile a₀ f v = ⊥ := by
  have hsup := support_eq_of_image_chart hbound hH hp a₀ hh hread hspare v
  have himg := image_ne_bot_iff (profile := profile) a₀ h0 hf v
  grind

end Image

end SupportLadderRows

end VaughtConjecture.Knight
