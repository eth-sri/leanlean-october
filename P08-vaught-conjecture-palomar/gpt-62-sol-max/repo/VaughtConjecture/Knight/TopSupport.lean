/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceOnlyCompositionRepair
public import VaughtConjecture.Knight.RelativeTailFloor
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.NormalForm

@[expose] public section

namespace VaughtConjecture.Knight.TopSupport

open Transform Value ExtOrd SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The top-labelled cells of a labelling (of any cell type: whole schemes or lower sets). -/
def topSet {X : Type*} (P : X → ExtOrd) : Set X := {d | P d = ⊤}

theorem mem_topSet {X : Type*} {P : X → ExtOrd} {d : X} : d ∈ topSet P ↔ P d = ⊤ := Iff.rfl

open Classical in
/-- The **uniform lowering**: non-top labels are kept, `⊤` is kept on `H` and replaced by `β`
off `H`. -/
noncomputable def lower (P : Cell D → ExtOrd) (H : Set (Cell D)) (β : ExtOrd) (d : Cell D) :
    ExtOrd :=
  if P d = ⊤ then (if d ∈ H then ⊤ else β) else P d

theorem lower_of_ne_top {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d ≠ ⊤) : lower P H β d = P d := by
  unfold lower; simp_all

theorem lower_of_mem {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d = ⊤) (hd : d ∈ H) : lower P H β d = ⊤ := by
  unfold lower; simp_all

theorem lower_of_not_mem {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d = ⊤) (hd : d ∉ H) : lower P H β d = β := by
  unfold lower; simp_all

/-- The top set of the lowering is `H`, for `H` a set of top cells and `β` proper. -/
theorem topSet_lower {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd}
    (hH : H ⊆ topSet P) (hβ : β ≠ ⊤) : topSet (lower P H β) = H := by
  ext d
  constructor
  · intro hd
    by_cases hP : P d = ⊤
    · by_contra hdH
      exact hβ ((lower_of_not_mem hP hdH).symm.trans hd)
    · exact absurd ((lower_of_ne_top hP).symm.trans hd) hP
  solve_by_elim [lower_of_mem]

/-- **Top availability**: a cell of `H` has a cell of `H` at every larger same-grade index. -/
def TopAvailable (D : CellScheme A) (H : Set (Cell D)) : Prop :=
  ∀ d ∈ H, ∀ Xi₀ : Cell D, D.scope d ⊆ D.scope Xi₀ → D.grade d = D.grade Xi₀ →
    ∃ Xi : Cell D, D.cell Xi = D.cell Xi₀ ∧ Xi ∈ H

/-- **Source separation**: beneath every surviving top owner `c` of grade `k`, the rounded
source of every lowered top lies strictly below the source of every surviving top. -/
def SourceSeparated (sem : Semantics D) (P : Cell D → ExtOrd) (H : Set (Cell D)) : Prop :=
  ∀ c ∈ H, ∀ a : D.below (D.cell c), a.1 ∈ H →
    ∀ d : D.below (D.cell c), P d.1 = ⊤ → d.1 ∉ H →
      extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c) < sem.E c a

/-- An **admissible** top support: a set of top cells satisfying both conditions. -/
structure Admissible (sem : Semantics D) (P : Cell D → ExtOrd) (H : Set (Cell D)) : Prop where
  subset : H ⊆ topSet P
  available : TopAvailable D H
  separated : SourceSeparated sem P H

/-- A replacement of a non-top label is not top. -/
theorem evr_ne_top {x : ExtOrd} (h : x ≠ ⊤) (k i : ℕ) : extVisibilityReplace x k i ≠ ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  all_goals simp_all

theorem selfVis_top_ext (k : ℕ) : SelfVis k ⊤ := extVisibilityReplace_top k k

theorem selfVis_max_of {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by grind

/-- A rounding at grade `K` is `K`-visible. -/
theorem selfVis_evr_self (K : ℕ) (t : ExtOrd) : SelfVis K (extVisibilityReplace t K K) := by
  rcases ExtOrd.cases t with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    aesop

/-- A value is at most its own rounding. -/
theorem le_evr_self (x : ExtOrd) (k : ℕ) : x ≤ extVisibilityReplace x k k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · by_cases h : k ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart h]
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp h), ofOrd_le_ofOrd]
      calc a = limitPart a + (finitePart a : Ordinal) := (limitPart_add_finitePart a).symm
        _ ≤ limitPart a + (k : Ordinal) := by (simp_all <;> omega)

variable {sem : Semantics D}

/-- The top set of a lawful labelling is top-available. -/
theorem topAvailable_of_respects {Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q) :
    TopAvailable D (topSet Q) := by
  intro d hd Xi₀ hs hg
  obtain ⟨Xi, hc, hle⟩ := hQ.availability d Xi₀ hs hg
  grind [mem_topSet]

/-- **Necessity of source separation**: the top set of any lawful `Q` is source-separated
relative to any `P` (the argument reads only the tops of `Q`). -/
theorem sourceSeparated_of_respects (P : Cell D → ExtOrd) {Q : Cell D → ExtOrd}
    (hQ : RespectsSemantics sem Q) : SourceSeparated sem P (topSet Q) := by
  intro c hc a ha d hdP hdQ
  rw [mem_topSet] at hc ha hdQ
  obtain ⟨τ, hτ, -, hread⟩ := hQ.rowWitness c
  by_contra hle
  have hle' := not_lt.mp hle
  have h1 : τ (sem.E c a) = ⊤ := by grind
  have h2 : τ (extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c)) =
      extVisibilityReplace (τ (sem.E c d)) (D.grade c) (D.grade c) :=
    hτ.comm _ le_rfl le_rfl
  have h3 : τ (sem.E c d) ≠ ⊤ := by grind
  have h4 := hτ.mono hle'
  grind [evr_ne_top]

/-- **Nonuniform necessity**: the actual top set of any lawful `Q` fixing the non-top labels of
`P` is an admissible top support of `P`. -/
theorem admissible_of_respects {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    (hoff : ∀ d, P d ≠ ⊤ → Q d = P d) : Admissible sem P (topSet Q) where
  subset d hd := by
    rw [mem_topSet] at hd ⊢
    grind
  available := topAvailable_of_respects hQ
  separated := sourceSeparated_of_respects P hQ

/-- The **retuned map**: the old witness capped at `β` at and below the cut `t`, unchanged
above it. -/
noncomputable def retune (σ : ExtOrd → ExtOrd) (t β x : ExtOrd) : ExtOrd :=
  if x ≤ t then min (σ x) β else σ x

theorem retune_of_le {σ : ExtOrd → ExtOrd} {t β x : ExtOrd} (h : x ≤ t) :
    retune σ t β x = min (σ x) β := ite_eq_left h

theorem retune_of_gt {σ : ExtOrd → ExtOrd} {t β x : ExtOrd} (h : ¬ x ≤ t) :
    retune σ t β x = σ x := ite_eq_right h

/-- The retuned map has the bottom fibre of the old witness. -/
theorem retune_eq_bot_iff {σ : ExtOrd → ExtOrd} {t β x : ExtOrd} (hβ : β ≠ ⊥) :
    retune σ t β x = ⊥ ↔ σ x = ⊥ := by
  by_cases h : x ≤ t
  · rw [retune_of_le h, min_eq_bot, or_iff_left hβ]
  · rw [retune_of_gt h]

/-- **The retuned map is a bounded map** at grade `K`, for a `K`-visible cut and cap. -/
theorem boundedMap_retune {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ) {t β : ExtOrd}
    (ht : SelfVis K t) (hβ : SelfVis K β) : BoundedMap K (retune σ t β) where
  bot := by rw [retune_of_le bot_le, hσ.bot, min_eq_left bot_le]
  mono := by
    intro x y hxy
    by_cases hy : y ≤ t
    · rw [retune_of_le (hxy.trans hy), retune_of_le hy]
      exact min_le_min_right β (hσ.mono hxy)
    · rw [retune_of_gt hy]
      by_cases hx : x ≤ t
      · rw [retune_of_le hx]; exact (min_le_left _ _).trans (hσ.mono hxy)
      · rw [retune_of_gt hx]; exact hσ.mono hxy
  comm := by
    intro x k i hk hi
    have hcomm := hσ.comm x hk hi
    by_cases hx : x ≤ t
    · rw [retune_of_le hx, retune_of_le ((le_iff_evr_le (ht.mono hk) hi).mp hx), hcomm,
        evr_min_of_selfVis hβ hk hi]
    · have hx' : ¬ extVisibilityReplace x k i ≤ t := fun h =>
        hx ((le_iff_evr_le (ht.mono hk) hi).mpr h)
      rw [retune_of_gt hx, retune_of_gt hx', hcomm]

/-- The retuned map interpolates to a faithful witness on any finite source set (the bottom
fibre is unchanged, so the source-block criterion is inherited from the old witness). -/
theorem exists_witness_retune {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop K) σ)
    {t β : ExtOrd} (ht : SelfVis K t) (hβ : SelfVis K β) (hβbot : β ≠ ⊥) (s : Finset ExtOrd) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop K) τ ∧ ∀ x ∈ s, τ x = retune σ t β x := by
  apply ((boundedMap_retune hσ ht hβ).interpolate_iff_source_blocks s).mpr
  intro x _ y _ hb hx
  rw [retune_eq_bot_iff hβbot] at hx ⊢
  exact witness_bot_of_same_block hσ hb hx

/-- The rounded sources of the lowered tops beneath an owner are self-visible at its grade. -/
theorem selfVis_sup_evr {X : Type*} (s : Finset X) (f : X → ExtOrd) (k : ℕ) :
    SelfVis k (s.sup fun x => extVisibilityReplace (f x) k k) := Finset.sup_induction (selfVis_bot k) (fun a ha b hb => selfVis_max_of ha hb)
    fun x _ => selfVis_evr_self k (f x)

/-- **Sufficiency**: an admissible top support gives a lawful uniform lowering. -/
theorem respects_lower {P : Cell D → ExtOrd} (hP : RespectsSemantics sem P) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {β : ExtOrd} (hβ : SelfVis K β) (hβbot : β ≠ ⊥)
    (hβgt : ∀ d, P d ≠ ⊤ → P d < β) {H : Set (Cell D)} (hH : Admissible sem P H) :
    RespectsSemantics sem (lower P H β) where
  orderly d := by
    by_cases hd : P d = ⊤
    · by_cases hdH : d ∈ H
      · rw [lower_of_mem hd hdH]; rfl
      · rw [lower_of_not_mem hd hdH]; exact (hβ.mono (hK d)).symm
    · rw [lower_of_ne_top hd]; exact hP.orderly d
  availability Sig Xi₀ hs hg := by
    by_cases hS : P Sig = ⊤
    · by_cases hSH : Sig ∈ H
      · obtain ⟨Xi, hc, hXi⟩ := hH.available Sig hSH Xi₀ hs hg
        refine ⟨Xi, hc, ?_⟩
        rw [lower_of_mem (hH.subset hXi) hXi]; simp
      · obtain ⟨Xi, hc, hle⟩ := hP.availability Sig Xi₀ hs hg
        refine ⟨Xi, hc, ?_⟩
        rw [hS] at hle
        have hXi : P Xi = ⊤ := top_le_iff.mp hle
        rw [lower_of_not_mem hS hSH]
        by_cases hXiH : Xi ∈ H
        · rw [lower_of_mem hXi hXiH]; simp
        · rw [lower_of_not_mem hXi hXiH]
    · obtain ⟨Xi, hc, hle⟩ := hP.availability Sig Xi₀ hs hg
      refine ⟨Xi, hc, ?_⟩
      rw [lower_of_ne_top hS]
      by_cases hXi : P Xi = ⊤
      · by_cases hXiH : Xi ∈ H
        · rw [lower_of_mem hXi hXiH]; simp
        · rw [lower_of_not_mem hXi hXiH]; grind
      · rw [lower_of_ne_top hXi]; assumption
  locality c := by
    by_cases hc : P c = ⊤
    · by_cases hcH : c ∈ H
      · -- a surviving top owner: the retuned witness
        classical
        let _ := Fintype.ofFinite (D.below (D.cell c))
        obtain ⟨σ, hσ, -, hread⟩ := hP.rowWitness c
        have hread' : ∀ d : D.below (D.cell c), σ (sem.E c d) = P d.1 := fun d => by grind
        -- the cut
        let L : Finset (D.below (D.cell c)) := Finset.univ.filter fun d => P d.1 = ⊤ ∧ d.1 ∉ H
        let R : D.below (D.cell c) → ExtOrd := fun d =>
          extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c)
        let t : ExtOrd := L.sup R
        have ht : SelfVis (D.grade c) t := selfVis_sup_evr L (sem.E c) (D.grade c)
        have hcut : ∀ d : D.below (D.cell c), P d.1 = ⊤ → d.1 ∉ H → sem.E c d ≤ t := by
          intro d hd hdH
          exact (le_evr_self _ (D.grade c)).trans
            (Finset.le_sup (f := R) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hdH⟩))
        have hsep : ∀ a : D.below (D.cell c), a.1 ∈ H → ¬ sem.E c a ≤ t := by
          intro a haH hle
          by_cases hL : L.Nonempty
          · obtain ⟨d, hdL, hdt⟩ := Finset.exists_mem_eq_sup L hL R
            obtain ⟨-, hd, hdH⟩ := Finset.mem_filter.mp hdL
            have hlt := hH.separated c hcH a haH d hd hdH
            grind
          · rw [Finset.not_nonempty_iff_eq_empty] at hL
            have ht0 : t = ⊥ := by simp only [t, hL, Finset.sup_empty]
            rw [ht0, le_bot_iff] at hle
            have h1 := hread' a
            rw [hle, hσ.bot, hH.subset haH] at h1
            trivial
        obtain ⟨τ, hτ, hτread⟩ := exists_witness_retune hσ ht (hβ.mono (hK c)) hβbot
          (Finset.univ.image (sem.E c))
        apply hτ.transformsTo
        intro d
        have hg : gTop (D.grade (⟨c, GradedLe.refl _⟩ : D.below (D.cell c)).1) (D.grade d.1) = ⊤ :=
          gTop_of_le d.2.2
        rw [hg, min_top_right, hτread _ (Finset.mem_image_of_mem _ (Finset.mem_univ d)),
          lower_of_mem hc hcH, min_top_right]
        by_cases hd : P d.1 = ⊤
        · by_cases hdH : d.1 ∈ H
          · rw [lower_of_mem hd hdH, retune_of_gt (hsep d hdH), hread', hd]
          · rw [lower_of_not_mem hd hdH, retune_of_le (hcut d hd hdH), hread', hd, min_top_left]
        · rw [lower_of_ne_top hd]
          by_cases hdt : sem.E c d ≤ t
          · rw [retune_of_le hdt, hread', min_eq_left (hβgt _ hd).le]
          · rw [retune_of_gt hdt, hread']
      · -- a lowered top owner: the old target capped at `β`
        have key := TransformsTo.cap (hP.locality c) (fun d => d.2.2) (hβ.mono (hK c))
        have e : (fun d : D.below (D.cell c) => min (lower P H β d.1) (lower P H β c)) =
            fun d => min (min (P d.1) (P c)) β := by
          funext d
          rw [lower_of_not_mem hc hcH, hc, min_top_right]
          by_cases hd : P d.1 = ⊤
          · rw [hd, min_top_left]
            by_cases hdH : d.1 ∈ H
            · rw [lower_of_mem hd hdH, min_top_left]
            · rw [lower_of_not_mem hd hdH, min_self]
          · rw [lower_of_ne_top hd]
        simp_all
    · -- a proper or bottom owner: a literally unchanged target
      have e : (fun d : D.below (D.cell c) => min (lower P H β d.1) (lower P H β c)) =
          fun d => min (P d.1) (P c) := by
        funext d
        rw [lower_of_ne_top hc]
        by_cases hd : P d.1 = ⊤
        · rw [hd, min_top_left]
          by_cases hdH : d.1 ∈ H
          · rw [lower_of_mem hd hdH, min_top_left]
          · rw [lower_of_not_mem hd hdH, min_eq_right (hβgt c hc).le]
        · rw [lower_of_ne_top hd]
      rw [e]; exact hP.locality c

/-- **Unique admissible support ⇒ exact readback**: if the only admissible support containing
the retained tops `TB` is the whole top set, then a lawful `Q` fixing the non-top labels and
keeping `TB` top is `P`. -/
theorem eq_of_unique_admissible {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    {TB : Set (Cell D)} (huniq : ∀ H, TB ⊆ H → Admissible sem P H → H = topSet P)
    (hoff : ∀ d, P d ≠ ⊤ → Q d = P d) (hTB : ∀ d ∈ TB, Q d = ⊤) : Q = P := by
  have hH : topSet Q = topSet P :=
    huniq _ (fun d hd => hTB d hd) (admissible_of_respects hQ hoff)
  funext d
  by_cases hd : P d = ⊤
  · rw [hd]; exact (mem_topSet.mp (hH ▸ (mem_topSet.mpr hd)))
  tauto

end VaughtConjecture.Knight.TopSupport
