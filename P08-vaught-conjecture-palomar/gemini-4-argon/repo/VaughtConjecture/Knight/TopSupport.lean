/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceOnlyCompositionRepair
public import VaughtConjecture.Knight.RelativeTailFloor
public import VaughtConjecture.Knight.CappedCore

/-! # The finite top-support criterion

The reviewer's notes20 §2 / plan34 §2 (2026-09-19): after the proper labels of a lawful
section `P` are fixed, the remaining ambiguity about which `⊤`-labelled cells stay top has a
finite description.

For `H` a set of top cells of `P` and a proper `β` above every proper label of `P` and visible
at the maximum grade, the **uniform lowering** `lower P H β` keeps every non-top label, keeps
`⊤` on `H`, and replaces `⊤` by `β` off `H`.  It is lawful exactly when

* **top availability** (`TopAvailable`): a surviving top has a surviving top owner at every
  larger same-grade index, and
* **source separation** (`SourceSeparated`): beneath every surviving top owner `c` of grade
  `k`, the rounded source `R_k(E_c(d))` of every lowered top `d` lies strictly below the source
  `E_c(a)` of every surviving top `a` (the diagonal `a = c` included).

**Necessity** (`admissible_of_respects`) holds for an arbitrary lawful `Q` fixing the non-top
labels of `P`, with `H` the actual top set of `Q`: at a surviving top owner the normalized
witness sends surviving top sources to `⊤`, lowered sources to their non-top labels, and
rounded lowered sources to rounded non-top labels, so monotonicity forbids
`E_c(a) ≤ R_k(E_c(d))`.  **Sufficiency** (`respects_lower`) is proved per owner: a proper or
bottom owner sees a literally unchanged locality target; a lowered owner sees the old target
capped at `β`; a surviving owner gets a **retuned witness** — the old normalized witness capped
at `β` below the visible cut `t_c = max R_k(E_c(d))` over the lowered tops beneath `c`, and
unchanged above it.  The retuned map is a bounded map at grade `k` with the bottom fibre of the
old witness (`β` is positive), so the source-block interpolation criterion
(`interpolate_iff_source_blocks`) supplies a faithful witness; long rows and several owners at
one index need nothing extra, and an empty cut collapses the retuned map to the old witness.
It is *not* a scalar post-composition of the old witness, since two sources with the same image
`⊤` can be split by the cut.

The criterion uses neither bountifulness, amalgamation, nor any completion constructor.  The
receiving corollaries (conditional on finite-cut receiving) are in `TopSupportReceiving`.

Construction-private (not root-exported). -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.TopSupport

open Transform Value ExtOrd SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-! ## The top set, the uniform lowering, and the two conditions -/

/-- The top-labelled cells of a labelling (of any cell type: whole schemes or lower sets). -/
def topSet {X : Type*} (P : X → ExtOrd) : Set X := {d | P d = ⊤}

theorem mem_topSet {X : Type*} {P : X → ExtOrd} {d : X} : d ∈ topSet P ↔ P d = ⊤ := Iff.rfl

open Classical in
/-- The **uniform lowering**: non-top labels are kept, `⊤` is kept on `H` and replaced by `β`
off `H`. -/
def lower (P : Cell D → ExtOrd) (H : Set (Cell D)) (β : ExtOrd) (d : Cell D) :
    ExtOrd :=
  if P d = ⊤ then (if d ∈ H then ⊤ else β) else P d

theorem lower_of_ne_top {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d ≠ ⊤) : lower P H β d = P d := by
  unfold lower; rw [ite_eq_right h]

theorem lower_of_mem {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d = ⊤) (hd : d ∈ H) : lower P H β d = ⊤ := by
  unfold lower; rw [ite_eq_left h, ite_eq_left hd]

theorem lower_of_not_mem {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd} {d : Cell D}
    (h : P d = ⊤) (hd : d ∉ H) : lower P H β d = β := by
  unfold lower; rw [ite_eq_left h, ite_eq_right hd]

/-- The top set of the lowering is `H`, for `H` a set of top cells and `β` proper. -/
theorem topSet_lower {P : Cell D → ExtOrd} {H : Set (Cell D)} {β : ExtOrd}
    (hH : H ⊆ topSet P) (hβ : β ≠ ⊤) : topSet (lower P H β) = H := by
  ext d
  refine ⟨fun hd => ?_, fun hd => lower_of_mem (hH hd) hd⟩
  by_cases hP : P d = ⊤
  · exact by_contra fun hdH => hβ ((lower_of_not_mem hP hdH).symm.trans hd)
  · exact absurd ((lower_of_ne_top hP).symm.trans hd) hP

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

/-! ## Necessity, for an arbitrary lawful alternative -/

/-- A replacement of a non-top label is not top. -/
theorem evr_ne_top {x : ExtOrd} (h : x ≠ ⊤) (k i : ℕ) : extVisibilityReplace x k i ≠ ⊤ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact bot_ne_top
  · exact absurd rfl h
  · rw [extVisibilityReplace_ofOrd]; exact ofOrd_ne_top _

theorem selfVis_top_ext (k : ℕ) : SelfVis k ⊤ := extVisibilityReplace_top k k

theorem selfVis_max_of {K : ℕ} {a b : ExtOrd} (ha : SelfVis K a) (hb : SelfVis K b) :
    SelfVis K (max a b) := by
  change extVisibilityReplace (max a b) K K = max a b
  rw [extVisibilityReplace_max a b le_rfl]; exact congrArg₂ max ha hb

/-- A rounding at grade `K` is `K`-visible. -/
theorem selfVis_evr_self (K : ℕ) (t : ExtOrd) : SelfVis K (extVisibilityReplace t K K) := by
  rcases ExtOrd.cases t with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact selfVis_bot K
  · rw [extVisibilityReplace_top]; exact selfVis_top_ext K
  · rw [extVisibilityReplace_ofOrd, selfVis_ofOrd_iff, finitePart_visibilityReplace]
    split_ifs <;> omega

/-- A value is at most its own rounding. -/
theorem le_evr_self (x : ExtOrd) (k : ℕ) : x ≤ extVisibilityReplace x k k := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · exact le_top
  · by_cases h : k ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart h]
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp h), ofOrd_le_ofOrd]
      exact (limitPart_add_finitePart a).symm.trans_le
        (add_le_add le_rfl (by exact_mod_cast (not_le.mp h).le))

variable {sem : Semantics D}

/-- **Nonuniform necessity**: the actual top set of any lawful `Q` fixing the non-top labels of
`P` is an admissible top support of `P`. -/
theorem admissible_of_respects {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    (hoff : ∀ d, P d ≠ ⊤ → Q d = P d) : Admissible sem P (topSet Q) where
  subset d hd := by_contra fun h => h ((hoff d h).symm.trans hd)
  available d hd Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := hQ.availability d Xi₀ hs hg
    exact ⟨Xi, hc, top_le_iff.mp (hd ▸ hle)⟩
  separated c hc a ha d hdP hdQ := by
    rw [mem_topSet] at hc ha hdQ
    obtain ⟨τ, hτ, -, hread⟩ := exists_bounded_exact_capped_witness
      (grade := fun d : D.below (D.cell c) => D.grade d.1) (E := sem.E c)
      (p := fun d => Q d.1) (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2)
      (by rw [hc]; exact selfVis_top_ext _) (hQ.locality c)
    refine not_le.mp fun hle => ?_
    have h1 : τ (sem.E c a) = ⊤ := by rw [hread a, ha, hc]; rfl
    have h2 : τ (extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c)) =
        extVisibilityReplace (τ (sem.E c d)) (D.grade c) (D.grade c) :=
      hτ.clause5 _ _ (by rw [gTop_of_le le_rfl]; exact le_top) _ le_rfl
    have h3 : τ (sem.E c d) ≠ ⊤ := by rw [hread d, hc, min_top_right]; exact hdQ
    have h4 := hτ.mono hle
    rw [h1, h2] at h4
    exact evr_ne_top h3 _ _ (top_le_iff.mp h4)

/-- The rounded sources of the lowered tops beneath an owner are self-visible at its grade. -/
theorem selfVis_sup_evr {X : Type*} (s : Finset X) (f : X → ExtOrd) (k : ℕ) :
    SelfVis k (s.sup fun x => extVisibilityReplace (f x) k k) :=
  Finset.sup_induction (selfVis_bot k) (fun _ ha _ hb => selfVis_max_of ha hb)
    fun x _ => selfVis_evr_self k (f x)

/-! ## Sufficiency -/

/-- **Sufficiency**: an admissible top support gives a lawful uniform lowering. -/
theorem respects_lower {P : Cell D → ExtOrd} (hP : RespectsSemantics sem P) {K : ℕ}
    (hK : ∀ d, D.grade d ≤ K) {β : ExtOrd} (hβ : SelfVis K β) (hβbot : β ≠ ⊥)
    (hβgt : ∀ d, P d ≠ ⊤ → P d < β) {H : Set (Cell D)} (hH : Admissible sem P H) :
    RespectsSemantics sem (lower P H β) where
  orderly d := by
    by_cases hd : P d = ⊤
    · by_cases hdH : d ∈ H
      · rw [lower_of_mem hd hdH]; exact (selfVis_top_ext _).symm
      · rw [lower_of_not_mem hd hdH]; exact (hβ.mono (hK d)).symm
    · rw [lower_of_ne_top hd]; exact hP.orderly d
  availability Sig Xi₀ hs hg := by
    by_cases hSH : P Sig = ⊤ ∧ Sig ∈ H
    · obtain ⟨Xi, hc, hXi⟩ := hH.available Sig hSH.2 Xi₀ hs hg
      exact ⟨Xi, hc, by rw [lower_of_mem (hH.subset hXi) hXi]; exact le_top⟩
    · obtain ⟨Xi, hc, hle⟩ := hP.availability Sig Xi₀ hs hg
      refine ⟨Xi, hc, le_trans (b := min β (P Xi)) ?_ ?_⟩
      · by_cases hS : P Sig = ⊤
        · rw [lower_of_not_mem hS fun h => hSH ⟨hS, h⟩]
          exact le_min le_rfl (le_top.trans (hS ▸ hle))
        · rw [lower_of_ne_top hS]
          exact le_min (hβgt Sig hS).le hle
      · unfold lower; split_ifs <;> [exact le_top; exact min_le_left _ _; exact min_le_right _ _]
  locality c := by
    by_cases hc : P c = ⊤
    · by_cases hcH : c ∈ H
      · classical
        let _ := Fintype.ofFinite (D.below (D.cell c))
        obtain ⟨σ, hσ, -, hread⟩ := exists_bounded_exact_capped_witness
          (grade := fun d : D.below (D.cell c) => D.grade d.1) (E := sem.E c)
          (p := fun d => P d.1) (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2)
          (by rw [hc]; exact selfVis_top_ext _) (hP.locality c)
        have hread' (d : D.below (D.cell c)) : σ (sem.E c d) = P d.1 := by
          rw [hread d]; change min (P d.1) (P c) = P d.1; rw [hc, min_top_right]
        let L : Finset (D.below (D.cell c)) := Finset.univ.filter fun d => P d.1 = ⊤ ∧ d.1 ∉ H
        let R (d : D.below (D.cell c)) : ExtOrd :=
          extVisibilityReplace (sem.E c d) (D.grade c) (D.grade c)
        let t : ExtOrd := L.sup R
        have ht : SelfVis (D.grade c) t := selfVis_sup_evr L (sem.E c) (D.grade c)
        have hβc : SelfVis (D.grade c) β := hβ.mono (hK c)
        let ret : ExtOrd → ExtOrd := fun x => if x ≤ t then min (σ x) β else σ x
        have hbm : BoundedMap (D.grade c) ret :=
          { bot := by dsimp [ret]; rw [hσ.bot, min_eq_left bot_le]
            mono := fun x y hxy => by
              dsimp [ret]
              by_cases hy : y ≤ t
              · rw [ite_eq_left (hxy.trans hy), ite_eq_left hy]
                exact min_le_min_right β (hσ.mono hxy)
              · rw [ite_eq_right hy]
                split_ifs
                · exact (min_le_left _ _).trans (hσ.mono hxy)
                · exact hσ.mono hxy
            comm := fun x k i hk hi => by
              have hcomm := hσ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi
              dsimp [ret]
              by_cases hx : x ≤ t
              · rw [ite_eq_left hx, ite_eq_left ((le_iff_evr_le (ht.mono hk) hi).mp hx), hcomm,
                  evr_min_of_selfVis hβc hk hi]
              · have hx' : ¬ extVisibilityReplace x k i ≤ t := fun h =>
                  hx ((le_iff_evr_le (ht.mono hk) hi).mpr h)
                rw [ite_eq_right hx, ite_eq_right hx', hcomm] }
        have hbot (x : ExtOrd) : ret x = ⊥ ↔ σ x = ⊥ := by
          dsimp [ret]; split_ifs <;> [exact min_eq_bot.trans (or_iff_left hβbot); exact Iff.rfl]
        obtain ⟨τ, hτ, hτread⟩ := (hbm.interpolate_iff_source_blocks
          (Finset.univ.image (sem.E c))).mpr fun x _ y _ hb hx =>
            (hbot y).mpr (witness_bot_of_same_block hσ hb ((hbot x).mp hx))
        apply hτ.transformsTo
        intro d
        have hg : gTop (D.grade (⟨c, GradedLe.refl _⟩ : D.below (D.cell c)).1) (D.grade d.1) = ⊤ :=
          gTop_of_le d.2.2
        rw [hg, min_top_right, hτread _ (Finset.mem_image_of_mem _ (Finset.mem_univ d)),
          lower_of_mem hc hcH, min_top_right]
        dsimp only [ret]
        by_cases hd : P d.1 = ⊤
        · by_cases hdH : d.1 ∈ H
          · have hgt : t < sem.E c d := by
              have hpos : ⊥ < sem.E c d := bot_lt_iff_ne_bot.mpr fun h0 =>
                bot_ne_top (hσ.bot ▸ h0 ▸ (hread' d).trans hd)
              exact (Finset.sup_lt_iff hpos).mpr fun e heL =>
                hH.separated c hcH d hdH e (Finset.mem_filter.mp heL).2.1
                  (Finset.mem_filter.mp heL).2.2
            rw [lower_of_mem hd hdH, ite_eq_right hgt.not_ge, hread', hd]
          · have hle : sem.E c d ≤ t := (le_evr_self _ (D.grade c)).trans
              (Finset.le_sup (f := R) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hdH⟩))
            rw [lower_of_not_mem hd hdH, ite_eq_left hle, hread', hd, min_top_left]
        · rw [lower_of_ne_top hd]
          split_ifs
          · rw [hread', min_eq_left (hβgt _ hd).le]
          · rw [hread']
      · have e : (fun d : D.below (D.cell c) => min (lower P H β d.1) (lower P H β c)) =
            fun d => min (min (P d.1) (P c)) β := by
          funext d
          rw [lower_of_not_mem hc hcH, hc, min_top_right]
          unfold lower; split_ifs with hd hdH
          · rw [hd, min_top_left]
          · rw [hd, min_self, min_top_left]
          · rfl
        rw [e]
        exact TransformsTo.capped (K := D.grade c) (fun d => d.2.2) (hβ.mono (hK c)) (hP.locality c)
    · have e : (fun d : D.below (D.cell c) => min (lower P H β d.1) (lower P H β c)) =
          fun d => min (P d.1) (P c) := by
        funext d
        rw [lower_of_ne_top hc]
        unfold lower; split_ifs with hd hdH
        · rw [hd, min_top_left]
        · rw [hd, min_top_left, min_eq_right (hβgt c hc).le]
        · rfl
      rw [e]; exact hP.locality c

/-! ## Exact readback from a unique or minimal admissible support -/

/-- **Unique admissible support ⇒ exact readback**: if the only admissible support containing
the retained tops `TB` is the whole top set, then a lawful `Q` fixing the non-top labels and
keeping `TB` top is `P`. -/
theorem eq_of_unique_admissible {P Q : Cell D → ExtOrd} (hQ : RespectsSemantics sem Q)
    {TB : Set (Cell D)} (huniq : ∀ H, TB ⊆ H → Admissible sem P H → H = topSet P)
    (hoff : ∀ d, P d ≠ ⊤ → Q d = P d) (hTB : ∀ d ∈ TB, Q d = ⊤) : Q = P := by
  have hH : topSet Q = topSet P := huniq _ (fun d hd => hTB d hd) (admissible_of_respects hQ hoff)
  funext d
  by_cases hd : P d = ⊤
  · rw [hd]; exact mem_topSet.mp (hH ▸ mem_topSet.mpr hd)
  · exact hoff d hd

