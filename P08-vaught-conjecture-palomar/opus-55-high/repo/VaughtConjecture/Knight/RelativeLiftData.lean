/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.SlackCutPasting
public import VaughtConjecture.Knight.CountedEncoding
public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.OrbitBlock
public import VaughtConjecture.Knight.Coface

/-! # Data for the relative lifting theorem of pattern-guarded probes

The reviewer's notes3 (`guarded_probe_construction.md` §§1–4, 2026-09-18) separate three
things: a *reference template* (one lawful labelling of the unchanged candidate scheme), the
*allowed* inherited pairs (lawful on the old and candidate faces, agreeing on the root, and
correct whenever the old labelling has the distinguished bottom pattern), and the *relative
lifting lemma* (every allowed pair has every relative old-face lift, using the original
candidate's bountifulness).  This file fixes the data and proves the ingredients:

* scalar facts about replacement under an `N`-visible cap (`evr_min_of_selfVis`,
  `lt_of_evr_lt`, `le_evr_zero_of_le`, `evr_zero_le`);
* a whole labelling from a lawful section below the top index (`RespectsSemantics.of_below_top`);
* the **same-bottom-pattern transport** (`map_respects_of_same_bottom_pattern`, from the
  reviewer's uncompiled helper `PatternTransport.lean` in the notes3 package): a bounded
  replacement-commuting image of a lawful section with the bottom flags of a lawful section is
  lawful — this is what makes long semantic source rows harmless;
* the request data `Requests` (old cap `C` of grade `N`, the marker offset `R < N`,
  requested-bottom `Z`, exact `F` with references and offsets, high `T` with the marker `a`;
  references and marker live **below the cap**), the target relations `Correct`, the
  distinguished class `InClass` (a bottom pattern on the **lower domain below the cap**), the
  relative data `RelativeData` (old and candidate schemes, a full-scope grade-`N` cap inside a
  possibly larger private context, the cleaned donor `e` on the cap's lower domain with bottom
  set exactly the class and literal elsewhere, the root transport `κ` into that domain, the
  candidate's bountifulness, the coverage of the candidate cells, and the template `V` with its
  frame inequalities), `Allowed`;
* the root lift from candidate bountifulness (`RelativeData.lift_root`) and the capped decoder
  of a lawful old labelling at the cap (`RelativeData.decoder`);
* **the selector** `g(u) = u(C)` in the class, `⊥` outside (`selector`; the reviewer's notes7
  §3): positive exactly in the class (`selector_ne_bot_iff`), equal to the cap when positive
  (`selector_eq_cap`), retained under cap agreement (`selector_cap_agree`), and the
  positive-triggered form of `Allowed` (`allowed_iff_selector`).

**General cap (notes7, 2026-09-19).**  The old scheme may have cells above grade `N`; they are
part of the protected private context but outside the pattern test, the donor, and the
decoder, all of which live on `DA.below (DA.cell C)`.  The marker reads at offset `R < N`
(plan 21); the block-floor version is `R = 0` (`dOf_zero`).

The cleaned donor's construction and the template's construction are in
`Knight/ReceivingTemplate.lean`.  Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Replacement under a visible cap -/

theorem evr_monotone k i (hi : i ≤ k) :
    Monotone (fun x => extVisibilityReplace x k i) :=
  fun _ _ h => evr_mono h hi

/-- Replacement at grade at most `N` commutes with meets against an `N`-visible value. -/
theorem evr_min_of_selfVis {γ} {N} (hγ : SelfVis N γ) {k i} (hk : k ≤ N)
    (hi : i ≤ k) x :
    extVisibilityReplace (min x γ) k i = min (extVisibilityReplace x k i) γ := by
  rw [(evr_monotone k i hi).map_min, evr_eq_self_of_selfVis (hγ.mono hk) i]

section
variable {x γ : ExtOrd}

/-- A replacement strictly below an `N`-visible value comes from a value strictly below it. -/
theorem lt_of_evr_lt {N i} (hγ : SelfVis N γ)
    (h : extVisibilityReplace x N i < γ) : x < γ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rwa [extVisibilityReplace_bot] at h
  · rw [extVisibilityReplace_top] at h; exact absurd h not_top_lt
  · by_cases hfp : N ≤ finitePart a
    · rwa [extVisibilityReplace_of_le_finitePart hfp] at h
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)] at h
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · exact absurd h (not_lt_bot)
      · exact lt_top_iff_ne_top.mpr (ofOrd_ne_top _)
      · rw [selfVis_ofOrd_iff] at hγ
        rw [ofOrd_lt_ofOrd] at h
        apply ofOrd_lt_ofOrd.mpr
        have hl : limitPart a ≤ limitPart g := by
          have := limitPart_mono h.le
          rwa [limitPart_limitPart_add_nat] at this
        rcases hl.lt_or_eq with hlt | heq
        · have h1 := limitPart_add_nat_le_of_lt hlt (finitePart a)
          rw [limitPart_add_finitePart] at h1
          refine lt_of_le_of_ne (h1.trans (limitPart_le g)) fun heq => hlt.ne ?_
          rw [heq]
        · have h1 : a < limitPart a + (finitePart g : Ordinal.{0}) := by
            conv_lhs => rw [← limitPart_add_finitePart a]
            exact add_lt_add_right (Nat.cast_lt.mpr ((not_le.mp hfp).trans_le hγ)) _
          rwa [heq, limitPart_add_finitePart] at h1

/-- Above an `N`-visible value, every replacement at grade `N` stays above it. -/
theorem le_evr_of_le {N} (hγ : SelfVis N γ) (hx : γ ≤ x) R :
    γ ≤ extVisibilityReplace x N R := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]; exact hx
  · rw [extVisibilityReplace_top]; exact le_top
  · by_cases hfp : N ≤ finitePart a
    · rwa [extVisibilityReplace_of_le_finitePart hfp]
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)]
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · exact bot_le
      · exact absurd hx (not_le.mpr (lt_top_iff_ne_top.mpr (ofOrd_ne_top _)))
      · rw [selfVis_ofOrd_iff] at hγ
        rw [ofOrd_le_ofOrd] at hx
        apply ofOrd_le_ofOrd.mpr
        have hl : limitPart g ≤ limitPart a := limitPart_mono hx
        rcases hl.lt_or_eq with hlt | heq
        · exact (limitPart_add_nat_le_of_lt hlt (finitePart g)).trans' (by
            rw [limitPart_add_finitePart]) |>.trans le_self_add
        · exfalso
          have h1 : limitPart a + (finitePart g : Ordinal.{0}) ≤
              limitPart a + (finitePart a : Ordinal.{0}) := by
            rw [← heq, limitPart_add_finitePart]
            conv_rhs => rw [heq, limitPart_add_finitePart]
            exact hx
          have h2 : finitePart g ≤ finitePart a := Nat.cast_le.mp (le_of_add_le_add_left h1)
          exact hfp (hγ.trans h2)

/-- An `N`-visible value below a replacement at offset `R < N` is below the value itself. -/
theorem le_of_le_evr {N R} (hγ : SelfVis N γ) (hR : R < N)
    (h : γ ≤ extVisibilityReplace x N R) : γ ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rwa [extVisibilityReplace_bot] at h
  · exact le_top
  · by_cases hfp : N ≤ finitePart a
    · rwa [extVisibilityReplace_of_le_finitePart hfp] at h
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)] at h
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · exact bot_le
      · exact absurd h (not_le.mpr (lt_top_iff_ne_top.mpr (ofOrd_ne_top _)))
      · rw [selfVis_ofOrd_iff] at hγ
        rw [ofOrd_le_ofOrd] at h
        apply ofOrd_le_ofOrd.mpr
        have hl : limitPart g ≤ limitPart a := by
          have := limitPart_mono h
          rwa [limitPart_limitPart_add_nat] at this
        rcases hl.lt_or_eq with hlt | heq
        · exact ((limitPart_add_nat_le_of_lt hlt (finitePart g)).trans' (by
            rw [limitPart_add_finitePart])).trans (limitPart_le a)
        · exfalso
          have h1 : limitPart g + (finitePart g : Ordinal.{0}) ≤
              limitPart g + (R : Ordinal.{0}) := by
            rw [limitPart_add_finitePart, heq]; exact h
          have h2 : finitePart g ≤ R := Nat.cast_le.mp (le_of_add_le_add_left h1)
          omega

end

/-! ## A whole labelling from a section below the top index -/

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- A lawful section below an index dominating every cell is a lawful whole labelling. -/
theorem RespectsSemantics.of_below_top {top : Finset ι × ℕ} (htop : ∀ d, GradedLe (D.cell d) top)
    {r : D.below top → ExtOrd} (hr : RespectsSemanticsBelow sem top r) :
    RespectsSemantics sem (fun d => r ⟨d, htop d⟩) where
  orderly d := hr.orderly ⟨d, htop d⟩
  locality Sig := hr.locality ⟨Sig, htop Sig⟩
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := hr.availability ⟨Sig, htop Sig⟩ ⟨Xi₀, htop Xi₀⟩ hs hg
    exact ⟨Xi.1, hc, hle⟩

/-- **Same-bottom-pattern transport** (the reviewer's helper, notes3): a bounded
replacement-commuting image of a lawful section having the bottom flags of a lawful section is
lawful.  No bottom reflection of the scalar map is needed. -/
theorem map_respects_of_same_bottom_pattern {BJ} {r q}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q) {K}
    {ν} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : BoundedMap K ν)
    (hpattern : ∀ d, ν (r d) = ⊥ ↔ q d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) :=
  (map_respects_iff_rowBlockBottom hr hK hν).mpr
    (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hq) hpattern)

/-! ## Requests, correctness, the distinguished class -/

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}

/-- **The request data**: the old cap `C` of grade `N`, the marker offset `R < N`, the
requested-bottom cells `Z`, the exactly requested cells `F` with their old references `ρ` and
offsets `off`, the high cells `T`, and the old marker `a`.  References and marker lie below
the cap. -/
structure Requests (DA : CellScheme A) (DQ : CellScheme Q) where
  /-- The old cap. -/
  C : Cell DA
  /-- The threshold, the cap's grade. -/
  N : ℕ
  /-- The marker offset (plan 21); the block-floor version is `R = 0`. -/
  R : ℕ
  R_lt_N : R < N
  /-- Requested bottom. -/
  Z : Set (Cell DQ)
  /-- Exactly requested proper values. -/
  F : Set (Cell DQ)
  /-- High values, read by a cutoff. -/
  T : Set (Cell DQ)
  /-- The old reference of an exact request, below the cap. -/
  ρ : Cell DQ → DA.below (DA.cell C)
  /-- Its offset. -/
  off : Cell DQ → ℕ
  /-- The old marker, below the cap. -/
  a : DA.below (DA.cell C)

namespace Requests

variable {DA : CellScheme A} {DQ : CellScheme Q} (r : Requests DA DQ)

/-- The cap as a cell of its own lower domain. -/
def capCell : DA.below (DA.cell r.C) := ⟨r.C, GradedLe.refl _⟩

/-- The restriction of an old labelling to the cap's lower domain. -/
def sec (u : Cell DA → ExtOrd) (d : DA.below (DA.cell r.C)) : ExtOrd := u d.1

section
variable (u : Cell DA → ExtOrd)

@[simp] theorem sec_apply (d : DA.below (DA.cell r.C)) :
    r.sec u d = u d.1 := rfl

@[simp] theorem sec_capCell  : r.sec u r.capCell = u r.C := rfl

end

section
variable (s : DA.below (DA.cell r.C) → ExtOrd)

/-- `t_f(s)`: the capped replacement of the reference, for a section `s` below the cap. -/
noncomputable def tOf (f : Cell DQ) : ExtOrd :=
  min (extVisibilityReplace (s (r.ρ f)) r.N (r.off f)) (s r.capCell)

/-- `d(s)`: the capped offset-`R` replacement of the marker. -/
noncomputable def dOf  : ExtOrd :=
  min (extVisibilityReplace (s r.a) r.N r.R) (s r.capCell)

/-- **The target relations** between an old section `s` below the cap and a candidate
labelling `v`. -/
def Correct (v : Cell DQ → ExtOrd) : Prop :=
  (∀ z ∈ r.Z, min (v z) (s r.capCell) = ⊥) ∧
    (∀ f ∈ r.F, min (v f) (s r.capCell) = r.tOf s f) ∧
    ∀ y ∈ r.T, r.dOf s ≤ min (v y) (s r.capCell)

end

end Requests

/-- The distinguished old bottom-pattern class, tested on a lower domain only. -/
def InClass {DA : CellScheme A} {BJ} (ZA : Set (DA.below BJ))
    (u : Cell DA → ExtOrd) : Prop :=
  ∀ d : DA.below BJ, u d.1 = ⊥ ↔ d ∈ ZA

/-! ## The relative data -/

/-- **The relative data**: the old scheme with a full-scope grade-`N` cap (cells above the
cap are allowed and untouched), the cleaned donor on the cap's lower domain, the candidate
scheme with its root face, its bountifulness, and the reference template. -/
structure RelativeData (DA : CellScheme A) (semA : Semantics DA) (DQ : CellScheme Q)
    (semQ : Semantics DQ) where
  /-- The requests. -/
  req : Requests DA DQ
  /-- The cap has grade `N`. -/
  grade_C : DA.grade req.C = req.N
  /-- The distinguished bottom pattern, on the lower domain below the cap. -/
  ZA : Set (DA.below (DA.cell req.C))
  C_notin : req.capCell ∉ ZA
  a_notin : req.a ∉ ZA
  ρ_notin : ∀ f ∈ req.F, req.ρ f ∉ ZA
  off_lt : ∀ f ∈ req.F, req.off f ≤ req.N
  /-- The cleaned donor: bottom exactly on the class, the cap's row elsewhere. -/
  e : DA.below (DA.cell req.C) → ExtOrd
  e_bot : ∀ d, e d = ⊥ ↔ d ∈ ZA
  e_eq : ∀ d, d ∉ ZA → e d = semA.E req.C d
  /-- The candidate's root and top indices. -/
  root : Finset ιQ × ℕ
  top : Finset ιQ × ℕ
  root_mem : root ∈ Plan.gradedPlan DQ.plan
  top_mem : top ∈ Plan.gradedPlan DQ.plan
  root_le : GradedLe root top
  root_ne : root ≠ top
  below_top : ∀ d, GradedLe (DQ.cell d) top
  top_le_N : top.2 ≤ req.N
  /-- Root cells are old cells below the cap, and lawful old sections below the cap pull back
  to lawful root sections. -/
  κ : DQ.below root → DA.below (DA.cell req.C)
  hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd, RespectsSemanticsBelow semA (DA.cell req.C) s →
    RespectsSemanticsBelow semQ root (fun d => s (κ d))
  /-- The candidate is bountiful. -/
  bountiful : semQ.IsBountiful
  /-- Every candidate cell is requested or a root cell. -/
  cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d
  /-- The reference template: lawful, the donor on the root, correct against the donor. -/
  V : Cell DQ → ExtOrd
  V_respects : RespectsSemantics semQ V
  V_root : ∀ r : DQ.below root, V r.1 = e (κ r)
  V_correct : req.Correct e V
  /-- The frame inequalities, when high values are requested. -/
  frame : req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e

namespace RelativeData

variable {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

/-- An **allowed** pair: lawful on both faces, agreeing on the root, correct in the class. -/
def Allowed (u : Cell DA → ExtOrd) (v : Cell DQ → ExtOrd) : Prop :=
  RespectsSemantics semA u ∧ RespectsSemantics semQ v ∧
    (∀ r : DQ.below X.root, v r.1 = u (X.κ r).1) ∧
    (InClass X.ZA u → X.req.Correct (X.req.sec u) v)

theorem grade_le d : DQ.grade d ≤ X.req.N :=
  (X.below_top d).2.trans X.top_le_N

/-- Lawful old labellings pull back to lawful root sections. -/
theorem hroot' u (hu : RespectsSemantics semA u) :
    RespectsSemanticsBelow semQ X.root (fun d => u (X.κ d).1) :=
  X.hroot (fun d => u d.1) (hu.toBelow _)

/-- In the class the cap is nonbottom. -/
theorem cap_ne_bot {u : Cell DA → ExtOrd} (hcls : InClass X.ZA u) : u X.req.C ≠ ⊥ :=
  fun h => X.C_notin ((hcls X.req.capCell).mp h)

/-! ## The selector -/

section
variable {u' : Cell DA → ExtOrd}

/-- **The root lift**: candidate bountifulness at the root–top pair installs a lawful old root
into a lawful candidate ambient at any `N`-visible cap, retaining the ambient's cap reading. -/
theorem lift_root (hu' : RespectsSemantics semA u')
    {w} (hw : RespectsSemantics semQ w) {γ}
    (hγ : SelfVis X.req.N γ)
    (hagr : ∀ r, min (w r.1) γ = min (u' (X.κ r).1) γ) :
    ∃ v', RespectsSemantics semQ v' ∧
      (∀ r, v' r.1 = u' (X.κ r).1) ∧ ∀ d, min (v' d) γ = min (w d) γ := by
  obtain ⟨q', hq', hcap, hface⟩ := X.bountiful X.root X.top X.root_mem X.top_mem X.root_le
    X.root_ne (fun d => u' (X.κ d).1) (fun d => w d.1) γ (X.hroot' u' hu') (hw.toBelow X.top)
    (hγ.mono X.top_le_N) (fun d => hagr d)
  refine ⟨fun d => q' ⟨d, X.below_top d⟩, RespectsSemantics.of_below_top X.below_top hq', ?_, ?_⟩
  · aesop
  · grind

/-- **The capped decoder** of a lawful old labelling at the cap: the exact capped shifter of its
locality at the cap's row, capped at the cap's label — a bounded map reading the donor as the
capped labelling on the distinguished class. -/
theorem decoder (hu' : RespectsSemantics semA u')
    (hcls : InClass X.ZA u') :
    ∃ θ : ExtOrd → ExtOrd, BoundedMap X.req.N θ ∧ (∀ x, θ x ≤ u' X.req.C) ∧
      ∀ d, θ (X.e d) = min (X.req.sec u' d) (u' X.req.C) := by
  have hvis : SelfVis (DA.grade X.req.C) (u' X.req.C) := (hu'.orderly X.req.C).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := DA.below (DA.cell X.req.C)) (grade := fun d => DA.grade d.1) (p := fun d => u' d.1)
    (c := ⟨X.req.C, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hu'.locality X.req.C)
  have hvisN : SelfVis X.req.N (u' X.req.C) := by rwa [X.grade_C] at hvis
  refine ⟨fun x => min (τ x) (u' X.req.C), ⟨?_, ?_, ?_⟩, fun x => min_le_right _ _, ?_⟩
  · simp only [hbot]; exact min_eq_left bot_le
  · intro x y h; exact min_le_min_right _ (hmono h)
  · intro x k i hk hi
    rw [hcomm x k i (by rw [X.grade_C]; exact hk) hi, evr_min_of_selfVis hvisN hk hi]
  · intro d
    by_cases hd : d ∈ X.ZA
    · have h1 : X.e d = ⊥ := (X.e_bot d).mpr hd
      have h2 : u' d.1 = ⊥ := (hcls d).mpr hd
      simp only [h1, h2, hbot, Requests.sec_apply]
    · rw [X.e_eq d hd]
      simp_all
      rw [hread d, min_assoc, min_self]

end

end RelativeData

end VaughtConjecture.Knight
