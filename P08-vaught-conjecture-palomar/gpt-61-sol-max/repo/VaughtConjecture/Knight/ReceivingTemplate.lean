/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.RelativeLift
import VaughtConjecture.Knight.CountedRecoding
import VaughtConjecture.Knight.CappedLocalityRecoding
import VaughtConjecture.Knight.Semantics
import VaughtConjecture.Knight.Reduction
import VaughtConjecture.Knight.VisibilityAlgebra
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import VaughtConjecture.Knight.FullScopeZeroExtension
import VaughtConjecture.Knight.RowCorrectness
import VaughtConjecture.Knight.RowReadback
import VaughtConjecture.Knight.PositiveNormalization
import VaughtConjecture.Knight.CoupledGradeOne
import VaughtConjecture.Knight.SemScheme
import VaughtConjecture.Knight.BlockCode

/-! # The receiving template: donor cleaning and the encoded candidate

The reviewer's notes7 (`mixed_proper_top_charts.md` §6, 2026-09-19), at the level of the
finite schemes.  Three steps, each a theorem:

* **Donor cleaning** (`cleaned_respects`, `exists_cleanedDonor`): the cap's row with the actual
  labelling's bottom pattern is lawful on the cap's lower domain.  The cleaning map
  `ν x = ⊥` if the reading witness kills `x`, `x` otherwise, is a bounded map, and the
  cleaned row has the bottom pattern of the actual (lawful) labelling; so
  `map_respects_of_same_bottom_pattern` applies.  No semantic row is changed.
* **The template from an encoding** (`template_of_encoding`): a bounded map `enc` through the
  candidate's grades, reflecting bottom on the candidate's values, sending the root labels to
  the donor's root sources, every exact request to its reference strip at its offset, every
  high request to the marker's offset-`R` replacement, and bottom to bottom, makes
  `enc ∘ P` a lawful template with literal donor root, correct against the donor, and
  satisfying the frame inequalities.  A block code (`BlockCode.code`) is such an `enc`.
* **The capped variant** (`template_of_encoding_capped`): root agreement is required only
  below `h = R_{N,R}(e a)`; the candidate's bountifulness at the root–top pair at cap `h`
  restores the literal donor root.  This is what top-labelled root cells need: their sources
  dominate `h` while the encoding sends `⊤` to `h`.
* **The relative data** (`mkRelativeData`): the assembled `RelativeData`, with the donor
  *constructed* from the actual labelling and the cap's row, and the template supplied by
  the two theorems above.  `Knight/ReceivingContext.lean` discharges every encoding
  hypothesis from an actual receiving context.

**The root alignment hypothesis.**  The template's root must be the donor's root
*sources* `E_C(κ r)`, while the encoding acts on the root *labels* `P(κ r) = u₀(κ r)`.  The
note asserts "its root equals `e|B` capped at `h`"; that holds only when every root cell's
source lies on the strip chosen for its label's block at its own offset
(`hroot_enc`).  It is not automatic: the reading witness of the cap's row may merge two
source strips into one label block, so two root cells with labels in one block can have
sources on different strips, and then no scalar encoding of the labels recovers both sources
(`TemplateRegression.no_scalar_root` in `Knight/TemplateRegression.lean`).  The hypothesis is
therefore explicit, and it is the first clause the model-side construction has to discharge.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open AmalgamationPlan  Value  SharpWitnessComposition

/-! ## Donor cleaning -/

section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- The cleaning map of a reading witness: bottom where the witness reads bottom. -/
noncomputable def cleaner (σ : LabelMap) (x : ExtOrd) :=
  if σ x = ⊥ then ⊥ else x

theorem cleaner_of_eq {σ} {x} (h : σ x = ⊥) : cleaner σ x = ⊥ :=
  ite_eq_left h

theorem cleaner_of_ne {σ} {x} (h : σ x ≠ ⊥) : cleaner σ x = x :=
  ite_eq_right h

theorem cleaner_eq_bot_iff {σ} (hσ : σ ⊥ = ⊥) x :
    cleaner σ x = ⊥ ↔ σ x = ⊥ := by grind only [cleaner_of_eq, cleaner_of_ne]

/-- The cleaning map of a bounded map is a bounded map. -/
theorem boundedMap_cleaner {K} {σ} (hσ : BoundedMap K σ) :
    BoundedMap K (cleaner σ) where
  bot := cleaner_of_eq hσ.bot
  mono x y hxy := by
    by_cases hy : σ y = ⊥
    · have hx : σ x = ⊥ := le_bot_iff.mp (hy ▸ hσ.mono hxy)
      rw [cleaner_of_eq hx, cleaner_of_eq hy]
    · rw [cleaner_of_ne hy]
      by_cases hx : σ x = ⊥
      · rw [cleaner_of_eq hx]; exact bot_le
      · rw [cleaner_of_ne hx]; exact hxy
  comm x k i hk hi := by
    have h := hσ.comm x k i hk hi
    by_cases hx : σ x = ⊥
    · have h' : σ (extVisibilityReplace x k i) = ⊥ := by rw [h, hx, extVisibilityReplace_bot]
      rw [cleaner_of_eq hx, cleaner_of_eq h', extVisibilityReplace_bot]
    · have h' : σ (extVisibilityReplace x k i) ≠ ⊥ := by
        rw [h]; exact fun hb => hx ((evr_eq_bot_iff).mp hb)
      rw [cleaner_of_ne hx, cleaner_of_ne h']

/-- Cleaning only needs the reading's bottom pattern, including on long source rows. -/
def cleaned_respects_of_bottom_agreement {BJ} {r u}
    (hr : RespectsSemanticsBelow sem BJ r) (hu : RespectsSemanticsBelow sem BJ u) {K}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) {σ} (hσ : BoundedMap K σ)
    (hbot : ∀ d, σ (r d) = ⊥ ↔ u d = ⊥) := by
  have h := map_respects_of_same_bottom_pattern hr hu hK (boundedMap_cleaner hσ)
    (fun d => (cleaner_eq_bot_iff hσ.bot _).trans (hbot d))
  have e : (fun d => cleaner σ (r d)) = fun d => if u d = ⊥ then ⊥ else r d := by
    simp_all [cleaner]
  rwa [e] at h

end

/-! ## The cleaned donor at a cap -/


/-! ## The template from an encoding -/

section

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- **The assembled relative data**: the cleaned donor is *constructed* from the actual
labelling and the cap's row; the template and its four properties are supplied by
`template_of_encoding` or `template_of_encoding_capped`. -/
noncomputable def mkRelativeData (req : Requests DA DQ) (grade_C : DA.grade req.C = req.N)
    (hrow : Semantics.RowLawful semA req.C (semA.E req.C))
    {u₀ : CellLabels DA} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (a_ne : u₀ req.a.1 ≠ ⊥) (ρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥)
    (off_lt : ∀ f ∈ req.F, req.off f ≤ req.N) {root top : GradedIndex ιQ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_N : top.2 ≤ req.N)
    (κ : DQ.below root → DA.belowCell req.C)
    (hroot : ∀ s ,
      Semantics.RowLawful semA req.C s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (V : CellLabels DQ) (V_respects : RespectsSemantics semQ V)
    (V_root : ∀ r , V r.1 = if u₀ (κ r).1 = ⊥ then ⊥ else semA.E req.C (κ r))
    (V_correct : req.Correct (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) V)
    (frame : req.T.Nonempty → ∀ f ∈ req.F,
      req.tOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) f ≤
        req.dOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d)) :
    RelativeData DA semA DQ semQ := ⟨req,
grade_C,
{d | u₀ d.1 = ⊥},
by
    change ¬ u₀ req.C = ⊥
    rw [hC]; exact top_ne_bot,
a_ne,
ρ_ne,
off_lt,
fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d,
fun d => by
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = ⊥ ↔ u₀ d.1 = ⊥
    by_cases h : u₀ d.1 = ⊥
    · simp only [h, ite_true]
    · simp only [h, ite_false, iff_false]
      intro hE
      
      obtain ⟨g, σ, _, _, hbot, _, _, hread⟩ := hu₀.locality req.C
      have hd := hread d
      change min (u₀ d.1) (u₀ req.C) = min (σ (semA.E req.C d)) (g (DA.grade d.1)) at hd
      rw [hC, min_top_right, hE, hbot, min_eq_left bot_le] at hd
      exact h hd,
fun d hd => by
    grind,
root,
top,
root_mem,
top_mem,
root_le,
root_ne,
below_top,
top_le_N,
κ,
hroot,
bountiful,
cover,
V,
V_respects,
V_root,
V_correct,
frame⟩

/-- Capped template repair needs encoding commutation only through the donor's top grade. -/
theorem template_of_encoding_at_grade (req : Requests DA DQ)
    (e : BelowLabels DA (DA.cell req.C))
    (he : Semantics.RowLawful semA req.C e) (ha_ne : e req.a ≠ ⊥)
    {P : CellLabels DQ} (hP : RespectsSemantics semQ P) {root top : GradedIndex ιQ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top)
    (κ : DQ.below root → DA.belowCell req.C)
    (hroot : ∀ s ,
      Semantics.RowLawful semA req.C s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : LabelMap} (henc : BoundedMap top.2 enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis top.2 (extVisibilityReplace (e req.a) req.N req.R))
    (hroot_cap : ∀ r, min (enc (P r.1)) (extVisibilityReplace (e req.a) req.N req.R) =
      min (e (κ r)) (extVisibilityReplace (e req.a) req.N req.R))
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f))
    (hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R)
    (hT : ∀ y ∈ req.T, enc (P y) = extVisibilityReplace (e req.a) req.N req.R) :
    ∃ V , RespectsSemantics semQ V ∧ (∀ r, V r.1 = e (κ r)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f)) ∧
      (∀ y ∈ req.T, extVisibilityReplace (e req.a) req.N req.R ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ := by
  set h := extVisibilityReplace (e req.a) req.N req.R with hh
  have hne : h ≠ ⊥ := fun h0 => ha_ne ((evr_eq_bot_iff).mp h0)
  -- the encoded candidate is lawful
  have hV0  :=
    RespectsSemantics.of_below_top below_top
      (map_respects_of_same_bottom_pattern (hP.toBelow top) (hP.toBelow top)
        (fun d => d.2.2) henc
        (fun d => ⟨hbotP d.1, fun h => by rw [h, henc.bot]⟩))
  -- restore the literal donor root at cap `h`
  obtain ⟨q', hq', hcap, hface⟩ := bountiful root top root_mem top_mem root_le root_ne
    (fun d => e (κ d)) (fun d => enc (P d.1)) h (hroot e he) (hV0.toBelow top)
    hvis (fun d => hroot_cap d)
  set V : CellLabels DQ := fun d => q' ⟨d, below_top d⟩ with hVdef
  have hVr  := RespectsSemantics.of_below_top below_top hq'
  have hVcap  := fun d => hcap ⟨d, below_top d⟩
  have hVF : ∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    grind
  have hVT : ∀ y ∈ req.T, h ≤ V y := by
    grind
  have hVZ : ∀ z ∈ req.Z, V z = ⊥ := by
    intro z hz
    have h1 := hVcap z
    rw [hZ z hz, henc.bot, min_eq_left bot_le] at h1
    rcases min_eq_bot.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hne
  refine ⟨V, hVr, fun r => hface r, ⟨?_, ?_, ?_⟩, ?_, hVF, hVT, hVZ⟩
  · simp_all
  · intro f hf
    rw [hVF f hf]
    rfl
  · intro y hy
    exact min_le_min_right _ (hVT y hy)
  · intro _ f hf
    exact min_le_min_right _ (hFlt f hf).le

/-- **The template from an encoding, with root agreement below the top code only.**  When
the encoded candidate agrees with the donor's root only below `h = R_{N,R}(e a)` (the case of
top-labelled root cells, whose sources dominate `h`), the candidate's bountifulness at the
root–top pair at cap `h` restores the literal donor root while retaining every `h`-reading;
the exact requests must then sit strictly below `h`. -/
def template_of_encoding_capped (req : Requests DA DQ)
    (e : BelowLabels DA (DA.cell req.C))
    (he : Semantics.RowLawful semA req.C e) (ha_ne : e req.a ≠ ⊥)
    {P : CellLabels DQ} (hP : RespectsSemantics semQ P) {root top : GradedIndex ιQ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → DA.belowCell req.C)
    (hroot : ∀ s ,
      Semantics.RowLawful semA req.C s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : LabelMap} (henc : BoundedMap req.R enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis req.R (extVisibilityReplace (e req.a) req.N req.R))
    (hroot_cap : ∀ r, min (enc (P r.1)) (extVisibilityReplace (e req.a) req.N req.R) =
      min (e (κ r)) (extVisibilityReplace (e req.a) req.N req.R))
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f))
    (hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R)
    (hT : ∀ y ∈ req.T, enc (P y) = extVisibilityReplace (e req.a) req.N req.R) := template_of_encoding_at_grade req e he ha_ne hP root_mem top_mem root_le root_ne
    below_top κ hroot bountiful
    ⟨henc.bot, henc.mono, fun x k i hk hi => henc.comm x k i (hk.trans top_le_R) hi⟩
    hbotP (hvis.mono top_le_R) hroot_cap hZ hF hFlt hT


