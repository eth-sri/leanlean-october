/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLift
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.PositiveNormalization
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.BlockCode

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

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Donor cleaning -/

section Cleaning

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

def cleaner (σ : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd :=
  if σ x = ⊥ then ⊥ else x

theorem cleaned_respects_of_bottom_agreement {BJ : Finset ι × ℕ} {r u : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hu : RespectsSemanticsBelow sem BJ u) {K : ℕ}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) {σ : ExtOrd → ExtOrd} (hσ : BoundedMap K σ)
    (hbot : ∀ d, σ (r d) = ⊥ ↔ u d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => if u d = ⊥ then ⊥ else r d) := by
  have hc : BoundedMap K (cleaner σ) := {
    bot := ite_eq_left hσ.bot
    mono := fun x y hxy => by
      by_cases hy : σ y = ⊥
      · have hx : σ x = ⊥ := le_bot_iff.mp (hy ▸ hσ.mono hxy)
        rw [cleaner, cleaner, ite_eq_left hx, ite_eq_left hy]
      · rw [cleaner, cleaner, ite_eq_right hy]; split_ifs <;> [exact bot_le; exact hxy]
    comm := fun x k i hk hi => by
      have h := hσ.comm x k i hk hi
      by_cases hx : σ x = ⊥
      · have h' : σ (extVisibilityReplace x k i) = ⊥ := by rw [h, hx, extVisibilityReplace_bot]
        rw [cleaner, cleaner, ite_eq_left hx, ite_eq_left h', extVisibilityReplace_bot]
      · have h' : σ (extVisibilityReplace x k i) ≠ ⊥ := by
          rw [h]; exact fun hb => hx ((evr_eq_bot_iff _ _).mp hb)
        rw [cleaner, cleaner, ite_eq_right hx, ite_eq_right h'] }
  have h := map_respects_of_same_bottom_pattern hr hu hK hc fun d => by
    dsimp only [cleaner]
    by_cases hs : σ (r d) = ⊥
    · rw [ite_eq_left hs]; exact ⟨fun _ => (hbot d).mp hs, fun _ => rfl⟩
    · rw [ite_eq_right hs]
      exact ⟨fun hx => absurd (hx ▸ hσ.bot) hs, fun hu0 => absurd ((hbot d).mpr hu0) hs⟩
  simpa only [cleaner, hbot] using h

end Cleaning

section Template

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}
  (req : Requests DA DQ)

local notation "BelC" => DA.below (DA.cell req.C)
local notation "GPlan" => Plan.gradedPlan DQ.plan

def mkRelativeData (grade_C : DA.grade req.C = req.N)
    (_hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (a_ne : u₀ req.a.1 ≠ ⊥) (ρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥)
    (off_lt : ∀ f ∈ req.F, req.off f ≤ req.N) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ GPlan) (top_mem : top ∈ GPlan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_N : top.2 ≤ req.N)
    (κ : DQ.below root → BelC)
    (hroot : ∀ s : BelC → ExtOrd, RespectsSemanticsBelow semA (DA.cell req.C) s →
      RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (V : Cell DQ → ExtOrd) (V_respects : RespectsSemantics semQ V)
    (V_root : ∀ r : DQ.below root, V r.1 = if u₀ (κ r).1 = ⊥ then ⊥ else semA.E req.C (κ r))
    (V_correct : req.Correct (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) V)
    (frame : req.T.Nonempty → ∀ f ∈ req.F,
      req.tOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) f ≤
        req.dOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d)) :
    RelativeData DA semA DQ semQ where
  req := req
  grade_C := grade_C
  ZA := {d | u₀ d.1 = ⊥}
  C_notin := by change ¬ u₀ req.C = ⊥; rw [hC]; exact top_ne_bot
  a_notin := a_ne
  ρ_notin := ρ_ne
  off_lt := off_lt
  e := fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d
  e_bot := fun d => by
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = ⊥ ↔ u₀ d.1 = ⊥
    by_cases h : u₀ d.1 = ⊥
    · simp only [h, ite_true]
    · simp only [h, ite_false, iff_false]
      intro hE
      obtain ⟨g, σ, _, _, hbot, _, _, hread⟩ := hu₀.locality req.C
      have hd : min (u₀ d.1) (u₀ req.C) = min (σ (semA.E req.C d)) (g (DA.grade d.1)) := hread d
      rw [hC, min_top_right, hE, hbot, min_eq_left bot_le] at hd
      exact h hd
  e_eq := fun d hd => ite_eq_right hd
  root := root
  top := top
  root_mem := root_mem
  top_mem := top_mem
  root_le := root_le
  root_ne := root_ne
  below_top := below_top
  top_le_N := top_le_N
  κ := κ
  hroot := hroot
  bountiful := bountiful
  cover := cover
  V := V
  V_respects := V_respects
  V_root := V_root
  V_correct := V_correct
  frame := frame

variable (e : DA.below (DA.cell req.C) → ExtOrd)
local notation "evrA" => extVisibilityReplace (e req.a) req.N req.R
local notation "evrF" => fun f => extVisibilityReplace (e (req.ρ f)) req.N (req.off f)

theorem template_of_encoding_at_grade
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (ha_ne : e req.a ≠ ⊥)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ GPlan) (top_mem : top ∈ GPlan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top)
    (κ : DQ.below root → BelC)
    (hroot : ∀ s : BelC → ExtOrd, RespectsSemanticsBelow semA (DA.cell req.C) s →
      RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap top.2 enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis top.2 evrA)
    (hroot_cap : ∀ r, min (enc (P r.1)) evrA = min (e (κ r)) evrA)
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = evrF f)
    (hFlt : ∀ f ∈ req.F, evrF f < evrA)
    (hT : ∀ y ∈ req.T, enc (P y) = evrA) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ r, V r.1 = e (κ r)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = evrF f) ∧
      (∀ y ∈ req.T, evrA ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ := by
  set h := evrA
  have hne : h ≠ ⊥ := fun h0 => ha_ne ((evr_eq_bot_iff _ _).mp h0)
  have hV0 : RespectsSemantics semQ (fun d => enc (P d)) :=
    RespectsSemantics.of_below_top below_top
      (map_respects_of_same_bottom_pattern (hP.toBelow top) (hP.toBelow top)
        (fun d => d.2.2) henc (fun d => ⟨hbotP d.1, fun h => by rw [h, henc.bot]⟩))
  obtain ⟨q', hq', hcap, hface⟩ := bountiful root top root_mem top_mem root_le root_ne
    (fun d => e (κ d)) (fun d => enc (P d.1)) h (hroot e he) (hV0.toBelow top)
    hvis (fun d => hroot_cap d)
  let V (d : Cell DQ) : ExtOrd := q' ⟨d, below_top d⟩
  have hVcap (d : Cell DQ) : min (V d) h = min (enc (P d)) h := hcap ⟨d, below_top d⟩
  have hVF (f) (hf : f ∈ req.F) : V f = evrF f := by
    have h1 := hVcap f
    rw [hF f hf, min_eq_left (hFlt f hf).le] at h1
    exact eq_of_min_eq_of_lt' h1 (hFlt f hf)
  have hVT (y) (hy : y ∈ req.T) : h ≤ V y := by
    have h1 := hVcap y
    rw [hT y hy, min_self] at h1
    exact min_eq_right_iff.mp h1
  have hVZ (z) (hz : z ∈ req.Z) : V z = ⊥ := by
    have h1 := hVcap z
    rw [hZ z hz, henc.bot, min_eq_left bot_le] at h1
    exact (min_eq_bot.mp h1).resolve_right hne
  refine ⟨V, RespectsSemantics.of_below_top below_top hq', fun r => hface r,
    ⟨fun z hz => by rw [hVZ z hz]; exact min_eq_left bot_le,
     fun f hf => by rw [hVF f hf]; rfl,
     fun y hy => min_le_min_right _ (hVT y hy)⟩,
    fun _ f hf => min_le_min_right _ (hFlt f hf).le, hVF, hVT, hVZ⟩

theorem template_of_encoding_capped
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (ha_ne : e req.a ≠ ⊥)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ GPlan) (top_mem : top ∈ GPlan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → BelC)
    (hroot : ∀ s : BelC → ExtOrd, RespectsSemanticsBelow semA (DA.cell req.C) s →
      RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap req.R enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis req.R evrA)
    (hroot_cap : ∀ r, min (enc (P r.1)) evrA = min (e (κ r)) evrA)
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = evrF f)
    (hFlt : ∀ f ∈ req.F, evrF f < evrA)
    (hT : ∀ y ∈ req.T, enc (P y) = evrA) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ r, V r.1 = e (κ r)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = evrF f) ∧
      (∀ y ∈ req.T, evrA ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ :=
  template_of_encoding_at_grade req e he ha_ne hP root_mem top_mem root_le root_ne
    below_top κ hroot bountiful
    ⟨henc.bot, henc.mono, fun x k i hk hi => henc.comm x k i (hk.trans top_le_R) hi⟩
    hbotP (hvis.mono top_le_R) hroot_cap hZ hF hFlt hT
