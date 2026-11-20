/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLift
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.PositiveNormalization
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.BlockCode

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

section Cleaning

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- The cleaning map of a reading witness: bottom where the witness reads bottom. -/
noncomputable def cleaner (σ : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd :=
  if σ x = ⊥ then ⊥ else x

theorem cleaner_of_eq {σ : ExtOrd → ExtOrd} {x : ExtOrd} (h : σ x = ⊥) : cleaner σ x = ⊥ :=
  ite_eq_left h

theorem cleaner_of_ne {σ : ExtOrd → ExtOrd} {x : ExtOrd} (h : σ x ≠ ⊥) : cleaner σ x = x :=
  ite_eq_right h

theorem cleaner_eq_bot_iff {σ : ExtOrd → ExtOrd} (hσ : σ ⊥ = ⊥) (x : ExtOrd) :
    cleaner σ x = ⊥ ↔ σ x = ⊥ := by grind [cleaner_of_eq, cleaner_of_ne]

/-- The cleaning map of a bounded map is a bounded map. -/
theorem boundedMap_cleaner {K : ℕ} {σ : ExtOrd → ExtOrd} (hσ : BoundedMap K σ) :
    BoundedMap K (cleaner σ) where
  bot := cleaner_of_eq hσ.bot
  mono x y hxy := by
    by_cases hy : σ y = ⊥
    · have hx : σ x = ⊥ := le_bot_iff.mp (hy ▸ hσ.mono hxy)
      rw [cleaner_of_eq hx, cleaner_of_eq hy]
    · rw [cleaner_of_ne hy]
      by_cases hx : σ x = ⊥
      · rw [cleaner_of_eq hx]; simp
      · rw [cleaner_of_ne hx]; assumption
  comm x k i hk hi := by
    have h := hσ.comm x k i hk hi
    by_cases hx : σ x = ⊥
    · simp_all [extVisibilityReplace, cleaner_of_eq]
    · have h' : σ (extVisibilityReplace x k i) ≠ ⊥ := by
        rw [h]; exact extVisibilityReplace_ne_bot hx k i
      rw [cleaner_of_ne hx, cleaner_of_ne h']

/-- Cleaning only needs the reading's bottom pattern, including on long source rows. -/
theorem cleaned_respects_of_bottom_agreement {BJ : Finset ι × ℕ} {r u : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hu : RespectsSemanticsBelow sem BJ u) {K : ℕ}
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) {σ : ExtOrd → ExtOrd} (hσ : BoundedMap K σ)
    (hbot : ∀ d, σ (r d) = ⊥ ↔ u d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => if u d = ⊥ then ⊥ else r d) := by
  have h := map_respects_of_same_bottom_pattern hr hu hK (boundedMap_cleaner hσ)
    (fun d => (cleaner_eq_bot_iff hσ.bot _).trans (hbot d))
  have e : (fun d => cleaner σ (r d)) = fun d => if u d = ⊥ then ⊥ else r d := by
    funext d
    simp [cleaner, hbot d]
  simp_all

end Cleaning

section Template

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- Assemble the requests and a lawful cleaned template on the literal root. -/
noncomputable def mkRelativeData (req : Requests DA DQ) (grade_C : DA.grade req.C = req.N)
    {u₀ : Cell DA → ExtOrd} (hC : u₀ req.C ≠ ⊥)
    (a_ne : u₀ req.a.1 ≠ ⊥) (ρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥)
    (off_lt : ∀ f ∈ req.F, req.off f ≤ req.N)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (e_bot : ∀ d, e d = ⊥ ↔ u₀ d.1 = ⊥)
    (e_eq : ∀ d, u₀ d.1 ≠ ⊥ → e d = semA.E req.C d) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_N : top.2 ≤ req.N)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (V : Cell DQ → ExtOrd) (V_respects : RespectsSemantics semQ V)
    (V_root : ∀ r : DQ.below root, V r.1 = e (κ r))
    (V_correct : req.Correct e V)
    (frame : req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) :
    RelativeData DA semA DQ semQ where
  req := req
  grade_C := grade_C
  ZA := {d | u₀ d.1 = ⊥}
  C_notin := hC
  a_notin := a_ne
  ρ_notin := ρ_ne
  off_lt := off_lt
  e := e
  e_bot := e_bot
  e_eq := e_eq
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

/-- Capped template repair needs encoding commutation only through the donor's top grade. -/
theorem template_of_encoding_at_grade (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (ha_ne : e req.a ≠ ⊥)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap top.2 enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis top.2 (extVisibilityReplace (e req.a) req.N req.R))
    (hroot_cap : ∀ r, min (enc (P r.1)) (extVisibilityReplace (e req.a) req.N req.R) =
      min (e (κ r)) (extVisibilityReplace (e req.a) req.N req.R))
    (hZ : ∀ z ∈ req.Z, P z = ⊥)
    (hF : ∀ f ∈ req.F, enc (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f))
    (hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R)
    (hT : ∀ y ∈ req.T, enc (P y) = extVisibilityReplace (e req.a) req.N req.R) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ r, V r.1 = e (κ r)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) ∧
      (∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f)) ∧
      (∀ y ∈ req.T, extVisibilityReplace (e req.a) req.N req.R ≤ V y) ∧
      ∀ z ∈ req.Z, V z = ⊥ := by
  set h := extVisibilityReplace (e req.a) req.N req.R with hh
  have hne : h ≠ ⊥ := fun h0 => ha_ne ((evr_eq_bot_iff _ _).mp h0)
  -- the encoded candidate is lawful
  have hV0 : RespectsSemantics semQ (fun d => enc (P d)) :=
    RespectsSemantics.of_below_top below_top
      (map_respects_of_same_bottom_pattern (hP.toBelow top) (hP.toBelow top)
        (fun d => d.2.2) henc
        (fun d => ⟨hbotP d.1, fun h => by rw [h, henc.bot]⟩))
  -- restore the literal donor root at cap `h`
  obtain ⟨q', hq', hcap, hface⟩ := bountiful root top root_mem top_mem root_le root_ne
    (fun d => e (κ d)) (fun d => enc (P d.1)) h (hroot e he) (hV0.toBelow top)
    hvis (fun d => hroot_cap d)
  set V : Cell DQ → ExtOrd := fun d => q' ⟨d, below_top d⟩ with hVdef
  have hVr : RespectsSemantics semQ V := RespectsSemantics.of_below_top below_top hq'
  have hVcap : ∀ d, min (V d) h = min (enc (P d)) h := by tauto
  have hVF : ∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    grind
  have hVT : ∀ y ∈ req.T, h ≤ V y := by
    grind
  have hVZ : ∀ z ∈ req.Z, V z = ⊥ := by
    intro z hz
    have h1 := hVcap z
    rw [hZ z hz, henc.bot, min_eq_left bot_le] at h1
    grind
  refine ⟨V, hVr, fun r => hface r, ⟨?_, ?_, ?_⟩, ?_, hVF, hVT, hVZ⟩
  · grind
  · tauto
  · intro y hy
    exact min_le_min_right _ (hVT y hy)
  · intro _ f hf
    exact min_le_min_right _ (hFlt f hf).le

end Template

end VaughtConjecture.Knight
