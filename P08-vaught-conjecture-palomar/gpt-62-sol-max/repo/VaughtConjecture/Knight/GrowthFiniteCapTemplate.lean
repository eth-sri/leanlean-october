/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingContext

@[expose] public section

namespace VaughtConjecture.Knight.GrowthFiniteCapTemplate

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

noncomputable section

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

/-- Construct a lawful donor template from the finite-cap chart and its
actual block-reference readings. Neither an encoding nor root source
alignment nor a replacement donor is an input. -/
theorem exists_template (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e)
    (w : Cell DA → ExtOrd) (hebot : ∀ d, e d = ⊥ ↔ w d.1 = ⊥)
    {τ : ExtOrd → ExtOrd} (hτ : BoundedMap req.N τ)
    (hchart : ∀ d, τ (e d) = min (w d.1) (w req.C))
    {α : Ordinal.{0}} (hα : limitPart α = α) {i : ℕ} (hi : i < req.N)
    (ha : w req.a.1 = ofOrd (α + i))
    (hai : ofOrd (α + i) < w req.C)
    (hcut : ofOrd (α + req.R) < w req.C)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (hle : ∀ μ ∈ S, μ ≤ α)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C))
    (off : Ordinal.{0} → ℕ) (hoff : ∀ μ ∈ S, off μ < req.N)
    (href : ∀ μ ∈ S, τ (e (ref μ)) = ofOrd (μ + off μ))
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < req.R)
    (hproper : ∀ d, P d ≠ ⊤ → P d < ofOrd (α + req.R))
    {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_lt_R : top.2 < req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful) (hlit : ∀ d, P d.1 = w (κ d).1)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ d, V d.1 = e (κ d)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) := by
  have hma : τ (e req.a) = ofOrd (α + i) := by rw [hchart, ha, min_eq_left hai.le]
  obtain ⟨hsa, ho, hread⟩ := read_strip_block hτ hα hi hma
  let η := limitPart (ordOf (e req.a)) + (req.R : Ordinal.{0})
  have hheight : extVisibilityReplace (e req.a) req.N req.R = ofOrd η :=
    (congrArg (fun x => extVisibilityReplace x req.N req.R) hsa).trans
      (extVisibilityReplace_of_finitePart_lt (ho.trans_lt hi) _)
  have hheight_read : τ (ofOrd η) = ofOrd (α + req.R) := hread _ req.R_lt_N.le
  have hstrip (μ) (hμ : μ ∈ S) : limitPart (ordOf (e (ref μ))) + req.R ≤ η := by
    have horbit := (read_strip_block hτ (hS μ hμ) (hoff μ hμ) (href μ hμ)).2.2
    exact add_le_add_left (strip_le_of_affine hτ.mono (Nat.zero_lt_of_lt hi)
      horbit hread (hle μ hμ)) _
  have htop (d : DQ.below root) (hd : P d.1 = ⊤) : ofOrd η ≤ e (κ d) := by
    by_contra! hh
    have hm := hτ.mono hh.le
    rw [hchart, ← hlit, hd, min_top_left, hheight_read] at hm
    exact hcut.not_ge hm
  refine template_of_chart req e he hτ S hS ref (fun μ hμ => ⟨off μ, hoff μ hμ, href μ hμ⟩)
    req.R_lt_N.le hheight hstrip hP root_mem top_mem root_le root_ne below_top top_lt_R ?_
    κ hroot bountiful hblocks hZ hT hF (fun d h => (hebot _).mpr ((hlit d).symm.trans h)) htop ?_
  · rw [finitePart_limitPart_add_nat]; exact top_lt_R.le
  · intro d p h
    rw [hchart, ← hlit, min_eq_left ((hproper d.1 (h ▸ ofOrd_ne_top p)).trans hcut).le, h]

end

end VaughtConjecture.Knight.GrowthFiniteCapTemplate
