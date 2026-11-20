/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingTemplate

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

theorem ofOrd_ordOf {x : ExtOrd} (hb : x ≠ ⊥) (ht : x ≠ ⊤) : ofOrd (ordOf x) = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact absurd rfl hb
  · exact absurd rfl ht
  · rw [ordOf_ofOrd]

section Reading

variable {N : ℕ} {τ : ExtOrd → ExtOrd} (hτ : BoundedMap N τ)

include hτ in
/-- Below a source read to `⊤`: its offset-`R` replacement is a proper `R`-visible value, and
every strip of a proper reading with offset below `N`, plus `N`, lies at most there. -/
theorem strip_add_le_of_read_top {sa : Ordinal.{0}} (ha : τ (ofOrd sa) = ⊤) (R : ℕ)
    (hR : R < N) :
    ∃ h : Ordinal.{0}, extVisibilityReplace (ofOrd sa) N R = ofOrd h ∧ R ≤ finitePart h ∧
      ∀ s t : Ordinal.{0}, τ (ofOrd s) = ofOrd t → finitePart t < N →
        limitPart s + N ≤ h := by
  have hs {s t : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t) : s < sa :=
    ofOrd_lt_ofOrd.mp (hτ.mono.reflect_lt (by rw [h, ha]; exact ofOrd_lt_top _))
  by_cases hfa : finitePart sa < N
  · refine ⟨limitPart sa + R, extVisibilityReplace_of_finitePart_lt hfa R, by
      rw [finitePart_limitPart_add_nat], ?_⟩
    intro s t h ht
    have hr := (read_strip hτ h ht).2.2
    simp only [ordOf_ofOrd] at hr
    rcases (limitPart_mono (hs h).le).lt_or_eq with hlt | heq
    · exact (limitPart_add_nat_le_of_lt hlt N).trans le_self_add
    · have he := hτ.comm (ofOrd sa) N 0 le_rfl (Nat.zero_le _)
      rw [extVisibilityReplace_of_finitePart_lt hfa, ha, extVisibilityReplace_top, ← heq,
        hr 0 (Nat.zero_le _)] at he
      exact (ofOrd_ne_top _ he).elim
  · have hfa' := not_lt.mp hfa
    refine ⟨sa, extVisibilityReplace_of_le_finitePart hfa' R, hR.le.trans hfa', fun s t h _ => ?_⟩
    calc limitPart s + (N : Ordinal.{0}) ≤ limitPart sa + finitePart sa :=
          add_le_add (limitPart_mono (hs h).le) (Nat.cast_le.mpr hfa')
      _ = sa := decomposition sa

end Reading

section Context

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- The same block encoder and root repair work at the physical width or a
shorter width supported by the chart. The marker enters only via its replaced
height and the lower bound for shared top labels. -/
theorem template_of_chart (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e)
    {τ : ExtOrd → ExtOrd} (hτ : BoundedMap req.N τ)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C))
    (href : ∀ μ ∈ S, ∃ i < req.N, τ (e (ref μ)) = ofOrd (μ + i))
    {K : ℕ} (hKN : K ≤ req.N) {η : Ordinal.{0}}
    (hheight : extVisibilityReplace (e req.a) req.N req.R = ofOrd η)
    (hstrip : ∀ μ ∈ S, limitPart (ordOf (e (ref μ))) + K ≤ η)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top)
    (hK : top.2 < K) (hη : top.2 ≤ finitePart η)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s, RespectsSemanticsBelow semA (DA.cell req.C) s →
      RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < K)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p)
    (hrootZ : ∀ d, P d.1 = ⊥ → e (κ d) = ⊥)
    (hrootT : ∀ d, P d.1 = ⊤ → ofOrd η ≤ e (κ d))
    (hrootF : ∀ d p, P d.1 = ofOrd p → τ (e (κ d)) = ofOrd p) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ d, V d.1 = e (κ d)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) := by
  let src := fun μ => ordOf (e (ref μ))
  let strip := fun μ => limitPart (src μ)
  have hsrc (μ) (hμ : μ ∈ S) : e (ref μ) = ofOrd (src μ) ∧
      ∃ i, finitePart (src μ) < req.N ∧ finitePart (μ + (i : ℕ)) < req.N ∧
        τ (ofOrd (src μ)) = ofOrd (μ + i) := by
    obtain ⟨i, hi, hr⟩ := href μ hμ
    have hfp : finitePart (μ + (i : ℕ)) < req.N := by rwa [finitePart_add_nat_of_limit (hS μ hμ)]
    obtain ⟨hs, hf, -⟩ := read_strip hτ hr hfp
    exact ⟨hs, i, hf.trans_lt hfp, hfp, hs ▸ hr⟩
  have hlt (μ) (hμ : μ ∈ S) (ν) (hν : ν ∈ S) (h : μ < ν) : strip μ < strip ν := by
    obtain ⟨-, i, -, hi, hri⟩ := hsrc μ hμ
    obtain ⟨-, j, -, hj, hrj⟩ := hsrc ν hν
    exact strip_lt_of_read hτ hri hrj hi hj (by
      rwa [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit (hS ν hν)])
  let B := BlockCode.ofFinset K top.2 hK S strip η (fun _ _ => limitPart_idem _) hstrip hlt hη
  have htop : B.code ⊤ = ofOrd η := rfl
  have hcode {p : Ordinal.{0}} (hp : limitPart p ∈ S) (hf : finitePart p < K) :
      B.code (ofOrd p) = ofOrd (strip (limitPart p) + finitePart p) :=
    B.code_listed hp (BlockCode.ofFinset_Λ_listed _ _ _ _ _ _ _ _ _ _ hp) hf.le
  have hbotP (d) (hd : B.code (P d) = ⊥) : P d = ⊥ := by
    rcases ExtOrd.cases (P d) with h | h | ⟨p, h⟩
    · exact h
    · rw [h, htop] at hd; exact (ofOrd_ne_bot η hd).elim
    · obtain ⟨hp, hf⟩ := hblocks d p h
      rw [h, hcode hp hf] at hd
      exact (ofOrd_ne_bot _ hd).elim
  have hrootcap (d : DQ.below root) :
      min (B.code (P d.1)) (ofOrd η) = min (e (κ d)) (ofOrd η) := by
    rcases ExtOrd.cases (P d.1) with h | h | ⟨p, h⟩
    · rw [h, B.code_bot, hrootZ d h]
    · rw [h, htop, min_self, min_eq_right (hrootT d h)]
    · obtain ⟨hp, hf⟩ := hblocks d.1 p h
      obtain ⟨-, i, -, hi, hr⟩ := hsrc _ hp
      obtain ⟨hs, heq, -⟩ := read_strip hτ (hrootF d p h) (hf.trans_le hKN)
      have hread : τ (ofOrd (ordOf (e (κ d)))) = ofOrd p := hs ▸ hrootF d p h
      have hμ := limitPart_add_nat_of_limit (hS _ hp) i
      have hal : limitPart (ordOf (e (κ d))) = strip (limitPart p) :=
        le_antisymm (strip_le_of_read hτ hread hr (hf.trans_le hKN) hi (by rw [hμ]))
          (strip_le_of_read hτ hr hread hi (hf.trans_le hKN) (by rw [hμ]))
      rw [h, hcode hp hf, ← hal, ← heq, limitPart_add_finitePart, ← hs]
  have hFenc (f) (hf : f ∈ req.F) :
      B.code (P f) = extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    obtain ⟨p, hp, hρ, ho⟩ := hF f hf
    obtain ⟨hμ, hfp⟩ := hblocks f p hp
    obtain ⟨hs, _, hn, -, -⟩ := hsrc _ hμ
    rw [hp, hcode hμ hfp, hρ, ho, hs, extVisibilityReplace_of_finitePart_lt hn]
  have hFlt (f) (hf : f ∈ req.F) : extVisibilityReplace (e (req.ρ f)) req.N (req.off f) < ofOrd η := by
    obtain ⟨p, hp, -, -⟩ := hF f hf
    obtain ⟨hs, hfp⟩ := hblocks f p hp
    rw [← hFenc f hf, hp, hcode hs hfp, ofOrd_lt_ofOrd]
    exact (add_lt_add_right (Nat.cast_lt.mpr hfp) _).trans_le (hstrip _ hs)
  have ha : e req.a ≠ ⊥ := by
    intro hb
    rw [hb, extVisibilityReplace_bot] at hheight
    exact ofOrd_ne_bot η hheight.symm
  obtain ⟨V, hv, hvr, hvc, hframe, -⟩ := template_of_encoding_at_grade req e he ha hP
    root_mem top_mem root_le root_ne below_top κ hroot bountiful B.boundedMap_code
    hbotP (hheight ▸ selfVis_ofOrd_iff.mpr hη) (by simpa only [hheight] using hrootcap)
    hZ hFenc (by simpa only [hheight] using hFlt) (fun y hy => by rw [hT y hy, htop, hheight])
  exact ⟨V, hv, hvr, hvc, hframe⟩

/-- The actual construction retains the input occurrence geometry and the
whole actual private bottom-pattern class. -/
theorem exists_relativeData_of_context_with_root (req : Requests DA DQ)
    (grade_C : DA.grade req.C = req.N)
    (hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (ha_top : u₀ req.a.1 = ⊤) (ha_ne_top : semA.E req.C req.a ≠ ⊤)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C))
    (href : ∀ μ ∈ S, ∃ j < req.N, u₀ (ref μ).1 = ofOrd (μ + j))
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    (cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d)
    (hlit : ∀ r : DQ.below root, P r.1 = u₀ (κ r).1)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < req.N)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p)
    (htoproot : ∀ r : DQ.below root, u₀ (κ r).1 = ⊤ →
      extVisibilityReplace (semA.E req.C req.a) req.N req.R ≤ semA.E req.C (κ r)) :
    ∃ X : RelativeData DA semA DQ semQ, X.req = req ∧ X.root = root ∧
      HEq X.κ κ ∧ HEq X.ZA {d : DA.below (DA.cell req.C) | u₀ d.1 = ⊥} := by
  classical
  obtain ⟨τ, hw, -, hr⟩ := hu₀.rowWitness req.C
  have hτ : BoundedMap req.N τ := grade_C ▸ hw.bounded
  have hread (d : DA.below (DA.cell req.C)) : τ (semA.E req.C d) = u₀ d.1 :=
    (hr d).trans (min_eq_left (hC ▸ le_top))
  let e (d : DA.below (DA.cell req.C)) := if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d
  have he : RespectsSemanticsBelow semA (DA.cell req.C) e :=
    cleaned_respects_of_bottom_agreement hrow (hu₀.toBelow _)
      (fun d => d.2.2.trans_eq grade_C) hτ (fun d => by rw [hread d])
  have heq (d) (hd : u₀ d.1 ≠ ⊥) : e d = semA.E req.C d := if_neg hd
  have he_read (d) : τ (e d) = u₀ d.1 := by
    by_cases hd : u₀ d.1 = ⊥
    · simp [e, hd, hw.bot]
    · rw [heq d hd, hread]
  have hebot (d) : e d = ⊥ ↔ u₀ d.1 = ⊥ := by
    constructor
    · intro hb; rw [← he_read d, hb, hw.bot]
    · exact fun h => if_pos h
  have ha : u₀ req.a.1 ≠ ⊥ := ha_top.trans_ne top_ne_bot
  have hsa : e req.a = ofOrd (ordOf (e req.a)) :=
    (ofOrd_ordOf ((hebot _).not.mpr ha) ((heq _ ha).trans_ne ha_ne_top)).symm
  have hta : τ (ofOrd (ordOf (e req.a))) = ⊤ := by rw [← hsa, he_read, ha_top]
  obtain ⟨η, hheight, hη, hbound⟩ := strip_add_le_of_read_top hτ hta req.R req.R_lt_N
  rw [← hsa] at hheight
  have href' (μ) (hμ : μ ∈ S) : ∃ i < req.N, τ (e (ref μ)) = ofOrd (μ + i) := by
    simpa only [he_read] using href μ hμ
  have hstrip (μ) (hμ : μ ∈ S) : limitPart (ordOf (e (ref μ))) + req.N ≤ η := by
    obtain ⟨i, hi, hm⟩ := href' μ hμ
    have hf : finitePart (μ + (i : Ordinal.{0})) < req.N := by
      rwa [finitePart_add_nat_of_limit (hS μ hμ)]
    exact hbound _ _ ((read_strip hτ hm hf).1 ▸ hm) hf
  have htop (d : DQ.below root) (hd : P d.1 = ⊤) : ofOrd η ≤ e (κ d) := by
    have ht := (hlit d).symm.trans hd
    rw [heq _ (ht.trans_ne top_ne_bot), ← hheight, heq _ ha]
    exact htoproot d ht
  obtain ⟨V, hVr, hVroot, hVcorr, hframe⟩ := template_of_chart req e he hτ S hS ref href' le_rfl
    hheight hstrip hP root_mem top_mem root_le root_ne below_top (top_le_R.trans_lt req.R_lt_N)
    (top_le_R.trans hη) κ hroot bountiful hblocks hZ hT hF
    (fun d h => (hebot _).mpr ((hlit d).symm.trans h)) htop
    (fun d p h => (he_read _).trans ((hlit d).symm.trans h))
  have hρ (f) (hf : f ∈ req.F) : u₀ (req.ρ f).1 ≠ ⊥ := by
    obtain ⟨p, hp, hρ, -⟩ := hF f hf
    obtain ⟨i, -, hi⟩ := href _ (hblocks f p hp).1
    rw [hρ, hi]; exact ofOrd_ne_bot _
  have hOff (f) (hf : f ∈ req.F) : req.off f ≤ req.N := by
    obtain ⟨p, hp, -, ho⟩ := hF f hf
    rw [ho]; exact (hblocks f p hp).2.le
  exact ⟨mkRelativeData req grade_C (hC.trans_ne top_ne_bot) ha hρ hOff e hebot heq
    root_mem top_mem root_le root_ne below_top (top_le_R.trans req.R_lt_N.le)
    κ hroot bountiful cover V hVr hVroot hVcorr hframe, rfl, rfl, HEq.rfl, HEq.rfl⟩

end Context

end VaughtConjecture.Knight
