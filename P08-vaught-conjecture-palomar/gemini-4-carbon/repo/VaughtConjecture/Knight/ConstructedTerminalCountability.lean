/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AnchorStable
public import VaughtConjecture.Knight.GrowthCarrierEvaluation
public import VaughtConjecture.Knight.LimitOfChain
public import VaughtConjecture.Knight.TopGradeTerminalCounting
public import VaughtConjecture.Knight.CapReceivingModel

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Donor cleaning -/

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
    cleaner σ x = ⊥ ↔ σ x = ⊥ := by
  by_cases h : σ x = ⊥
  · rw [cleaner_of_eq h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [cleaner_of_ne h]
    exact ⟨fun hx => by rw [hx] at h; exact absurd hσ h, fun hx => absurd hx h⟩

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
      · rw [cleaner_of_eq hx]; exact bot_le
      · rw [cleaner_of_ne hx]; exact hxy
  comm x k i hk hi := by
    have h := hσ.comm x k i hk hi
    by_cases hx : σ x = ⊥
    · have h' : σ (extVisibilityReplace x k i) = ⊥ := by rw [h, hx, extVisibilityReplace_bot]
      rw [cleaner_of_eq hx, cleaner_of_eq h', extVisibilityReplace_bot]
    · have h' : σ (extVisibilityReplace x k i) ≠ ⊥ := by
        rw [h]; exact fun hb => hx ((evr_eq_bot_iff _ _).mp hb)
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
    simp only [cleaner, hbot d]
  rwa [e] at h

end Cleaning

/-! ## The cleaned donor at a cap -/

section Cap

variable {ιA : Type*} [DecidableEq ιA] {A : Finset ιA} {DA : CellScheme A} {semA : Semantics DA}

end Cap

/-! ## The template from an encoding -/

section Template

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- **The assembled relative data**: the cleaned donor is *constructed* from the actual
labelling and the cap's row; the template and its four properties are supplied by
`template_of_encoding` or `template_of_encoding_capped`. -/
noncomputable def mkRelativeData (req : Requests DA DQ) (grade_C : DA.grade req.C = req.N)
    (hrow : RespectsSemanticsBelow semA (DA.cell req.C) (semA.E req.C))
    {u₀ : Cell DA → ExtOrd} (hu₀ : RespectsSemantics semA u₀) (hC : u₀ req.C = ⊤)
    (a_ne : u₀ req.a.1 ≠ ⊥) (ρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥)
    (off_lt : ∀ f ∈ req.F, req.off f ≤ req.N) {root top : Finset ιQ × ℕ}
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
    (V_root : ∀ r : DQ.below root, V r.1 = if u₀ (κ r).1 = ⊥ then ⊥ else semA.E req.C (κ r))
    (V_correct : req.Correct (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) V)
    (frame : req.T.Nonempty → ∀ f ∈ req.F,
      req.tOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) f ≤
        req.dOf (fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d)) :
    RelativeData DA semA DQ semQ where
  req := req
  grade_C := grade_C
  ZA := {d | u₀ d.1 = ⊥}
  C_notin := by
    change ¬ u₀ req.C = ⊥
    rw [hC]; exact top_ne_bot
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
      have _ := hrow
      obtain ⟨g, σ, _, _, hbot, _, _, hread⟩ := hu₀.locality req.C
      have hd := hread d
      change min (u₀ d.1) (u₀ req.C) = min (σ (semA.E req.C d)) (g (DA.grade d.1)) at hd
      rw [hC, min_top_right, hE, hbot, min_eq_left bot_le] at hd
      exact h hd
  e_eq := fun d hd => by
    have hd' : ¬ u₀ d.1 = ⊥ := hd
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = _
    rw [ite_eq_right hd']
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
  have hVcap : ∀ d, min (V d) h = min (enc (P d)) h := fun d => hcap ⟨d, below_top d⟩
  have hVF : ∀ f ∈ req.F, V f = extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    intro f hf
    have h1 := hVcap f
    rw [hF f hf, min_eq_left (hFlt f hf).le] at h1
    -- KVC's RelativeLift exports this scalar helper without GuardActivation.
    exact eq_of_min_eq_of_lt' h1 (hFlt f hf)
  have hVT : ∀ y ∈ req.T, h ≤ V y := by
    intro y hy
    have h1 := hVcap y
    rw [hT y hy, min_self] at h1
    exact min_eq_right_iff.mp h1
  have hVZ : ∀ z ∈ req.Z, V z = ⊥ := by
    intro z hz
    have h1 := hVcap z
    rw [hZ z hz, henc.bot, min_eq_left bot_le] at h1
    rcases min_eq_bot.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hne
  refine ⟨V, hVr, fun r => hface r, ⟨?_, ?_, ?_⟩, ?_, hVF, hVT, hVZ⟩
  · intro z hz
    rw [hVZ z hz]
    exact min_eq_left bot_le
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
theorem template_of_encoding_capped (req : Requests DA DQ)
    (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (ha_ne : e req.a ≠ ⊥)
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P) {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_le_R : top.2 ≤ req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd,
      RespectsSemanticsBelow semA (DA.cell req.C) s →
        RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful)
    {enc : ExtOrd → ExtOrd} (henc : BoundedMap req.R enc)
    (hbotP : ∀ d, enc (P d) = ⊥ → P d = ⊥)
    (hvis : SelfVis req.R (extVisibilityReplace (e req.a) req.N req.R))
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
  exact template_of_encoding_at_grade req e he ha_ne hP root_mem top_mem root_le root_ne
    below_top κ hroot bountiful
    ⟨henc.bot, henc.mono, fun x k i hk hi => henc.comm x k i (hk.trans top_le_R) hi⟩
    hbotP (hvis.mono top_le_R) hroot_cap hZ hF hFlt hT

end Template

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## The ordinal under a proper value -/

theorem ofOrd_ordOf {x : ExtOrd} (hb : x ≠ ⊥) (ht : x ≠ ⊤) : ofOrd (ordOf x) = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact absurd rfl hb
  · exact absurd rfl ht
  · rw [ordOf_ofOrd]

/-! ## Reading-witness facts -/

section Reading

variable {N : ℕ} {τ : ExtOrd → ExtOrd} (hτ : BoundedMap N τ)

include hτ in
/-- A source read to a proper value with offset below `N` has offset below `N`, the same. -/
theorem read_finitePart {s t : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (ht : finitePart t < N) : finitePart s < N ∧ finitePart s = finitePart t := by
  have key : ∀ i ≤ N, τ (extVisibilityReplace (ofOrd s) N i) = ofOrd (limitPart t + i) := by
    intro i hi
    rw [hτ.comm _ N i le_rfl hi, h, extVisibilityReplace_of_finitePart_lt ht]
  have hlt : finitePart s < N := by
    by_contra hge
    have hge' := not_lt.mp hge
    have h1 := key (finitePart t) ht.le
    have h2 := key (finitePart t + 1) ht
    rw [extVisibilityReplace_of_le_finitePart hge'] at h1 h2
    rw [h1, ofOrd_inj] at h2
    have h3 := add_left_cancel h2
    exact absurd (Nat.cast_injective h3) (Nat.succ_ne_self _).symm
  refine ⟨hlt, ?_⟩
  have h1 := key (finitePart s) hlt.le
  rw [extVisibilityReplace_of_finitePart_lt hlt, limitPart_add_finitePart, h, ofOrd_inj] at h1
  have := congrArg finitePart h1
  rw [finitePart_limitPart_add_nat] at this
  exact this.symm

include hτ in
/-- Two proper readings with offsets below `N` in different blocks come from different
strips, in the same order. -/
theorem strip_lt_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (hlt : limitPart t < limitPart t') : limitPart s < limitPart s' := by
  have hss' : s < s' := by
    by_contra hle
    have := hτ.mono (ofOrd_le_ofOrd.mpr (not_lt.mp hle))
    rw [h, h', ofOrd_le_ofOrd] at this
    exact absurd (limitPart_mono this) (not_le.mpr hlt)
  have hlp : limitPart s ≤ limitPart s' := limitPart_mono hss'.le
  rcases hlp.lt_or_eq with hlt' | heq
  · exact hlt'
  exfalso
  have hfs := (read_finitePart hτ h ht).1
  have hfs' := (read_finitePart hτ h' ht').1
  have k1 := hτ.comm (ofOrd s) N 0 le_rfl (Nat.zero_le _)
  have k2 := hτ.comm (ofOrd s') N 0 le_rfl (Nat.zero_le _)
  rw [extVisibilityReplace_of_finitePart_lt hfs, h, extVisibilityReplace_of_finitePart_lt ht,
    Nat.cast_zero, add_zero, add_zero] at k1
  rw [extVisibilityReplace_of_finitePart_lt hfs', h', extVisibilityReplace_of_finitePart_lt ht',
    Nat.cast_zero, add_zero, add_zero] at k2
  rw [heq] at k1
  rw [k1, ofOrd_inj] at k2
  exact hlt.ne k2

include hτ in
/-- **Strip uniqueness**: two proper readings with offsets below `N` in the *same* block come
from the same strip.  Both sources sit on affine strips through offset `N`; if the strips
differed, the lower strip's `N`-endpoint would map at or below the upper strip's floor. -/
theorem strip_unique_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (heq : limitPart t = limitPart t') : limitPart s = limitPart s' := by
  have key : ∀ (s t : Ordinal.{0}), τ (ofOrd s) = ofOrd t → finitePart t < N →
      ∀ i ≤ N, τ (ofOrd (limitPart s + i)) = ofOrd (limitPart t + i) := by
    intro s t h ht i hi
    have hfs := (read_finitePart hτ h ht).1
    have k := hτ.comm (ofOrd s) N i le_rfl hi
    rwa [extVisibilityReplace_of_finitePart_lt hfs, h,
      extVisibilityReplace_of_finitePart_lt ht] at k
  have hNpos : (0 : ℕ) < N := lt_of_le_of_lt (Nat.zero_le _) ht
  -- one direction: a strictly lower strip is impossible
  have one : ∀ (s s' t t' : Ordinal.{0}), τ (ofOrd s) = ofOrd t → τ (ofOrd s') = ofOrd t' →
      finitePart t < N → finitePart t' < N → limitPart t = limitPart t' →
      ¬ limitPart s < limitPart s' := by
    intro s s' t t' h h' ht ht' heq hlt
    have h1 := key s t h ht N le_rfl
    have h2 := key s' t' h' ht' 0 (Nat.zero_le _)
    rw [Nat.cast_zero, add_zero, add_zero] at h2
    have hle : limitPart s + (N : Ordinal.{0}) < limitPart s' :=
      add_nat_lt_of_lt_limit (limitPart_idem s) (limitPart_idem s') hlt N
    have hm := hτ.mono (ofOrd_le_ofOrd.mpr hle.le)
    rw [h1, h2, ofOrd_le_ofOrd, ← heq] at hm
    have : (N : Ordinal.{0}) ≤ 0 := le_of_add_le_add_left (by rwa [add_zero])
    exact absurd (Nat.cast_le.mp this) (not_le.mpr hNpos)
  rcases lt_trichotomy (limitPart s) (limitPart s') with hlt | heq' | hgt
  · exact absurd hlt (one s s' t t' h h' ht ht' heq)
  · exact heq'
  · exact absurd hgt (one s' s t' t h' h ht' ht heq.symm)

include hτ in
/-- Below a source read to `⊤`: its offset-`R` replacement is a proper `R`-visible value, and
every strip of a proper reading with offset below `N`, plus `N`, lies at most there. -/
theorem strip_add_le_of_read_top {sa : Ordinal.{0}} (ha : τ (ofOrd sa) = ⊤) (R : ℕ)
    (hR : R < N) :
    ∃ h : Ordinal.{0}, extVisibilityReplace (ofOrd sa) N R = ofOrd h ∧ R ≤ finitePart h ∧
      ∀ s t : Ordinal.{0}, τ (ofOrd s) = ofOrd t → finitePart t < N →
        limitPart s + N ≤ h := by
  by_cases hfa : finitePart sa < N
  · refine ⟨limitPart sa + R, extVisibilityReplace_of_finitePart_lt hfa R, ?_, ?_⟩
    · rw [finitePart_limitPart_add_nat]
    · intro s t h ht
      have hfs := (read_finitePart hτ h ht).1
      have hss : s < sa := by
        by_contra hle
        have := hτ.mono (ofOrd_le_ofOrd.mpr (not_lt.mp hle))
        rw [h, ha] at this
        exact absurd this (not_top_le_ofOrd t)
      have hlp : limitPart s ≤ limitPart sa := limitPart_mono hss.le
      rcases hlp.lt_or_eq with hlt | heq
      · exact (limitPart_add_nat_le_of_lt hlt N).trans le_self_add
      · exfalso
        have k1 := hτ.comm (ofOrd s) N 0 le_rfl (Nat.zero_le _)
        have k2 := hτ.comm (ofOrd sa) N 0 le_rfl (Nat.zero_le _)
        rw [extVisibilityReplace_of_finitePart_lt hfs, h,
          extVisibilityReplace_of_finitePart_lt ht] at k1
        rw [extVisibilityReplace_of_finitePart_lt hfa, ha, extVisibilityReplace_top] at k2
        rw [heq] at k1
        rw [k1] at k2
        exact ofOrd_ne_top _ k2
  · have hfa' := not_lt.mp hfa
    refine ⟨sa, extVisibilityReplace_of_le_finitePart hfa' R, hR.le.trans hfa', ?_⟩
    intro s t h ht
    have hss : s < sa := by
      by_contra hle
      have := hτ.mono (ofOrd_le_ofOrd.mpr (not_lt.mp hle))
      rw [h, ha] at this
      exact absurd this (not_top_le_ofOrd t)
    calc limitPart s + (N : Ordinal.{0}) ≤ limitPart sa + (N : Ordinal.{0}) :=
          add_le_add_left (limitPart_mono hss.le) _
      _ ≤ limitPart sa + (finitePart sa : Ordinal.{0}) :=
          add_le_add_right (Nat.cast_le.mpr hfa') _
      _ = sa := limitPart_add_finitePart sa

end Reading

/-! ## The template from an actual receiving context -/

section Context

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

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
    ∃ X : RelativeData DA semA DQ semQ, X.req = req ∧ X.root = root ∧ X.top = top ∧
      HEq X.κ κ ∧ HEq X.ZA {d : DA.below (DA.cell req.C) | u₀ d.1 = ⊥} ∧
      (∀ d, X.e d = if u₀ d.1 = ⊥ then ⊥ else semA.E X.req.C d) ∧
      (∀ f ∈ X.req.F,
        X.V f = extVisibilityReplace (semA.E X.req.C (X.req.ρ f)) X.req.N (X.req.off f)) ∧
      (∀ y ∈ X.req.T, extVisibilityReplace (semA.E X.req.C X.req.a) X.req.N X.req.R ≤ X.V y) ∧
      ∀ z ∈ X.req.Z, X.V z = ⊥ := by
  classical
  -- the reading witness of the cap's row
  have hvis : SelfVis (DA.grade req.C) (u₀ req.C) := (hu₀.orderly req.C).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := DA.below (DA.cell req.C)) (grade := fun d => DA.grade d.1) (p := fun d => u₀ d.1)
    (c := req.capCell) (fun d => d.2.2) hvis (hu₀.locality req.C)
  have hτ : BoundedMap req.N τ :=
    ⟨hbot, hmono, fun x k i hk hi =>
      hcomm x k i (by change k ≤ DA.grade req.C; rw [grade_C]; exact hk) hi⟩
  have hread' : ∀ d : DA.below (DA.cell req.C), τ (semA.E req.C d) = u₀ d.1 := by
    intro d
    rw [hread d]
    change min (u₀ d.1) (u₀ req.C) = u₀ d.1
    rw [hC, min_top_right]
  have hτtop : τ ⊤ = ⊤ := by
    have h1 := hread' req.capCell
    change τ (semA.E req.C req.capCell) = u₀ req.C at h1
    rw [hC] at h1
    have h2 : τ (semA.E req.C req.capCell) ≤ τ ⊤ := hmono le_top
    rw [h1] at h2
    exact top_le_iff.mp h2
  -- the donor
  set e : DA.below (DA.cell req.C) → ExtOrd :=
    fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d with hedef
  have he : RespectsSemanticsBelow semA (DA.cell req.C) e :=
    cleaned_respects_of_bottom_agreement hrow (hu₀.toBelow _)
      (fun d => d.2.2.trans_eq grade_C) hτ (fun d => by rw [hread' d])
  have he_eq : ∀ d, u₀ d.1 ≠ ⊥ → e d = semA.E req.C d := fun d h => by
    change (if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d) = _
    rw [ite_eq_right h]
  -- the marker's source
  have ha_ne_bot : semA.E req.C req.a ≠ ⊥ := fun h0 => by
    have := hread' req.a
    rw [h0, hbot, ha_top] at this
    exact bot_ne_top this
  obtain ⟨sa, hsa⟩ : ∃ sa, semA.E req.C req.a = ofOrd sa := by
    rcases ExtOrd.cases (semA.E req.C req.a) with h | h | ⟨sa, h⟩
    · exact absurd h ha_ne_bot
    · exact absurd h ha_ne_top
    · exact ⟨sa, h⟩
  have hτa : τ (ofOrd sa) = ⊤ := by rw [← hsa, hread', ha_top]
  obtain ⟨h, hh, hRh, hstrip⟩ := strip_add_le_of_read_top hτ hτa req.R req.R_lt_N
  -- the references' sources
  have hsrc : ∀ μ ∈ S, ∃ s, semA.E req.C (ref μ) = ofOrd s ∧
      τ (ofOrd s) = u₀ (ref μ).1 := by
    intro μ hμ
    obtain ⟨j, -, hj⟩ := href μ hμ
    rcases ExtOrd.cases (semA.E req.C (ref μ)) with h0 | h0 | ⟨s, h0⟩
    · exfalso
      have := hread' (ref μ)
      rw [h0, hbot, hj] at this
      exact ofOrd_ne_bot _ this.symm
    · exfalso
      have := hread' (ref μ)
      rw [h0, hτtop, hj] at this
      exact ofOrd_ne_top _ this.symm
    · exact ⟨s, h0, by rw [← h0]; exact hread' _⟩
  set strip : Ordinal.{0} → Ordinal.{0} := fun μ => limitPart (ordOf (semA.E req.C (ref μ)))
    with hstripdef
  have hsrc' : ∀ μ ∈ S, ∃ j < req.N, τ (ofOrd (ordOf (semA.E req.C (ref μ)))) = ofOrd (μ + j) ∧
      strip μ = limitPart (ordOf (semA.E req.C (ref μ))) := by
    intro μ hμ
    obtain ⟨s, hs, hτs⟩ := hsrc μ hμ
    obtain ⟨j, hjN, hj⟩ := href μ hμ
    refine ⟨j, hjN, ?_, rfl⟩
    rw [hs, ordOf_ofOrd, hτs, hj]
  have hfpμ : ∀ μ ∈ S, ∀ j : ℕ, finitePart (μ + (j : Ordinal.{0})) = j := fun μ hμ j =>
    finitePart_add_nat_of_limit (hS μ hμ) j
  have hlpμ : ∀ μ ∈ S, ∀ j : ℕ, limitPart (μ + (j : Ordinal.{0})) = μ := fun μ hμ j =>
    limitPart_add_nat_of_limit (hS μ hμ) j
  -- the block code
  have hlim : ∀ μ ∈ S, limitPart (strip μ) = strip μ := fun μ _ => limitPart_idem _
  have hle : ∀ μ ∈ S, strip μ + req.N ≤ h := by
    intro μ hμ
    obtain ⟨j, hjN, hτs, -⟩ := hsrc' μ hμ
    exact hstrip _ _ hτs (by rw [hfpμ μ hμ]; exact hjN)
  have hstrict : ∀ μ ∈ S, ∀ μ' ∈ S, μ < μ' → strip μ < strip μ' := by
    intro μ hμ μ' hμ' hlt
    obtain ⟨j, hjN, hτs, -⟩ := hsrc' μ hμ
    obtain ⟨j', hjN', hτs', -⟩ := hsrc' μ' hμ'
    exact strip_lt_of_read hτ hτs hτs' (by rw [hfpμ μ hμ]; exact hjN)
      (by rw [hfpμ μ' hμ']; exact hjN') (by rw [hlpμ μ hμ, hlpμ μ' hμ']; exact hlt)
  set B : BlockCode := BlockCode.ofFinset req.N req.R req.R_lt_N S strip h hlim hle hstrict hRh
    with hBdef
  have hB_N : B.N = req.N := rfl
  have hB_R : B.R = req.R := rfl
  have hBtop : B.code ⊤ = ofOrd h := rfl
  have hBlisted : ∀ μ ∈ S, B.Λ μ = some (strip μ) := fun μ hμ =>
    BlockCode.ofFinset_Λ_listed req.N req.R req.R_lt_N S strip h hlim hle hstrict hRh hμ
  have hcode : ∀ p, limitPart p ∈ S → finitePart p ≤ req.N →
      B.code (ofOrd p) = ofOrd (strip (limitPart p) + finitePart p) := fun p hp hfp =>
    B.code_listed hp (hBlisted _ hp) hfp
  -- the source facts of a listed block
  have hsrcfp : ∀ μ ∈ S, finitePart (ordOf (semA.E req.C (ref μ))) < req.N := by
    intro μ hμ
    obtain ⟨j, hjN, hτs, -⟩ := hsrc' μ hμ
    exact (read_finitePart hτ hτs (by rw [hfpμ μ hμ]; exact hjN)).1
  have hevr : ∀ μ ∈ S, ∀ i, extVisibilityReplace (semA.E req.C (ref μ)) req.N i =
      ofOrd (strip μ + i) := by
    intro μ hμ i
    obtain ⟨s, hs, -⟩ := hsrc μ hμ
    have hfs : finitePart s < req.N := by
      have := hsrcfp μ hμ
      rwa [hs, ordOf_ofOrd] at this
    rw [hs, extVisibilityReplace_of_finitePart_lt hfs]
    change ofOrd (limitPart s + i) = ofOrd (limitPart (ordOf (semA.E req.C (ref μ))) + i)
    rw [hs, ordOf_ofOrd]
  -- the encoding hypotheses
  have hh' : extVisibilityReplace (e req.a) req.N req.R = ofOrd h := by
    rw [he_eq _ (by rw [ha_top]; exact top_ne_bot), hsa]; exact hh
  have hvish : SelfVis req.R (extVisibilityReplace (e req.a) req.N req.R) := by
    rw [hh']; exact extVisibilityReplace_of_le_finitePart hRh _
  have hbotP : ∀ d, B.code (P d) = ⊥ → P d = ⊥ := by
    intro d hd
    rcases ExtOrd.cases (P d) with h0 | h0 | ⟨p, h0⟩
    · exact h0
    · rw [h0, hBtop] at hd; exact absurd hd (ofOrd_ne_bot _)
    · obtain ⟨hp, hfp⟩ := hblocks d p h0
      rw [h0, hcode p hp hfp.le] at hd
      exact absurd hd (ofOrd_ne_bot _)
  -- proper-root alignment, derived from strip uniqueness
  have halign : ∀ (r : DQ.below root) p, P r.1 = ofOrd p →
      semA.E req.C (κ r) = ofOrd (strip (limitPart p) + finitePart p) := by
    intro r p hP0
    obtain ⟨hp, hfp⟩ := hblocks _ p hP0
    have hu : u₀ (κ r).1 = ofOrd p := by rw [← hlit r]; exact hP0
    obtain ⟨s, hs⟩ : ∃ s, semA.E req.C (κ r) = ofOrd s := by
      rcases ExtOrd.cases (semA.E req.C (κ r)) with h0 | h0 | ⟨s, h0⟩
      · exfalso
        have := hread' (κ r)
        rw [h0, hbot, hu] at this
        exact ofOrd_ne_bot _ this.symm
      · exfalso
        have := hread' (κ r)
        rw [h0, hτtop, hu] at this
        exact ofOrd_ne_top _ this.symm
      · exact ⟨s, h0⟩
    have hτs : τ (ofOrd s) = ofOrd p := by rw [← hs, hread', hu]
    obtain ⟨j, hjN, hτref, hstripμ⟩ := hsrc' _ hp
    have hlp : limitPart s = strip (limitPart p) := by
      rw [hstripμ]
      exact strip_unique_of_read hτ hτs hτref hfp (by rw [hfpμ _ hp]; exact hjN)
        (by rw [hlpμ _ hp])
    have hfp' : finitePart s = finitePart p := (read_finitePart hτ hτs hfp).2
    rw [hs, ← hlp, ← hfp', limitPart_add_finitePart]
  have hroot_cap : ∀ r : DQ.below root,
      min (B.code (P r.1)) (ofOrd h) = min (e (κ r)) (ofOrd h) := by
    intro r
    rcases ExtOrd.cases (u₀ (κ r).1) with h0 | h0 | ⟨p, h0⟩
    · rw [hlit r, h0, B.code_bot]
      change min ⊥ (ofOrd h) = min (if u₀ (κ r).1 = ⊥ then ⊥ else semA.E req.C (κ r)) (ofOrd h)
      rw [ite_eq_left h0]
    · rw [hlit r, h0, hBtop, min_self, he_eq _ (by rw [h0]; exact top_ne_bot)]
      have := htoproot r h0
      rw [hsa, hh] at this
      exact (min_eq_right this).symm
    · have hP0 : P r.1 = ofOrd p := by rw [hlit r, h0]
      obtain ⟨hp, hfp⟩ := hblocks _ p hP0
      rw [hP0, hcode p hp hfp.le, he_eq _ (by rw [h0]; exact ofOrd_ne_bot _), halign r p hP0]
  have hF' : ∀ f ∈ req.F, B.code (P f) =
      extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    intro f hf
    obtain ⟨p, hPf, hρ, hoff⟩ := hF f hf
    obtain ⟨hp, hfp⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [hPf, hcode p hp hfp.le, hρ, hoff, he_eq _ (by rw [hj]; exact ofOrd_ne_bot _), hevr _ hp]
  have hFlt : ∀ f ∈ req.F, extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R := by
    intro f hf
    obtain ⟨p, hPf, hρ, hoff⟩ := hF f hf
    obtain ⟨hp, hfp⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [hρ, hoff, he_eq _ (by rw [hj]; exact ofOrd_ne_bot _), hevr _ hp, hh', ofOrd_lt_ofOrd]
    calc strip (limitPart p) + (finitePart p : Ordinal.{0})
        < strip (limitPart p) + (req.N : Ordinal.{0}) :=
          (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp)
      _ ≤ h := hle _ hp
  have hT' : ∀ y ∈ req.T, B.code (P y) = extVisibilityReplace (e req.a) req.N req.R := by
    intro y hy
    rw [hT y hy, hBtop, hh']
  have ha_ne : e req.a ≠ ⊥ := by
    rw [he_eq _ (by rw [ha_top]; exact top_ne_bot), hsa]; exact ofOrd_ne_bot _
  -- the template
  obtain ⟨V, hVr, hVroot, hVcorr, hframe, hVF, hVT, hVZ⟩ := template_of_encoding_capped req e he
    ha_ne hP root_mem top_mem root_le root_ne below_top top_le_R κ hroot bountiful
    (B.boundedMap_code) hbotP hvish (by rw [hh']; exact hroot_cap) hZ hF' hFlt hT'
  have ha_ne' : u₀ req.a.1 ≠ ⊥ := by rw [ha_top]; exact top_ne_bot
  have hρ_ne : ∀ f ∈ req.F, u₀ (req.ρ f).1 ≠ ⊥ := by
    intro f hf
    obtain ⟨p, hPf, hρ, -⟩ := hF f hf
    obtain ⟨hp, -⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [hρ, hj]; exact ofOrd_ne_bot _
  have hoff_lt : ∀ f ∈ req.F, req.off f ≤ req.N := by
    intro f hf
    obtain ⟨p, hPf, -, hoff⟩ := hF f hf
    rw [hoff]; exact (hblocks f p hPf).2.le
  refine ⟨mkRelativeData req grade_C hrow hu₀ hC ha_ne' hρ_ne hoff_lt root_mem top_mem root_le
    root_ne below_top (top_le_R.trans req.R_lt_N.le) κ hroot bountiful cover V hVr hVroot hVcorr
    hframe, rfl, rfl, rfl, HEq.rfl, HEq.rfl, fun _ => rfl, ?_, ?_, hVZ⟩
  · intro f hf
    have h1 := hVF f hf
    obtain ⟨p, hPf, hρ, -⟩ := hF f hf
    obtain ⟨hp, -⟩ := hblocks f p hPf
    obtain ⟨j, -, hj⟩ := href _ hp
    rw [he_eq _ (by rw [hρ, hj]; exact ofOrd_ne_bot _)] at h1
    exact h1
  · intro y hy
    have h1 := hVT y hy
    rw [he_eq _ ha_ne'] at h1
    exact h1

end Context

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.HollowGrowth
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open CellScheme.restrictFace
noncomputable section
universe w

private theorem evr_offset_mono (x : ExtOrd) (N : ℕ) {i j : ℕ} (h : i ≤ j) :
    extVisibilityReplace x N i ≤ extVisibilityReplace x N j := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · simp
  · simp
  · by_cases ha : finitePart a < N
    · rw [extVisibilityReplace_of_finitePart_lt ha,
        extVisibilityReplace_of_finitePart_lt ha, ofOrd_le_ofOrd]
      exact add_le_add_right (Nat.cast_le.mpr h) _
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha),
        extVisibilityReplace_of_le_finitePart (not_lt.mp ha)]

private theorem exists_marker {α : Ordinal.{0}} {n : ℕ} {p : S α n} {c : Cell p.scheme.scheme}
    (hsc : p.scheme.scheme.scope c = Finset.univ) (hgr : p.scheme.scheme.grade c = p.topGrade)
    (hc : p.label c = ⊤) :
    ∃ r : p.scheme.scheme.below (p.scheme.scheme.cell c), p.label r.1 = ⊤ ∧
      ∀ L ≤ p.topGrade, ∀ d : p.scheme.scheme.below (p.scheme.scheme.cell c), p.label d.1 = ⊤ →
        ofOrd (α + L) ≤ p.someProvisionalValue d.1 →
          extVisibilityReplace (p.scheme.rows.E c r) p.topGrade L ≤ p.scheme.rows.E c d := by
  classical
  let : Fintype (p.scheme.scheme.below (p.scheme.scheme.cell c)) := Fintype.ofFinite _
  let T := Finset.univ.filter fun d : p.scheme.scheme.below (p.scheme.scheme.cell c) =>
    p.label d.1 = ⊤
  obtain ⟨r, hr, hmin⟩ := T.exists_min_image (p.scheme.rows.E c)
    ⟨⟨c, GradedLe.refl _⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  have hmin' (s) (hs : p.label s.1 = ⊤) := hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
  refine ⟨r, (Finset.mem_filter.mp hr).2, fun L hL d hd hv => ?_⟩
  by_cases hcap : p.ProvisionalCap d.1
  · obtain ⟨s, hs, hsd⟩ := hcap.transport d.2 hsc hgr hc
    exact ((evr_mono (hmin' s hs) hL).trans (evr_offset_mono _ _ hL)).trans hsd
  · have hnotself : extVisibilityReplace (p.scheme.rows.E c d) p.topGrade p.topGrade ≠
        p.scheme.rows.E c d := fun h => hcap ⟨c, d.2, d, hsc, hgr, hc, hd, h.le⟩
    obtain ⟨a, ha, hfp⟩ : ∃ a : Ordinal.{0}, p.scheme.rows.E c d = ofOrd a ∧
        finitePart a < p.topGrade := by
      rcases ExtOrd.cases (p.scheme.rows.E c d) with hb | ht | ⟨a, ha⟩
      · simp [hb] at hnotself
      · simp [ht] at hnotself
      · exact ⟨a, ha, by
          by_contra hn
          exact hnotself (by rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hn)])⟩
    have hband : p.ProvisionalBand d.1 (finitePart a) := ⟨c, d.2, hsc, hgr, hc, by
      change p.scheme.rows.E c d =
        extVisibilityReplace (p.scheme.rows.E c d) p.topGrade (finitePart a)
      rw [ha, extVisibilityReplace_of_finitePart_lt hfp, limitPart_add_finitePart]⟩
    have hval : p.someProvisionalValue d.1 = ofOrd (α + finitePart a) :=
      (isProvisionalValue_iff.mp (Or.inr (Or.inr ⟨hd, hcap, finitePart a, hband, rfl⟩))).symm
    rw [hval, ofOrd_le_ofOrd] at hv
    apply (evr_mono (hmin' d hd) hL).trans
    rw [ha, extVisibilityReplace_of_finitePart_lt hfp, ofOrd_le_ofOrd]
    exact (add_le_add_right (le_of_add_le_add_left hv) _).trans_eq (limitPart_add_finitePart a)

private theorem belowMap_val_of_heq {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    {A : Finset ιA} {B : Finset ιB} {DA : CellScheme A} {DB : CellScheme B}
    {I J : Finset ιA × ℕ} {U V : Finset ιB × ℕ} (hIJ : I = J) (hUV : U = V)
    {f : DA.below I → DB.below U} {g : DA.below J → DB.below V}
    (hfg : HEq f g) (a : DA.below I) : (f a).1 = (g ⟨a.1, hIJ ▸ a.2⟩).1 := by
  subst J; subst V; exact congrArg Subtype.val (congrFun (eq_of_heq hfg) a)

variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

private theorem receives_exactly_of_pos (hM : W.IsModel) (hg : W.HasTopGradeGrowth)
    (hh : W.IsHollow) {n : ℕ} (hn : 0 < n) (t : Fin n ↪ M) (p : S α.1 n)
    (hp : W.eval t = some p) (q : S α.1 (n + 1)) (hq : IsCoface p q) :
    ∃ (y : M) (hy : y ∉ Set.range t), W.eval (snoc t y hy) = some q := by
  classical
  obtain ⟨C₀, hCN, -, -⟩ := exists_referenceContext_margin hM p hp
    (donorRequests q) (donorRequests_ok q) (n + 1)
  have hpc : typeMap C₀.proj C₀.p₀ = some p := by
    have h := hM.consistent C₀.ctx C₀.p₀ C₀.proj C₀.eval_ctx
    rw [C₀.proj_ctx, hp, knightTower_pull] at h; exact h.symm
  obtain ⟨x, hxK, e₀, he₀, hpx⟩ := hg (max (max C₀.m C₀.N) (n + 1)) ⟨_, C₀.ctx, C₀.p₀, C₀.eval_ctx⟩
  obtain ⟨y, f₀, hf₀, hxy, hsync⟩ := exists_syncCover' hM.consistent hM.covering x.eval_eq (n + 1)
  have hcy : typeMap (e₀.trans f₀) y.type = some C₀.p₀ := by
    rw [← typeMap_trans e₀ f₀ y.type x.type hxy]; exact hpx
  let C := y.type
  have hN : max (max C₀.m C₀.N) (n + 1) < C.topGrade :=
    hxK.trans_le (topGrade_le_of_typeMap_eq_some hxy)
  have hNm : C₀.m < C.topGrade := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hN)
  have hNC : C₀.N < C.topGrade := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hN)
  have hn1 : n + 1 < C.topGrade := (le_max_right _ _).trans_lt hN
  obtain ⟨cap, hsc, hgr, hctop⟩ := exists_topCell_of_topGrade_pos C (by omega)
  obtain ⟨marker, hmtop, hmark⟩ := exists_marker hsc hgr hctop
  let face := C₀.proj.trans (e₀.trans f₀)
  have hface_tup : face.trans y.tuple = t := by
    simp only [face, Function.Embedding.trans_assoc, hf₀, he₀, C₀.proj_ctx]
  have hpy : typeMap face C = some p := by
    rw [← typeMap_trans C₀.proj _ C C₀.p₀ hcy]; exact hpc
  have below (d : Cell C₀.p₀.scheme.scheme) :
      GradedLe (C.scheme.scheme.cell (mapCell hcy d)) (C.scheme.scheme.cell cap) :=
    ⟨by change C.scheme.scheme.scope (mapCell hcy d) ⊆ C.scheme.scheme.scope cap
        rw [hsc]; exact Finset.subset_univ _,
      by change C.scheme.scheme.grade (mapCell hcy d) ≤ C.scheme.scheme.grade cap
         rw [hgr, grade_mapCell hcy]
         have hcard := Finset.card_le_univ (C₀.p₀.scheme.scheme.scope d)
         simp only [Fintype.card_fin] at hcard
         exact (C₀.p₀.scheme.scheme.grade_le_card_scope d).trans (hcard.trans hNm.le)⟩
  let ref : Ordinal.{0} → C.scheme.scheme.below (C.scheme.scheme.cell cap) :=
    fun μ => ⟨mapCell hcy (C₀.repBase μ), below _⟩
  let req : Requests C.scheme.scheme q.scheme.scheme := {
    C := cap, N := C.topGrade, R := n + 1, R_lt_N := hn1,
    Z := {d | q.label d = ⊥}, F := {d | q.label d ≠ ⊥ ∧ q.label d ≠ ⊤}, T := {d | q.label d = ⊤},
    ρ := fun d => ref (limitPart (ordOf (q.label d))),
    off := fun d => finitePart (ordOf (q.label d)), a := marker }
  have hvP := hq.extendsDomain.visible
  have hP' : q.restrictFace Fin.castSuccEmb hvP = p := restrictFace_eq_of_typeMap_eq_some hq
  have hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme := congrArg scheme hP'
  have hvC := visible_of_typeMap_eq_some hpy
  have hC' : C.restrictFace face hvC = p := restrictFace_eq_of_typeMap_eq_some hpy
  have hC : C.scheme.restrictFace face hvC = p.scheme := congrArg scheme hC'
  let root : Finset (Fin (n + 1)) × ℕ := (Finset.univ.image Fin.castSuccEmb, n)
  let top : Finset (Fin (n + 1)) × ℕ := (Finset.univ, n + 1)
  have hc : GradedLe (Finset.univ.image face, n) (C.scheme.scheme.cell cap) :=
    ⟨by change _ ⊆ C.scheme.scheme.scope cap; rw [hsc]; exact Finset.subset_univ _,
      by change _ ≤ C.scheme.scheme.grade cap; rw [hgr]; exact (Nat.le_succ n).trans hn1.le⟩
  let κ := Growth.literalKappa p.scheme Fin.castSuccEmb hvP hP face hvC hC cap hc
  have hlit (a : q.scheme.scheme.below root) : q.label a.1 = C.label (κ a).1 := by
    change q.label a.1 = C.label (commonFace Fin.castSuccEmb hvP hP face hvC hC n a).1
    rw [commonFace_val]
    exact ((StageType.label_castCell hC'.symm _).trans
      ((StageType.label_castCell hP' _).trans
        (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ a)))).symm
  have htoproot (a : q.scheme.scheme.below root) (ha : C.label (κ a).1 = ⊤) :
      extVisibilityReplace (C.scheme.rows.E cap marker) C.topGrade (n + 1) ≤
        C.scheme.rows.E cap (κ a) := by
    let d : Cell p.scheme.scheme := SemScheme.castCell hP ((bP Fin.castSuccEmb hvP n).symm a).1
    have he : (κ a).1 = mapCell hpy d := by
      change (commonFace Fin.castSuccEmb hvP hP face hvC hC n a).1 = _
      rw [commonFace_val]; rfl
    let d₀ := mapCell hpc d
    have hd₀ : C₀.p₀.label d₀ = ⊤ := by
      rw [he, label_mapCell hpy] at ha; rw [label_mapCell hpc, ha]
    have hsv := stableValue_mapCell' hM.consistent x.eval_eq he₀ hpx d₀
    have hprov : ofOrd (α.1 + ↑(n + 1)) < y.type.someProvisionalValue (mapCell hcy d₀) :=
      (mapCell_trans hxy hpx hcy d₀) ▸
        (hsync (mapCell hpx d₀)).2 (by rw [label_mapCell hpx, hd₀])
          (hsv.trans ((stableValue_eq_label_of_hollow hM hh C₀.eval_ctx d₀).trans hd₀))
    have hka : (κ a).1 = mapCell hcy d₀ := he.trans (mapCell_trans hcy hpc hpy d)
    exact hmark (n + 1) hn1.le (κ a) ha (hka ▸ hprov.le)
  have hmarker : C.scheme.rows.E cap marker ≠ ⊤ := by
    rcases C.scheme.rows_coded cap marker with h | ⟨_, _, _, h⟩ <;> rw [h]
    · exact bot_ne_top
    · exact ofOrd_ne_top _
  have hrmem : root ∈ Plan.gradedPlan q.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr ⟨hvP, hn, ?_⟩
    dsimp only [root]
    simp only [Finset.card_image_of_injective _ Fin.castSuccEmb.injective,
      Finset.card_univ, Fintype.card_fin, le_refl]
  have htmem : top ∈ Plan.gradedPlan q.scheme.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨q.scheme.scheme.isPlan.domain_mem, Nat.succ_pos n,
      by dsimp only [top]; simp only [Finset.card_univ, Fintype.card_fin, le_refl]⟩
  have hbelowQ (d : Cell q.scheme.scheme) : GradedLe (q.scheme.scheme.cell d) top :=
    ⟨Finset.subset_univ _, (q.scheme.scheme.grade_le_card_scope d).trans
      (by simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_univ (q.scheme.scheme.scope d))⟩
  obtain ⟨X, hreq, hr, _, hk, hz, _⟩ :=
    exists_relativeData_of_context_with_root req hgr (C.scheme.consistent cap) C.respects
      hctop hmtop hmarker (blocks q)
      (fun μ hμ => by
        obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
        exact limitPart_eq_self_of_isNonSuccessor (donorRequests_ok q r hr).1)
      ref
      (fun μ hμ => by
        obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
        exact ⟨C₀.repOff r.block, (C₀.rep_off_lt r hr).trans hNC,
          (label_mapCell hcy _).trans (C₀.rep_label r hr)⟩)
      q.respects hrmem htmem
      ⟨Finset.subset_univ _, Nat.le_succ n⟩
      (fun h => Nat.ne_add_one n (congrArg Prod.snd h))
      hbelowQ
      le_rfl κ (fun _ hs => Growth.literalKappa_lawful _ _ _ _ _ _ _ _ _ hs)
      q.scheme.bountiful
      (fun d => by
        by_cases hb : q.label d = ⊥
        · exact Or.inl hb
        by_cases ht : q.label d = ⊤
        · exact Or.inr (Or.inr (Or.inl ht))
        exact Or.inr (Or.inl ⟨hb, ht⟩))
      hlit
      (fun d β hd => by
        have hr := mem_donorRequests.mpr ⟨d, β, hd, rfl⟩
        exact ⟨mem_blocks.mpr ⟨_, hr, rfl⟩, (C₀.offset_lt _ hr).trans hNC⟩)
      (fun _ h => h) (fun _ h => h)
      (fun d hd => by
        rcases ExtOrd.cases (q.label d) with hb | ht | ⟨β, hβ⟩
        · exact (hd.1 hb).elim
        · exact (hd.2 ht).elim
        · exact ⟨β, hβ, by dsimp [req]; rw [hβ, ordOf_ofOrd],
            by dsimp [req]; rw [hβ, ordOf_ofOrd]⟩)
      htoproot
  have hin : InClass X.ZA C.label := by
    have hiff : ∀ {B₁ B₂ : Finset (Fin y.arity) × ℕ}, B₁ = B₂ →
        ∀ {Z₁ : Set (C.scheme.scheme.below B₁)} {Z₂ : Set (C.scheme.scheme.below B₂)},
          HEq Z₁ Z₂ → (InClass Z₁ C.label ↔ InClass Z₂ C.label)
      | _, _, rfl, _, _, hZ => by rw [eq_of_heq hZ]
    exact (hiff (congrArg (fun r => C.scheme.scheme.cell r.C) hreq) hz).mpr fun _ => Iff.rfl
  obtain ⟨z, _, hzRoot, s, heval, he, hc'⟩ :=
    GrowthCarrierEvaluation.exists_correct_donor C q.scheme p.scheme face hvC hvP hC hP X
      ⟨hr, fun a => belowMap_val_of_heq hr (congrArg (fun r => C.scheme.scheme.cell r.C) hreq) hk a⟩
      (hreq.symm ▸ hn1) W.actualLabelling hM y.eval_eq hin
  rw [hreq] at hc'
  have hsq : s = q := StageType.eq_of_label he fun d => by
    let v := fun d' => s.label (SemScheme.castCell he.symm d')
    by_cases hb : q.label d = ⊥
    · have hz' := hc'.1 d hb
      change min (v d) (C.label cap) = ⊥ at hz'
      rw [hctop, min_top_right] at hz'
      exact hz'.trans hb.symm
    by_cases ht : q.label d = ⊤
    · have htop' := hc'.2.2 d ht
      change min (extVisibilityReplace (C.label marker.1) C.topGrade (n + 1)) (C.label cap) ≤
        min (v d) (C.label cap) at htop'
      rw [hmtop, hctop, extVisibilityReplace_top, min_self, min_top_right] at htop'
      exact (top_le_iff.mp htop').trans ht.symm
    · have hp' := hc'.2.1 d ⟨hb, ht⟩
      rcases ExtOrd.cases (q.label d) with hb' | ht' | ⟨β, hβ⟩
      · exact (hb hb').elim
      · exact (ht ht').elim
      have hr' := mem_donorRequests.mpr ⟨d, β, hβ, rfl⟩
      have hμ := limitPart_idem β
      change min (v d) (C.label cap) = min (extVisibilityReplace
        (C.label (ref (limitPart (ordOf (q.label d)))).1) C.topGrade
          (finitePart (ordOf (q.label d)))) (C.label cap) at hp'
      rw [hctop, min_top_right, min_top_right, hβ, ordOf_ofOrd,
        (label_mapCell hcy _).trans (C₀.rep_label _ hr'),
        extVisibilityReplace_of_finitePart_lt (by
          rw [finitePart_add_nat_of_limit hμ]; exact (C₀.rep_off_lt _ hr').trans hNC),
        limitPart_add_nat_of_limit hμ, limitPart_add_finitePart] at hp'
      exact hp'.trans hβ.symm
  have hr' : ∃ hzRoot : z ∉ Set.range (face.trans y.tuple),
      W.eval (snoc (face.trans y.tuple) z hzRoot) = some q := ⟨hzRoot, hsq ▸ heval⟩
  exact ⟨z, hface_tup ▸ hr'⟩

private theorem receives_exactly (hM : W.IsModel) (hg : W.HasTopGradeGrowth) (hh : W.IsHollow)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.1 (n + 1)) (hq : IsCoface p q) :
    ∃ (y : M) (hy : y ∉ Set.range t), W.eval (snoc t y hy) = some q := by
  by_cases hn : 0 < n
  · exact receives_exactly_of_pos hM hg hh hn t p hp q hq
  obtain ⟨z, hz, pR, _, hco, heval⟩ := hM.highGradeDominance t p hp 0 stage_pos
  obtain ⟨Q, hQ, hkeep⟩ := FixedHeight.pinnedCofaceLift (CanonicalCoatomSupply.supply α.2)
    1 (by omega) pR Fin.castSuccEmb p hco q hq
  obtain ⟨y, hy, heval'⟩ := receives_exactly_of_pos hM hg hh (Nat.succ_pos n) _ pR heval Q hQ
  have he := exactParent_typeMap hM.consistent
    (snoc (snoc t z hz) y hy) Q (FixedHeight.extendFace Fin.castSuccEmb) heval'
  have htup : (FixedHeight.extendFace Fin.castSuccEmb).trans (snoc (snoc t z hz) y hy) =
      snoc t y (fun ⟨i, hi⟩ => hy ⟨Fin.castSucc i, (snoc_apply_castSucc t z hz i).trans hi⟩) := by
    apply Function.Embedding.ext; intro i
    refine Fin.lastCases ?_ (fun _ => ?_) i <;>
      simp [Function.Embedding.trans_apply, snoc_apply_last, snoc_apply_castSucc]
  rw [htup] at he
  exact ⟨y, _, he.trans hkeep⟩

private theorem exists_common_cover {M₁ M₂ : Type w}
    {V : KnightRealization α M₁} {W : KnightRealization α M₂}
    (hcV : V.IsExactParentConsistent) (hvV : V.IsInitialSegmentCovering) (hW : W.IsModel)
    (hgW : W.HasTopGradeGrowth) (hhW : W.IsHollow) {n : ℕ} {t₁ : Fin n ↪ M₁}
    {t₂ : Fin n ↪ M₂} {p : S α.1 n} (h₁ : V.eval t₁ = some p) (h₂ : W.eval t₂ = some p)
    (x : M₁) :
    ∃ (N : ℕ) (f : Fin n ↪ Fin N) (s : Fin N ↪ M₁) (u : Fin N ↪ M₂) (P : S α.1 N),
      f.trans s = t₁ ∧ f.trans u = t₂ ∧ V.eval s = some P ∧ W.eval u = some P ∧
        ∃ i, s i = x := by
  classical
  by_cases hx : x ∈ Set.range t₁
  · obtain ⟨i, hi⟩ := hx
    exact ⟨n, Function.Embedding.refl _, t₁, t₂, p, Function.Embedding.refl_trans _,
      Function.Embedding.refl_trans _, h₁, h₂, i, hi⟩
  · obtain ⟨k, s, hst, hsome⟩ := hvV (snoc t₁ x hx)
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hsome
    have hft : (Fin.castSuccEmb.trans (Fin.castAddEmb k)).trans s = t₁ := trans_snoc_cover hst
    have htm : typeMap (Fin.castSuccEmb.trans (Fin.castAddEmb k)) P = some p := by
      rw [← exactParent_typeMap hcV s P _ hP, hft]; exact h₁
    obtain ⟨u, hut, huP⟩ := rootedExtensionOver_of_onePoint hW.consistent
      (fun t' p' _ hp' q' hq' _ =>
        let ⟨y, hy, he⟩ := receives_exactly hW hgW hhW t' p' hp' q' hq'
        ⟨snoc t' y hy, castSuccEmb_trans_snoc t' y hy, he⟩)
      t₂ p ⟨Function.Embedding.refl _, Function.Embedding.refl_trans _⟩ h₂ _ P htm trivial
    exact ⟨_, _, s, u, P, hft, hut, hP, huP, cover_mem_range hst⟩

theorem nonempty_iso {M₁ M₂ : Type w} [Countable M₁] [Countable M₂]
    {V : KnightRealization α M₁} {W : KnightRealization α M₂}
    (hV : V.IsModel) (hW : W.IsModel)
    (hgV : V.HasTopGradeGrowth) (hgW : W.HasTopGradeGrowth)
    (hhV : V.IsHollow) (hhW : W.IsHollow) : Nonempty (V.Iso W) := by
  obtain ⟨sV, hsV⟩ := exists_eval_empty_at hV
  obtain ⟨sW, hsW⟩ := exists_eval_empty_at hW
  have hs : sW = sV := Subsingleton.elim _ _; subst sW
  have hstep : CommonChartStepSupply (A₁ := V) (A₂ := W) := by
    rintro nd (x | y)
    · obtain ⟨N, f, s, u, P, hs, hu, hsP, huP, i, hi⟩ :=
        exists_common_cover hV.consistent hV.covering hW hgW hhW nd.eval₁ nd.eval₂ x
      exact ⟨⟨⟨N, s, u, P, hsP, huP⟩, f, hs, hu, fun _ hx => ⟨i, hi.trans (Sum.inl.inj hx)⟩,
        fun _ hy => absurd hy Sum.inl_ne_inr⟩⟩
    · obtain ⟨N, f, s, u, P, hs, hu, hsP, huP, i, hi⟩ :=
        exists_common_cover hW.consistent hW.covering hV hgV hhV nd.eval₂ nd.eval₁ y
      exact ⟨⟨⟨N, u, s, P, huP, hsP⟩, f, hu, hs, fun _ hx => absurd hx.symm Sum.inl_ne_inr,
        fun _ hy => ⟨i, hi.trans (Sum.inr.inj hy)⟩⟩⟩
  obtain ⟨e, -⟩ := exists_iso_of_selectedCommonCharts hV.consistent hW.consistent (fun _ => True)
    ⟨0, Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, sV, hsV, hsW⟩ trivial
    (restrictedCommonChartStepSupply_true hstep)
  exact ⟨e⟩

end
end VaughtConjecture.Knight.HollowGrowth

namespace VaughtConjecture.Knight.ConstructedSpectrumEndpoint
open TypeTower StageType KnightRealization Value ExtOrd AmalgamationPlan CappedDonor
open Transform SharpWitnessComposition CellScheme.restrictFace
noncomputable section
universe w

section Encoding
variable {N L r i : ℕ} {τ : ExtOrd → ExtOrd} (hτ : BoundedMap N τ)
  {α sa : Ordinal.{0}} (hα : limitPart α = α)
  (ha : τ (ofOrd sa) = ofOrd (α + i)) (hi : i < N) (hLN : L < N) (hrL : r < L)
  (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ)
  (hle : ∀ μ ∈ S, μ ≤ α) (src : Ordinal.{0} → Ordinal.{0})
  (off : Ordinal.{0} → ℕ) (hoff : ∀ μ ∈ S, off μ < N)
  (hread : ∀ μ ∈ S, τ (ofOrd (src μ)) = ofOrd (μ + off μ))

include hτ hα ha hi hLN in
private theorem marker_read : τ (ofOrd (limitPart sa + L)) = ofOrd (α + L) := by
  have hf : finitePart (α + i) < N := by rw [finitePart_add_nat_of_limit hα]; exact hi
  have hs := (read_finitePart hτ ha hf).1
  have he := hτ.comm (ofOrd sa) N L le_rfl hLN.le
  rwa [extVisibilityReplace_of_finitePart_lt hs, ha,
    extVisibilityReplace_of_finitePart_lt hf, limitPart_add_nat_of_limit hα] at he

include hτ hα ha hi hS hle hoff hread in
private theorem strip_le (μ : Ordinal.{0}) (hμ : μ ∈ S) :
    limitPart (src μ) ≤ limitPart sa := by
  have hf : finitePart (μ + off μ) < N := by
    rw [finitePart_add_nat_of_limit (hS μ hμ)]; exact hoff μ hμ
  have hfa : finitePart (α + i) < N := by rw [finitePart_add_nat_of_limit hα]; exact hi
  rcases (hle μ hμ).lt_or_eq with hm | hm
  · exact (strip_lt_of_read hτ (hread μ hμ) ha hf hfa (by
      rw [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit hα]; exact hm)).le
  · exact (strip_unique_of_read hτ (hread μ hμ) ha hf hfa (by
      rw [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit hα, hm])).le

private def capCode : BlockCode :=
  BlockCode.ofFinset L r hrL S (fun μ => limitPart (src μ)) (limitPart sa + L)
    (fun μ _ => limitPart_idem (src μ))
    (fun μ hμ => add_le_add_left (strip_le hτ hα ha hi S hS hle src off hoff hread μ hμ) _)
    (fun μ hμ ν hν hμν => strip_lt_of_read hτ (hread μ hμ) (hread ν hν)
      (by rw [finitePart_add_nat_of_limit (hS μ hμ)]; exact hoff μ hμ)
      (by rw [finitePart_add_nat_of_limit (hS ν hν)]; exact hoff ν hν)
      (by rw [limitPart_add_nat_of_limit (hS μ hμ), limitPart_add_nat_of_limit (hS ν hν)]; exact hμν))
    (by rw [finitePart_limitPart_add_nat]; exact hrL.le)

private theorem capCode_listed {p : Ordinal.{0}} (hp : limitPart p ∈ S) (hfp : finitePart p ≤ L) :
    (capCode hτ hα ha hi hrL S hS hle src off hoff hread).code (ofOrd p) =
      ofOrd (limitPart (src (limitPart p)) + finitePart p) :=
  BlockCode.code_listed _ hp (BlockCode.ofFinset_Λ_listed L r hrL S _ _ _ _ _ _ hp) hfp

include hLN in
private theorem capCode_of_read {p b : Ordinal.{0}} (hp : limitPart p ∈ S)
    (hfp : finitePart p < L) (hb : τ (ofOrd b) = ofOrd p) :
    (capCode hτ hα ha hi hrL S hS hle src off hoff hread).code (ofOrd p) = ofOrd b := by
  have ho : finitePart (limitPart p + off (limitPart p)) < N := by
    rw [finitePart_limitPart_add_nat]; exact hoff _ hp
  have hsame := strip_unique_of_read hτ hb (hread _ hp) (hfp.trans hLN) ho
    (by rw [limitPart_add_nat_of_limit (limitPart_idem p)])
  rw [capCode_listed hτ hα ha hi hrL S hS hle src off hoff hread hp hfp.le, ← hsame,
    ← (read_finitePart hτ hb (hfp.trans hLN)).2, limitPart_add_finitePart]
end Encoding

private theorem exists_cap_template {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
    {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
    {semA : Semantics DA} {semQ : Semantics DQ}
    (req : Requests DA DQ) (e : DA.below (DA.cell req.C) → ExtOrd)
    (he : RespectsSemanticsBelow semA (DA.cell req.C) e) (heproper : ∀ d, e d ≠ ⊤)
    (w : Cell DA → ExtOrd) (hebot : ∀ d, e d = ⊥ ↔ w d.1 = ⊥)
    {τ : ExtOrd → ExtOrd} (hτ : BoundedMap req.N τ)
    (hchart : ∀ d, τ (e d) = min (w d.1) (w req.C))
    {α : Ordinal.{0}} (hα : limitPart α = α) {i : ℕ} (hi : i < req.N)
    (ha : w req.a.1 = ofOrd (α + i)) (hai : ofOrd (α + i) < w req.C)
    (hcut : ofOrd (α + req.R) < w req.C)
    (S : Finset Ordinal.{0}) (hS : ∀ μ ∈ S, limitPart μ = μ) (hle : ∀ μ ∈ S, μ ≤ α)
    (ref : Ordinal.{0} → DA.below (DA.cell req.C)) (off : Ordinal.{0} → ℕ)
    (hoff : ∀ μ ∈ S, off μ < req.N) (href : ∀ μ ∈ S, τ (e (ref μ)) = ofOrd (μ + off μ))
    {P : Cell DQ → ExtOrd} (hP : RespectsSemantics semQ P)
    (hblocks : ∀ d p, P d = ofOrd p → limitPart p ∈ S ∧ finitePart p < req.R)
    (hproper : ∀ d, P d ≠ ⊤ → P d < ofOrd (α + req.R))
    {root top : Finset ιQ × ℕ}
    (root_mem : root ∈ Plan.gradedPlan DQ.plan) (top_mem : top ∈ Plan.gradedPlan DQ.plan)
    (root_le : GradedLe root top) (root_ne : root ≠ top)
    (below_top : ∀ d, GradedLe (DQ.cell d) top) (top_lt_R : top.2 < req.R)
    (κ : DQ.below root → DA.below (DA.cell req.C))
    (hroot : ∀ s, RespectsSemanticsBelow semA (DA.cell req.C) s →
      RespectsSemanticsBelow semQ root (fun d => s (κ d)))
    (bountiful : semQ.IsBountiful) (hlit : ∀ d, P d.1 = w (κ d).1)
    (hZ : ∀ z ∈ req.Z, P z = ⊥) (hT : ∀ y ∈ req.T, P y = ⊤)
    (hF : ∀ f ∈ req.F, ∃ p, P f = ofOrd p ∧ req.ρ f = ref (limitPart p) ∧
      req.off f = finitePart p) :
    ∃ V : Cell DQ → ExtOrd, RespectsSemantics semQ V ∧ (∀ d, V d.1 = e (κ d)) ∧
      req.Correct e V ∧ (req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e) := by
  classical
  have hma : τ (e req.a) = ofOrd (α + i) := by rw [hchart, ha, min_eq_left hai.le]
  have hanb : e req.a ≠ ⊥ := fun hb => ofOrd_ne_bot _ (by rw [hb, hτ.bot] at hma; exact hma.symm)
  let sa := ordOf (e req.a)
  have hsa : e req.a = ofOrd sa := (ofOrd_ordOf hanb (heproper _)).symm
  have hmar : τ (ofOrd sa) = ofOrd (α + i) := hsa ▸ hma
  let src := fun μ => ordOf (e (ref μ))
  have hsrc (μ) (hμ : μ ∈ S) : e (ref μ) = ofOrd (src μ) :=
    (ofOrd_ordOf (fun hb => ofOrd_ne_bot _ (by have hr := href μ hμ; rw [hb, hτ.bot] at hr; exact hr.symm))
      (heproper _)).symm
  have hread (μ) (hμ : μ ∈ S) : τ (ofOrd (src μ)) = ofOrd (μ + off μ) := by
    rw [← hsrc μ hμ, href μ hμ]
  let B := capCode hτ hα hmar hi top_lt_R S hS hle src off hoff hread
  let height := ofOrd (limitPart sa + req.R)
  have hBtop : B.code ⊤ = height := rfl
  have hcode {p : Ordinal.{0}} (hp : limitPart p ∈ S) (hfp : finitePart p ≤ req.R) :
      B.code (ofOrd p) = ofOrd (limitPart (src (limitPart p)) + finitePart p) :=
    capCode_listed hτ hα hmar hi top_lt_R S hS hle src off hoff hread hp hfp
  have hfs : finitePart sa < req.N :=
    (read_finitePart hτ hmar (by rw [finitePart_add_nat_of_limit hα]; exact hi)).1
  have hheight : extVisibilityReplace (e req.a) req.N req.R = height := by
    rw [hsa, extVisibilityReplace_of_finitePart_lt hfs]
  have hheight_read : τ height = ofOrd (α + req.R) := marker_read hτ hα hmar hi req.R_lt_N
  have hbotP (d) (hb : B.code (P d) = ⊥) : P d = ⊥ := by
    rcases ExtOrd.cases (P d) with hb' | ht | ⟨p, hp⟩
    · exact hb'
    · rw [ht, hBtop] at hb; exact (ofOrd_ne_bot _ hb).elim
    · obtain ⟨hs, ho⟩ := hblocks d p hp
      rw [hp, hcode hs ho.le] at hb; exact (ofOrd_ne_bot _ hb).elim
  have hrootcap (d : DQ.below root) : min (B.code (P d.1)) height = min (e (κ d)) height := by
    rcases ExtOrd.cases (P d.1) with hb | ht | ⟨p, hp⟩
    · rw [hb, B.code_bot, (hebot _).mpr ((hlit d).symm.trans hb)]
    · rw [ht, hBtop, min_self]
      have hr := hchart (κ d); rw [← hlit, ht, min_top_left] at hr
      refine (min_eq_right (by
        by_contra hn
        have hm := hτ.mono (not_le.mp hn).le
        rw [hr, hheight_read] at hm; exact (not_le_of_gt hcut) hm)).symm
    · obtain ⟨hs, ho⟩ := hblocks d.1 p hp
      have heq : e (κ d) = ofOrd (ordOf (e (κ d))) :=
        (ofOrd_ordOf (fun hz => ofOrd_ne_bot p ((hp.symm.trans (hlit d)).trans ((hebot _).mp hz)))
          (heproper _)).symm
      have hr : τ (ofOrd (ordOf (e (κ d)))) = ofOrd p := by
        rw [← heq, hchart, ← hlit,
          min_eq_left ((hproper d.1 (hp ▸ ofOrd_ne_top p)).trans hcut).le, hp]
      rw [hp, capCode_of_read hτ hα hmar hi req.R_lt_N top_lt_R S hS hle src off hoff hread hs ho hr,
        ← heq]
  have hFenc (d) (hd : d ∈ req.F) :
      B.code (P d) = extVisibilityReplace (e (req.ρ d)) req.N (req.off d) := by
    obtain ⟨p, hp, hρ, ho⟩ := hF d hd
    obtain ⟨hs, hfp⟩ := hblocks d p hp
    rw [hp, hcode hs hfp.le, hρ, ho, hsrc _ hs, extVisibilityReplace_of_finitePart_lt
      (read_finitePart hτ (hread _ hs) (by rw [finitePart_limitPart_add_nat]; exact hoff _ hs)).1]
  have hFlt (d) (hd : d ∈ req.F) :
      extVisibilityReplace (e (req.ρ d)) req.N (req.off d) < height := by
    obtain ⟨p, hp, _, _⟩ := hF d hd
    obtain ⟨hs, hfp⟩ := hblocks d p hp
    rw [← hFenc d hd, hp, hcode hs hfp.le]
    exact ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp) |>.trans_le
      (add_le_add_left (strip_le hτ hα hmar hi S hS hle src off hoff hread _ hs) _))
  have hvis : SelfVis top.2 (extVisibilityReplace (e req.a) req.N req.R) := by
    rw [hheight]
    exact extVisibilityReplace_of_le_finitePart
      (by rw [finitePart_limitPart_add_nat]; exact top_lt_R.le) _
  obtain ⟨V, hV, hVr, hVc, hframe, -⟩ :=
    template_of_encoding_at_grade req e he hanb hP root_mem top_mem root_le root_ne
      below_top κ hroot bountiful B.boundedMap_code hbotP hvis
      (by simpa only [hheight] using hrootcap) hZ hFenc
      (by simpa only [hheight] using hFlt)
      (fun y hy => (congrArg B.code (hT y hy)).trans (hBtop.trans hheight.symm))
  exact ⟨V, hV, hVr, hVc, hframe⟩

private theorem block_le {α : LimitStage} {β : Ordinal.{0}} (hβ : β < α.nextBlock.1) :
    limitPart β ≤ α.1 := by
  rcases lt_or_ge β α.1 with h | h
  · exact (limitPart_le β).trans h.le
  · obtain ⟨k, rfl⟩ := exists_nat_of_lt_add_omega h hβ
    rw [limitPart_add_nat_of_limit (limitPart_eq_self_of_isNonSuccessor (Or.inr α.2))]

private theorem exists_cut {α : LimitStage} {n : ℕ} (q : S α.nextBlock.1 (n + 1)) (floor : ℕ) :
    ∃ L : ℕ, floor < L ∧ n + 1 < L ∧
      (∀ d β, q.label d = ofOrd β → finitePart β < L) ∧
      ∀ d, q.label d ≠ ⊤ → q.label d < ofOrd (α.1 + L) := by
  classical
  let L := max floor (max (n + 1)
    (Finset.univ.sup fun d : Cell q.scheme.scheme => finitePart (ordOf (q.label d)))) + 1
  have hfp (d) (β) (hd : q.label d = ofOrd β) : finitePart β < L := by
    have h := Finset.le_sup (f := fun d : Cell q.scheme.scheme =>
      finitePart (ordOf (q.label d))) (Finset.mem_univ d)
    rw [hd, ordOf_ofOrd] at h; dsimp [L]; omega
  refine ⟨L, by dsimp [L]; omega, by dsimp [L]; omega, hfp, fun d hnt => ?_⟩
  rcases ExtOrd.cases (q.label d) with hb | ht | ⟨β, hd⟩
  · rw [hb]; exact bot_lt_ofOrd _
  · exact (hnt ht).elim
  · have hb := block_le (ofOrd_lt_ofOrd.mp (hd ▸ (q.label_bound d).resolve_right hnt))
    rw [hd, ofOrd_lt_ofOrd]
    calc β = limitPart β + finitePart β := (limitPart_add_finitePart β).symm
      _ < limitPart β + (L : Ordinal.{0}) := add_lt_add_right (Nat.cast_lt.mpr (hfp d β hd)) _
      _ ≤ α.1 + (L : Ordinal.{0}) := add_le_add_left hb _

private theorem private_bottom {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hM : W.IsModel) {J : ℕ} {u : Fin J ↪ M} {C : S α.1 J}
    (hC : W.eval u = some C) (d : Cell C.scheme.scheme) :
    W.stableValue u C d = ⊥ ↔ C.label d = ⊥ := by
  rw [← truncExt_stableValue hM.consistent hM.covering hC d]; exact truncExt_eq_bot_iff.symm

private theorem exists_cleaned_source_chart {M : Type w} {α : LimitStage}
    {W : KnightRealization α M} (hM : W.IsModel) {J : ℕ} {u : Fin J ↪ M} {C : S α.1 J}
    (hC : W.eval u = some C) (c : Cell C.scheme.scheme) (hc : C.label c = ⊤) :
    ∃ e : C.scheme.scheme.below (C.scheme.scheme.cell c) → ExtOrd,
      RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) e ∧
      (∀ d, e d = ⊥ ↔ C.label d.1 = ⊥) ∧
      (∀ d, C.label d.1 ≠ ⊥ → e d = C.scheme.rows.E c d) ∧
      ∃ θ : ExtOrd → ExtOrd, BoundedMap (C.scheme.scheme.grade c) θ ∧
        ∀ d, θ (e d) = min (W.stableValue u C d.1) (W.stableValue u C c) := by
  have hl := stableLiftRespects hM hC
  have hvis : SelfVis (C.scheme.scheme.grade c) (W.stableValue u C c) := (hl.orderly c).symm
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := C.scheme.scheme.below (C.scheme.scheme.cell c))
    (grade := fun d => C.scheme.scheme.grade d.1) (p := fun d => W.stableValue u C d.1)
    (c := ⟨c, GradedLe.refl _⟩) (fun d => d.2.2) hvis (hl.locality c)
  have hcb : W.stableValue u C c ≠ ⊥ := fun h =>
    top_ne_bot (hc.symm.trans ((private_bottom hM hC c).mp h))
  have hbottom (d : C.scheme.scheme.below (C.scheme.scheme.cell c)) :
      τ (C.scheme.rows.E c d) = ⊥ ↔ W.stableValue u C d.1 = ⊥ := by
    rw [hread d]
    exact ⟨fun h => (min_eq_bot.mp h).resolve_right hcb, fun h => by rw [h, min_eq_left bot_le]⟩
  let e : C.scheme.scheme.below (C.scheme.scheme.cell c) → ExtOrd :=
    fun d => if C.label d.1 = ⊥ then ⊥ else C.scheme.rows.E c d
  have he : RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) e := by
    simpa only [private_bottom hM hC] using cleaned_respects_of_bottom_agreement
      (C.scheme.consistent c) (hl.toBelow _) (fun d => d.2.2) ⟨hbot, hmono, hcomm⟩ hbottom
  have heq (d) (hd : C.label d.1 ≠ ⊥) : e d = C.scheme.rows.E c d := ite_eq_right hd
  have heb (d) : e d = ⊥ ↔ C.label d.1 = ⊥ := by
    by_cases hd : C.label d.1 = ⊥
    · simp only [e, hd, ite_true]
    · rw [heq d hd]
      exact ⟨fun h => (hd ((private_bottom hM hC d.1).mp
        ((hbottom d).mp (by rw [h, hbot])))).elim, fun h => (hd h).elim⟩
  refine ⟨e, he, heb, heq, fun x => min (τ x) (W.stableValue u C c),
    ⟨by rw [hbot, min_eq_left bot_le], fun _ _ hxy => min_le_min_right _ (hmono hxy),
      fun x k i hk hi => by rw [hcomm x k i hk hi, evr_min_of_selfVis hvis hk hi]⟩, fun d => ?_⟩
  change min (τ (e d)) (W.stableValue u C c) = min (W.stableValue u C d.1) (W.stableValue u C c)
  by_cases hd : C.label d.1 = ⊥
  · rw [(heb d).mpr hd, hbot, (private_bottom hM hC d.1).mpr hd]
  · rw [heq d hd, hread d, min_assoc, min_self]

private theorem receives_positive {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hM : W.IsModel) (hh : ¬ W.IsHollow) (hg : W.HasTopGradeGrowth) {n : ℕ} (hn : 0 < n)
    (t : Fin n ↪ M) (p : S α.1 n) (hp : W.eval t = some p)
    (q : S α.nextBlock.1 (n + 1)) (hq : IsCoface (stableLiftType hM t p hp) q)
    (γ : Ordinal.{0}) (hγ : γ < α.nextBlock.1) :
    ∃ (y : M) (hy : y ∉ Set.range t) (s : S α.1 (n + 1)),
      W.eval (snoc t y hy) = some s ∧ ∃ he : q.scheme = s.scheme,
        (∀ d, q.label d ≠ ⊤ →
          W.stableValue (snoc t y hy) s (SemScheme.castCell he d) = q.label d) ∧
        (∀ d, q.label d = ⊤ →
          ofOrd γ < W.stableValue (snoc t y hy) s (SemScheme.castCell he d)) := by
  classical
  obtain ⟨k, s₀, p₀, hs₀, a₀, i, hatop, ha₀⟩ :=
    (hasInfinityAnchor_iff_exists_finite_stable hM).mp (Classical.not_not.mp hh)
  obtain ⟨b, hb⟩ : ∃ b : ℕ, γ < α.1 + b := by
    rcases lt_or_ge γ α.1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨b, rfl⟩ := exists_nat_of_lt_add_omega h hγ
      exact ⟨b + 1, add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self b)) _⟩
  obtain ⟨L, hbL, hnL, hfp, hproper⟩ := exists_cut q b
  have hγL : ofOrd γ < ofOrd (α.1 + L) :=
    ofOrd_lt_ofOrd.mpr (hb.trans (add_lt_add_right (Nat.cast_lt.mpr hbL) _))
  have hblim (μ) (hμ : μ ∈ blocks q) : limitPart μ = μ := by
    obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
    exact limitPart_eq_self_of_isNonSuccessor (donorRequests_ok q r hr).1
  have hble (μ) (hμ : μ ∈ blocks q) : μ ≤ α.1 := by
    obtain ⟨r, hr, rfl⟩ := mem_blocks.mp hμ
    obtain ⟨d, β, hd, rfl⟩ := mem_donorRequests.mp hr
    exact block_le (ofOrd_lt_ofOrd.mp (hd ▸ (q.label_bound d).resolve_right (hd ▸ ofOrd_ne_top _)))
  let old := (blocks q).filter (· < α.1)
  let reqs : List BlockRequest := old.toList.map fun μ => ⟨μ, 0⟩
  obtain ⟨C₀, hC₀⟩ := exists_ctx_hasCells hM (Ctx.root p hp) reqs fun r hr => by
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hr
    have hm := Finset.mem_filter.mp (Finset.mem_toList.mp hμ)
    exact ⟨hblim μ hm.1 ▸ CappedDonor.isNonSuccessor_limitPart μ, hm.2⟩
  choose repBase repOff hrep using fun μ : old =>
    hC₀ ⟨μ.1, 0⟩ (List.mem_map.mpr ⟨μ.1, Finset.mem_toList.mpr μ.2, rfl⟩)
  let offsetBound : ℕ := Finset.univ.sup repOff
  obtain ⟨y₀, hxy₀, g₀, hgu₀⟩ :=
    exists_labelledExt_le hM.consistent hM.covering ⟨k, s₀, p₀, hs₀⟩ C₀.ctx
  obtain ⟨z, hhigh, hyz⟩ := hg (max (max L C₀.m) (max offsetBound i)) y₀
  change max (max L C₀.m) (max offsetBound i) < z.type.topGrade at hhigh
  obtain ⟨f₀, hfu₀, hf₀⟩ := hxy₀.trans hyz
  obtain ⟨e₀, heu₀, _⟩ := hyz
  let g := g₀.trans e₀
  have hgu : g.trans z.tuple = C₀.ctx := by rw [Function.Embedding.trans_assoc, heu₀, hgu₀]
  let u := z.tuple
  let C := z.type
  have hC : W.eval u = some C := z.eval_eq
  have hhigh' : max (max L C₀.m) (max offsetBound i) < C.topGrade := hhigh
  obtain ⟨c, hsc, hgr, hc⟩ := exists_topCell_of_topGrade_pos C (by omega)
  let f := C₀.proj.trans g
  have hfu : f.trans u = t := by rw [Function.Embedding.trans_assoc, hgu, C₀.proj_ctx]
  have hf : typeMap f C = some p := by
    have h := hM.consistent u C f hC
    rw [hfu, hp, knightTower_pull] at h; exact h.symm
  have hgQ : typeMap g C = some C₀.p₀ := by
    have h := hM.consistent u C g hC
    rw [hgu, C₀.eval_ctx, knightTower_pull] at h; exact h.symm
  have hLN : L < C.scheme.scheme.grade c := by rw [hgr]; omega
  have hi' : i < C.scheme.scheme.grade c := by rw [hgr]; omega
  have hm : C₀.m < C.scheme.scheme.grade c := by rw [hgr]; omega
  have hoff : offsetBound < C.scheme.scheme.grade c := by rw [hgr]; omega
  have hbound := stable_ge_of_top hM hC hc
  have hcut : ofOrd (α.1 + L) < W.stableValue u C c :=
    (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr hLN) _)).trans_le hbound
  have hai : ofOrd (α.1 + i) < W.stableValue u C c :=
    (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr hi') _)).trans_le hbound
  have hab : GradedLe (C.scheme.scheme.cell (mapCell hf₀ a₀)) (C.scheme.scheme.cell c) :=
    ⟨by change C.scheme.scheme.scope (mapCell hf₀ a₀) ⊆ C.scheme.scheme.scope c
        rw [hsc]; exact Finset.subset_univ _,
      by change C.scheme.scheme.grade (mapCell hf₀ a₀) ≤ C.scheme.scheme.grade c
         rw [grade_mapCell, hgr]
         exact (le_csSup p₀.topGrades_bddAbove (grade_mem_topGrades hatop)).trans
           (topGrade_le_of_typeMap_eq_some hf₀)⟩
  let a : C.scheme.scheme.below (C.scheme.scheme.cell c) := ⟨mapCell hf₀ a₀, hab⟩
  have ha : W.stableValue u C a.1 = ofOrd (α.1 + i) := by
    rw [stableValue_mapCell' hM.consistent hC hfu₀ hf₀, ha₀]
  have hbelowC (d : Cell C₀.p₀.scheme.scheme) :
      GradedLe (C.scheme.scheme.cell (mapCell hgQ d)) (C.scheme.scheme.cell c) :=
    ⟨by change C.scheme.scheme.scope (mapCell hgQ d) ⊆ C.scheme.scheme.scope c
        rw [hsc]; exact Finset.subset_univ _,
      by change C.scheme.scheme.grade (mapCell hgQ d) ≤ C.scheme.scheme.grade c
         rw [grade_mapCell]
         have hcard := Finset.card_le_univ (C₀.p₀.scheme.scheme.scope d)
         simp only [Fintype.card_fin] at hcard
         exact (C₀.p₀.scheme.scheme.grade_le_card_scope d).trans (hcard.trans hm.le)⟩
  let ref : Ordinal.{0} → C.scheme.scheme.below (C.scheme.scheme.cell c) := fun μ =>
    if μ = α.1 then a else
      if hμ : μ ∈ old then ⟨mapCell hgQ (repBase ⟨μ, hμ⟩), hbelowC _⟩ else ⟨c, GradedLe.refl _⟩
  let off : Ordinal.{0} → ℕ := fun μ =>
    if μ = α.1 then i else if hμ : μ ∈ old then repOff ⟨μ, hμ⟩ else 0
  have href (μ) (hμ : μ ∈ blocks q) : off μ < C.scheme.scheme.grade c ∧
      W.stableValue u C (ref μ).1 = ofOrd (μ + off μ) ∧
      ofOrd (μ + off μ) < W.stableValue u C c := by
    by_cases heq : μ = α.1
    · subst μ; simpa [ref, off] using ⟨hi', ha, hai⟩
    · have hmem : μ ∈ old := Finset.mem_filter.mpr ⟨hμ, lt_of_le_of_ne (hble μ hμ) heq⟩
      let b' : old := ⟨μ, hmem⟩
      have hlab := hrep b'
      have hnt : C₀.p₀.label (repBase b') ≠ ⊤ := hlab ▸ ofOrd_ne_top _
      have hst : W.stableValue u C (mapCell hgQ (repBase b')) = ofOrd (μ + repOff b') := by
        rw [stableValue_mapCell' hM.consistent hC hgu hgQ,
          stableValue_of_ne_top hM.consistent hM.covering C₀.eval_ctx hnt, hlab]
      have hlt : ofOrd (μ + repOff b') < W.stableValue u C c := by
        have hb₀ := (C₀.p₀.label_bound (repBase b')).resolve_right hnt
        rw [hlab] at hb₀
        exact hb₀.trans_le ((ofOrd_le_ofOrd.mpr le_self_add).trans hbound)
      simpa [ref, off, heq, hmem, b'] using
        ⟨(Finset.le_sup (f := repOff) (Finset.mem_univ b')).trans_lt hoff, hst, hlt⟩
  have hvP := visible_of_typeMap_eq_some hq
  have hvC := visible_of_typeMap_eq_some hf
  have hP : q.scheme.restrictFace Fin.castSuccEmb hvP = p.scheme :=
    congrArg StageType.scheme (restrictFace_eq_of_typeMap_eq_some hq)
  have hF : C.scheme.restrictFace f hvC = p.scheme :=
    congrArg StageType.scheme (restrictFace_eq_of_typeMap_eq_some hf)
  let root : Finset (Fin (n + 1)) × ℕ := (Finset.univ.image Fin.castSuccEmb, n)
  let top : Finset (Fin (n + 1)) × ℕ := (Finset.univ, n + 1)
  have hbelowR : GradedLe (Finset.univ.image f, n) (C.scheme.scheme.cell c) :=
    ⟨by change _ ⊆ C.scheme.scheme.scope c; rw [hsc]; exact Finset.subset_univ _,
      (Nat.le_succ n).trans (hnL.le.trans hLN.le)⟩
  let κ := Growth.literalKappa p.scheme Fin.castSuccEmb hvP hP f hvC hF c hbelowR
  have hlit (d : q.scheme.scheme.below root) : q.label d.1 = W.stableValue u C (κ d).1 := by
    have hP' := restrictFace_eq_of_typeMap_eq_some hq
    have hsf : typeMap f (stableLiftType hM u C hC) = some (stableLiftType hM t p hp) := by
      have h := stableLift_consistent hM u (stableLiftType hM u C hC) f (stableLift_eval_some hM hC)
      rw [hfu, stableLift_eval_some hM hp] at h; exact h.symm
    have hC' := restrictFace_eq_of_typeMap_eq_some hsf
    change q.label d.1 = W.stableValue u C (commonFace Fin.castSuccEmb hvP hP f hvC hF n d).1
    rw [commonFace_val]
    exact ((StageType.label_castCell hC'.symm _).trans
      ((StageType.label_castCell hP' _).trans
        (congrArg q.label (toCell_belowEquiv_symm_val _ _ _ _ d)))).symm
  let req : Requests C.scheme.scheme q.scheme.scheme := {
    C := c, N := C.scheme.scheme.grade c, R := L, R_lt_N := hLN,
    Z := {d | q.label d = ⊥}, F := {d | q.label d ≠ ⊥ ∧ q.label d ≠ ⊤}, T := {d | q.label d = ⊤},
    ρ := fun d => ref (limitPart (ordOf (q.label d))),
    off := fun d => finitePart (ordOf (q.label d)), a := a }
  obtain ⟨e, he, hebot, heeq, τ, hτ, hchart⟩ := exists_cleaned_source_chart hM hC c hc
  have heproper (d) : e d ≠ ⊤ := by
    by_cases hb : C.label d.1 = ⊥
    · rw [(hebot d).mpr hb]; exact bot_ne_top
    · rw [heeq d hb]
      rcases C.scheme.rows_coded c d with h | ⟨_, _, _, h⟩ <;> rw [h]
      · exact bot_ne_top
      · exact ofOrd_ne_top _
  have hblocks (d β) (hd : q.label d = ofOrd β) :
      limitPart β ∈ blocks q ∧ finitePart β < L :=
    ⟨mem_blocks.mpr ⟨_, mem_donorRequests.mpr ⟨d, β, hd, rfl⟩, rfl⟩, hfp d β hd⟩
  have hfields (d) (hd : d ∈ req.F) : ∃ β, q.label d = ofOrd β ∧
      req.ρ d = ref (limitPart β) ∧ req.off d = finitePart β := by
    rcases ExtOrd.cases (q.label d) with hb | ht | ⟨β, hβ⟩
    · exact (hd.1 hb).elim
    · exact (hd.2 ht).elim
    · exact ⟨β, hβ, by dsimp [req]; rw [hβ, ordOf_ofOrd], by dsimp [req]; rw [hβ, ordOf_ofOrd]⟩
  have hrmem : root ∈ Plan.gradedPlan q.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr ⟨hvP, hn, ?_⟩
    dsimp only [root]
    simp only [Finset.card_image_of_injective _ Fin.castSuccEmb.injective,
      Finset.card_univ, Fintype.card_fin, le_refl]
  have htmem : top ∈ Plan.gradedPlan q.scheme.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨q.scheme.scheme.isPlan.domain_mem, Nat.succ_pos n,
      by dsimp only [top]; simp only [Finset.card_univ, Fintype.card_fin, le_refl]⟩
  have hrt : GradedLe root top := ⟨Finset.subset_univ _, Nat.le_succ _⟩
  have hrne : root ≠ top := fun h => Nat.succ_ne_self n (congrArg Prod.snd h).symm
  have htop (d) : GradedLe (q.scheme.scheme.cell d) top :=
    ⟨Finset.subset_univ _, (q.scheme.scheme.grade_le_card_scope d).trans
      (by simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_univ (q.scheme.scheme.scope d))⟩
  have hroot : ∀ s, RespectsSemanticsBelow C.scheme.rows (C.scheme.scheme.cell c) s →
      RespectsSemanticsBelow q.scheme.rows root (fun d => s (κ d)) :=
    fun _ hs => Growth.literalKappa_lawful _ _ _ _ _ _ _ _ _ hs
  have hαlim : limitPart α.1 = α.1 := limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)
  obtain ⟨V, hV, hVr, hVc, hframe⟩ :=
    exists_cap_template req e he heproper (W.stableValue u C)
      (fun d => (hebot d).trans (private_bottom hM hC d.1).symm)
      hτ hchart hαlim hi' ha hai hcut (blocks q) hblim hble ref off
      (fun μ hμ => (href μ hμ).1)
      (fun μ hμ => by rw [hchart, (href μ hμ).2.1, min_eq_left (href μ hμ).2.2.le])
      q.respects hblocks hproper hrmem htmem hrt hrne htop hnL κ hroot q.scheme.bountiful hlit
      (fun _ h => h) (fun _ h => h) hfields
  let X : RelativeData C.scheme.scheme C.scheme.rows q.scheme.scheme q.scheme.rows := {
    req := req, grade_C := rfl, ZA := {d | C.label d.1 = ⊥},
    C_notin := by change C.label c ≠ ⊥; rw [hc]; exact top_ne_bot,
    a_notin := fun hb => ofOrd_ne_bot _ (ha ▸ (private_bottom hM hC a.1).mpr hb),
    ρ_notin := fun d hd hb => by
      obtain ⟨β, hβ, hρ, -⟩ := hfields d hd
      have h := (private_bottom hM hC (req.ρ d).1).mpr hb
      rw [hρ, (href _ (hblocks d β hβ).1).2.1] at h; exact ofOrd_ne_bot _ h,
    off_lt := fun d hd => by
      obtain ⟨β, hβ, -, ho⟩ := hfields d hd
      rw [ho]; exact (hfp d β hβ).le.trans hLN.le,
    e := e, e_bot := hebot, e_eq := heeq,
    root := root, top := top, root_mem := hrmem, top_mem := htmem,
    root_le := hrt, root_ne := hrne, below_top := htop, top_le_N := hnL.le.trans hLN.le,
    κ := κ, hroot := hroot, bountiful := q.scheme.bountiful,
    cover := fun d => by
      by_cases hb : q.label d = ⊥
      · exact Or.inl hb
      by_cases ht : q.label d = ⊤
      · exact Or.inr (Or.inr (Or.inl ht))
      exact Or.inr (Or.inl ⟨hb, ht⟩),
    V := V, V_respects := hV, V_root := hVr, V_correct := hVc, frame := hframe }
  obtain ⟨y, _, hyRoot, s, hev, he', hc'⟩ :=
    GrowthCarrierEvaluation.exists_correct_donor C q.scheme p.scheme f hvC hvP hF hP X
      ⟨rfl, fun _ => rfl⟩ (hnL.trans hLN)
      { label := W.stableValue
        lawful := by intro n' u' p' hp'; exact stableLiftRespects_of_consistent hM.consistent hM.covering hp'
        mapCell := by intro n' m' u' p' v' q' hv g' hgu' hpq d; exact stableValue_mapCell' hM.consistent hv hgu' hpq d }
      hM hC (fun d => private_bottom hM hC d.1)
  have hy : y ∉ Set.range t := by rwa [hfu] at hyRoot
  have hsnoc : ∀ {w : Fin n ↪ M} (hw : w = t) (hyw : y ∉ Set.range w),
      snoc w y hyw = snoc t y hy
    | _, rfl, _ => rfl
  rw [hsnoc hfu hyRoot] at hev hc'
  refine ⟨y, hy, s, hev, he'.symm, ?_, ?_⟩
  · intro d hnt
    by_cases hb : q.label d = ⊥
    · have he0 := hc'.1 d hb
      change min _ (W.stableValue u C c) = ⊥ at he0
      exact ((min_eq_bot.mp he0).resolve_right (ne_of_gt ((bot_lt_ofOrd _).trans hcut))).trans hb.symm
    · have he1 := hc'.2.1 d ⟨hb, hnt⟩
      rcases ExtOrd.cases (q.label d) with hb' | ht' | ⟨β, hβ⟩
      · exact (hb hb').elim
      · exact (hnt ht').elim
      obtain ⟨ho, hr⟩ : off (limitPart β) < C.scheme.scheme.grade c ∧
          W.stableValue u C (ref (limitPart β)).1 = ofOrd (limitPart β + off (limitPart β)) :=
        ⟨(href _ (hblocks d β hβ).1).1, (href _ (hblocks d β hβ).1).2.1⟩
      change min _ (W.stableValue u C c) = min (extVisibilityReplace
        (W.stableValue u C (ref (limitPart (ordOf (q.label d)))).1) (C.scheme.scheme.grade c)
          (finitePart (ordOf (q.label d)))) (W.stableValue u C c) at he1
      have hlt := (hproper d hnt).trans hcut
      rw [hβ, ordOf_ofOrd, hr, extVisibilityReplace_of_finitePart_lt
        (by rw [finitePart_limitPart_add_nat]; exact ho), limitPart_limitPart_add_nat,
        limitPart_add_finitePart, ← hβ, min_eq_left hlt.le] at he1
      exact eq_of_min_eq_of_lt' he1 hlt
  · intro d hd
    have he2 := hc'.2.2 d hd
    change min (extVisibilityReplace (W.stableValue u C a.1) (C.scheme.scheme.grade c) L)
      (W.stableValue u C c) ≤ min _ (W.stableValue u C c) at he2
    rw [ha, extVisibilityReplace_of_finitePart_lt
      (by rw [finitePart_add_nat_of_limit hαlim]; exact hi'),
      limitPart_add_nat_of_limit hαlim, min_eq_left hcut.le] at he2
    exact hγL.trans_le (he2.trans (min_le_left _ _))

private theorem of_positive {α : LimitStage} {M : Type w} {R : KnightRealization α M}
    (hne : Nonempty M) (hcons : R.IsExactParentConsistent) (hcover : R.IsInitialSegmentCovering)
    (hpos : ∀ {n : ℕ}, 0 < n → ∀ (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ q : S α.1 (n + 1), IsCoface p q →
        ∀ δ : ExtOrd, ⊥ < δ → δ < ofOrd α.1 →
          ∃ (y : M) (hy : y ∉ Set.range t) (r : S α.1 (n + 1)),
            R.eval (snoc t y hy) = some r ∧ ∃ he : r.scheme = q.scheme,
              ∀ d, min (r.label d) δ = min (q.label (SemScheme.castCell he d)) δ) :
    FiniteCutReceiving R := by
  intro n t p hp q hqp δ hδ hδα
  cases n with
  | succ n => exact hpos (Nat.succ_pos n) t p hp q hqp δ hδ hδα
  | zero =>
    obtain ⟨x⟩ := hne
    obtain ⟨k, u₀, _, hu₀⟩ := hcover ⟨fun _ : Fin 1 => x, fun a b _ => Subsingleton.elim a b⟩
    obtain ⟨P₀, hP₀⟩ := Option.isSome_iff_exists.mp hu₀
    have hh : ∃ (u : Fin (1 + k) ↪ M) (P : S α.1 (1 + k)), R.eval u = some P := ⟨u₀, P₀, hP₀⟩
    rw [Nat.add_comm 1 k] at hh
    obtain ⟨u, P, hP⟩ := hh
    obtain ⟨Q, hQP, hQq, _⟩ := exists_amalgam_point (CanonicalCoatomSupply.supply α.2)
      k (Fin.last (k + 1)) P q
    have hcof : IsCoface P Q := by
      change typeMap Fin.castSuccEmb Q = some P
      rwa [castSuccEmb_eq_succAboveEmb_last]
    obtain ⟨y, hy, ⟨rs, rl, rb, rr⟩, hr, he, hcap⟩ := hpos (Nat.succ_pos k) u P hP Q hcof δ hδ hδα
    dsimp only at he; subst rs
    let r : S α.1 (k + 2) := ⟨Q.scheme, rl, rb, rr⟩
    let f := pointEmb (Fin.last (k + 1))
    have hv : Finset.univ.image f ∈ Q.scheme.scheme.plan :=
      (typeMap_isSome_iff f Q).mp (by rw [hQq]; rfl)
    have heq : Q.restrictFace f hv = q :=
      Option.some.inj ((typeMap_eq_some f Q hv).symm.trans hQq)
    have hy0 : y ∉ Set.range t := fun ⟨i, _⟩ => i.elim0
    have htup : f.trans (snoc u y hy) = snoc t y hy0 := by
      ext i; obtain rfl : i = Fin.last 0 := Subsingleton.elim _ _
      change snoc u y hy (Fin.last (k + 1)) = snoc t y hy0 (Fin.last 0)
      simp only [snoc_apply_last]
    have hscheme := congrArg StageType.scheme heq
    change (r.restrictFace f hv).scheme = q.scheme at hscheme
    refine ⟨y, hy0, r.restrictFace f hv, ?_, hscheme, fun d => ?_⟩
    · rw [← htup, hcons _ r f hr]; exact typeMap_eq_some f r hv
    · refine (hcap (toCell Q.scheme.scheme f hv d)).trans (congrArg (fun x => min x δ) ?_)
      cases heq; rfl

private theorem stableLift_isModel {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hM : W.IsModel) (hh : ¬ W.IsHollow) (hg : W.HasTopGradeGrowth) :
    (stableLift hM).IsModel := by
  have hcons := stableLift_consistent hM
  have hcov := stableLift_covering hM
  refine FiniteCutReceiving.isModel (of_positive hM.nonempty hcons hcov ?_) hM.nonempty hcons hcov
  intro n hn t p hp q hqp δ hδ hδα
  obtain ⟨p₀, hp₀, rfl⟩ := stableLift_eval_eq_some hM hp
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.nextBlock.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact False.elim (lt_irrefl _ hδ)
    · exact False.elim ((not_lt_of_ge le_top) hδα)
    · exact ⟨ν, rfl, ofOrd_lt_ofOrd.mp hδα⟩
  obtain ⟨y, hy, s, hs, he, hproper, htop⟩ := receives_positive hM hh hg hn t p₀ hp₀ q hqp ν hν
  refine ⟨y, hy, stableLiftType hM _ s hs, stableLift_eval_some hM hs, he.symm, fun d => ?_⟩
  change min (W.stableValue (snoc t y hy) s d) (ofOrd ν) =
    min (q.label (SemScheme.castCell he.symm d)) (ofOrd ν)
  by_cases hd : q.label (SemScheme.castCell he.symm d) = ⊤
  · have hh := htop (SemScheme.castCell he.symm d) hd
    rw [hd, min_eq_right le_top]; exact min_eq_right hh.le
  · have hh := hproper (SemScheme.castCell he.symm d) hd
    exact congrArg (fun x => min x (ofOrd ν)) hh

theorem countableTerminalFibres : CountableTerminalFibres :=
  TopGradeTerminalCounting.countableTerminalFibres_of_growth_results
    (fun ρ _ W hh hg => by
      rw [prolongsToIn_isModelClass_iff_on]
      have hsucc : blockStage (ρ + 1) = (blockStage ρ).nextBlock := by
        apply Subtype.ext
        change blockLevel (ρ + 1) = blockLevel ρ + Ordinal.omega0
        have h := blockLevel_succ ρ
        rwa [Order.succ_eq_add_one] at h
      have hex : ∀ {β : LimitStage}, β = (blockStage ρ).nextBlock →
          ∀ hle : blockStage ρ ≤ β, W.1.ProlongsToOnIn IsModelClass hle
        | _, rfl, _ => ⟨stableLift W.2.1, stableLift_isModel W.2.1 hh hg, stableLift_reduct W.2.1⟩
      exact hex hsucc _)
    (fun _ _ W V hgW hgV hhW hhV => HollowGrowth.nonempty_iso W.2.1 V.2.1 hgW hgV hhW hhV)

end
end VaughtConjecture.Knight.ConstructedSpectrumEndpoint
