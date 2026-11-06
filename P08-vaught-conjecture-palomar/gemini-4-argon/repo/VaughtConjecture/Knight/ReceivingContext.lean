/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingTemplate

/-! # The receiving template from an actual receiving context

The reviewer's notes7 (`mixed_proper_top_charts.md` §6, 2026-09-19), at the level of the
finite schemes: from the actual private labelling `u₀` reading a full-scope grade-`N` cap
`C` at `⊤`, the cap's row, one old reference per block of the candidate's proper values
(labelled in that block with offset below `N`), a top marker `a`, and a lawful candidate `P`
extending the root literally, the theorem `exists_relativeData_of_context` **produces** the
relative data: the cleaned donor, the source strips, the block code, the encoded candidate,
and the literal root restoration.  The remaining model-side input is one clause:

* **the one-row criterion** (`htoproot`): a top-labelled root cell's source dominates the
  marker's offset-`R` replacement.  `ProvisionalCap.transport` supplies the intermediate
  inequality `R_{N,N}(E_C Σ) ≤ E_C d` for a provisionally capped `d` and some top source `Σ`;
  it does not construct the joint context in which the marker is a *least* top source and
  every top root cell is provisionally capped.  A least-top-source marker is a sufficient
  route, not necessarily the weakest requirement.  Stable-top fixedness or effective-anchor
  data do not discharge `htoproot` until that context-selection theorem is proved.

**Proper-root alignment is derived, not assumed.**  Every proper candidate label has offset
below `N` (`hblocks`), so a proper root cell's source sits on an *affine* strip of the reading
witness, and two distinct strips cannot both map affinely onto one block
(`strip_unique_of_read`): the root cell's source is its block's reference strip at its own
offset.  The earlier hypothesis `halign` is now a lemma inside the proof.  The grade-one
merging regression (`TemplateRegression.no_scalar_root`) has a value whose offset equals the
grade, outside this offset bound; it shows the bound is necessary, not that alignment fails
under it.

The reading witness `τ` of the cap's row (`exists_exact_capped_shifter`) yields the source
facts used: a source read to a proper value with offset below `N` has the same offset
(`read_finitePart`), readings in different blocks come from different strips, in order
(`strip_lt_of_read`), readings in the same block come from the same strip
(`strip_unique_of_read`), and every such strip plus `N` lies below the offset-`R` replacement
of a source read to `⊤` (`strip_add_le_of_read_top`).

Not here: obtaining the context itself (references by uniformity, provisional bounds for the
root's top cells and one private stably-top occurrence, `N = topGrade`) from the model
clauses; that is the model-side supply, stated in `docs/STATUS.md`.

Construction-private (not root-exported). -/

@[expose] public noncomputable section

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
  have key (i) (hi : i ≤ N) : τ (extVisibilityReplace (ofOrd s) N i) = ofOrd (limitPart t + i) := by
    rw [hτ.comm _ N i le_rfl hi, h, extVisibilityReplace_of_finitePart_lt ht]
  have hlt : finitePart s < N := by
    by_contra hge
    have h1 := key (finitePart t) ht.le
    have h2 := key (finitePart t + 1) ht
    rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hge)] at h1 h2
    exact (Nat.succ_ne_self _).symm (Nat.cast_injective (add_left_cancel (ofOrd_inj.mp (h1 ▸ h2))))
  refine ⟨hlt, ?_⟩
  have h1 := key (finitePart s) hlt.le
  rw [extVisibilityReplace_of_finitePart_lt hlt, limitPart_add_finitePart, h, ofOrd_inj] at h1
  simpa [finitePart_limitPart_add_nat] using (congrArg finitePart h1).symm

include hτ in
/-- Two proper readings with offsets below `N` in different blocks come from different
strips, in the same order. -/
theorem strip_lt_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (hlt : limitPart t < limitPart t') : limitPart s < limitPart s' := by
  have hss' : s < s' := not_le.mp fun hle => by
    have := hτ.mono (ofOrd_le_ofOrd.mpr hle)
    rw [h, h', ofOrd_le_ofOrd] at this
    exact hlt.not_ge (limitPart_mono this)
  rcases (limitPart_mono hss'.le).lt_or_eq with hlt' | heq
  · exact hlt'
  have k1 := hτ.comm (ofOrd s) N 0 le_rfl (Nat.zero_le _)
  have k2 := hτ.comm (ofOrd s') N 0 le_rfl (Nat.zero_le _)
  rw [extVisibilityReplace_of_finitePart_lt (read_finitePart hτ h ht).1, h,
    extVisibilityReplace_of_finitePart_lt ht, Nat.cast_zero, add_zero, add_zero, heq] at k1
  rw [extVisibilityReplace_of_finitePart_lt (read_finitePart hτ h' ht').1, h',
    extVisibilityReplace_of_finitePart_lt ht', Nat.cast_zero, add_zero, add_zero, k1, ofOrd_inj] at k2
  exact (hlt.ne k2).elim

include hτ in
/-- **Strip uniqueness**: two proper readings with offsets below `N` in the *same* block come
from the same strip.  Both sources sit on affine strips through offset `N`; if the strips
differed, the lower strip's `N`-endpoint would map at or below the upper strip's floor. -/
theorem strip_unique_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (heq : limitPart t = limitPart t') : limitPart s = limitPart s' := by
  have key (s t : Ordinal.{0}) (h : τ (ofOrd s) = ofOrd t) (ht : finitePart t < N)
      (i) (hi : i ≤ N) : τ (ofOrd (limitPart s + i)) = ofOrd (limitPart t + i) := by
    have k := hτ.comm (ofOrd s) N i le_rfl hi
    rwa [extVisibilityReplace_of_finitePart_lt (read_finitePart hτ h ht).1, h,
      extVisibilityReplace_of_finitePart_lt ht] at k
  have one (s s' t t' : Ordinal.{0}) (h : τ (ofOrd s) = ofOrd t) (h' : τ (ofOrd s') = ofOrd t')
      (ht : finitePart t < N) (ht' : finitePart t' < N) (heq : limitPart t = limitPart t')
      (hlt : limitPart s < limitPart s') : False := by
    have h1 := key s t h ht N le_rfl
    have h2 := key s' t' h' ht' 0 (Nat.zero_le _)
    rw [Nat.cast_zero, add_zero, add_zero] at h2
    have hm := hτ.mono (ofOrd_le_ofOrd.mpr
      (add_nat_lt_of_lt_limit (limitPart_idem s) (limitPart_idem s') hlt N).le)
    rw [h1, h2, ofOrd_le_ofOrd, ← heq] at hm
    have : (N : Ordinal.{0}) ≤ 0 := le_of_add_le_add_left (by rwa [add_zero])
    exact not_le_of_gt (lt_of_le_of_lt (Nat.zero_le _) ht) (Nat.cast_le.mp this)
  rcases lt_trichotomy (limitPart s) (limitPart s') with hlt | heq' | hgt
  · exact (one s s' t t' h h' ht ht' heq hlt).elim
  · exact heq'
  · exact (one s' s t' t h' h ht' ht heq.symm hgt).elim

include hτ in
/-- Below a source read to `⊤`: its offset-`R` replacement is a proper `R`-visible value, and
every strip of a proper reading with offset below `N`, plus `N`, lies at most there. -/
theorem strip_add_le_of_read_top {sa : Ordinal.{0}} (ha : τ (ofOrd sa) = ⊤) (R : ℕ)
    (hR : R < N) :
    ∃ h : Ordinal.{0}, extVisibilityReplace (ofOrd sa) N R = ofOrd h ∧ R ≤ finitePart h ∧
      ∀ s t : Ordinal.{0}, τ (ofOrd s) = ofOrd t → finitePart t < N →
        limitPart s + N ≤ h := by
  have hss {s t} (h : τ (ofOrd s) = ofOrd t) : s < sa := not_le.mp fun hle => by
    have := hτ.mono (ofOrd_le_ofOrd.mpr hle)
    rw [h, ha] at this
    exact not_top_le_ofOrd t this
  by_cases hfa : finitePart sa < N
  · refine ⟨limitPart sa + R, extVisibilityReplace_of_finitePart_lt hfa R,
      by rw [finitePart_limitPart_add_nat], fun s t h ht => ?_⟩
    rcases (limitPart_mono (hss h).le).lt_or_eq with hlt | heq
    · exact (limitPart_add_nat_le_of_lt hlt N).trans le_self_add
    · have k1 := hτ.comm (ofOrd s) N 0 le_rfl (Nat.zero_le _)
      have k2 := hτ.comm (ofOrd sa) N 0 le_rfl (Nat.zero_le _)
      rw [extVisibilityReplace_of_finitePart_lt (read_finitePart hτ h ht).1, h,
        extVisibilityReplace_of_finitePart_lt ht, heq] at k1
      rw [extVisibilityReplace_of_finitePart_lt hfa, ha, extVisibilityReplace_top, k1] at k2
      exact (ofOrd_ne_top _ k2).elim
  · have hfa' := not_lt.mp hfa
    refine ⟨sa, extVisibilityReplace_of_le_finitePart hfa' R, hR.le.trans hfa', fun s t h _ => ?_⟩
    calc limitPart s + (N : Ordinal.{0}) ≤ limitPart sa + (finitePart sa : Ordinal.{0}) :=
          add_le_add (limitPart_mono (hss h).le) (Nat.cast_le.mpr hfa')
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
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := DA.below (DA.cell req.C)) (grade := fun d => DA.grade d.1) (p := fun d => u₀ d.1)
    (c := req.capCell) (fun d => d.2.2) (hu₀.orderly req.C).symm (hu₀.locality req.C)
  have hτ : BoundedMap req.N τ :=
    ⟨hbot, hmono, fun x k i hk hi =>
      hcomm x k i (by change k ≤ DA.grade req.C; rw [grade_C]; exact hk) hi⟩
  have hread' (d : DA.below (DA.cell req.C)) : τ (semA.E req.C d) = u₀ d.1 := by
    rw [hread d]
    change min (u₀ d.1) (u₀ req.C) = u₀ d.1
    rw [hC, min_top_right]
  have hτtop : τ ⊤ = ⊤ :=
    top_le_iff.mp (hC.symm.le.trans ((hread' req.capCell).symm.le.trans (hmono le_top)))
  set e : DA.below (DA.cell req.C) → ExtOrd :=
    fun d => if u₀ d.1 = ⊥ then ⊥ else semA.E req.C d
  have he : RespectsSemanticsBelow semA (DA.cell req.C) e :=
    cleaned_respects_of_bottom_agreement hrow (hu₀.toBelow _)
      (fun d => d.2.2.trans_eq grade_C) hτ (fun d => by rw [hread' d])
  have he_eq (d) (h : u₀ d.1 ≠ ⊥) : e d = semA.E req.C d := ite_eq_right h
  have hsa : semA.E req.C req.a = ofOrd (ordOf (semA.E req.C req.a)) :=
    (ofOrd_ordOf (fun h0 => top_ne_bot (ha_top ▸ hbot ▸ h0 ▸ (hread' req.a).symm)) ha_ne_top).symm
  obtain ⟨h, hh, hRh, hstrip⟩ :=
    strip_add_le_of_read_top hτ (by rw [← hsa, hread', ha_top]) req.R req.R_lt_N
  have hordOf (d) {p} (hu : u₀ d.1 = ofOrd p) :
      semA.E req.C d = ofOrd (ordOf (semA.E req.C d)) ∧
      τ (ofOrd (ordOf (semA.E req.C d))) = ofOrd p := by
    have h : semA.E req.C d = ofOrd (ordOf (semA.E req.C d)) :=
      (ofOrd_ordOf (fun h0 => ofOrd_ne_bot p (hu ▸ hbot ▸ h0 ▸ (hread' d).symm))
        (fun h0 => ofOrd_ne_top p (hu ▸ hτtop ▸ h0 ▸ (hread' d).symm))).symm
    exact ⟨h, h ▸ (hread' d).trans hu⟩
  set strip : Ordinal.{0} → Ordinal.{0} := fun μ => limitPart (ordOf (semA.E req.C (ref μ)))
  have hsrc' (μ) (hμ : μ ∈ S) : ∃ j < req.N,
      τ (ofOrd (ordOf (semA.E req.C (ref μ)))) = ofOrd (μ + j) := by
    obtain ⟨j, hjN, hj⟩ := href μ hμ
    exact ⟨j, hjN, (hordOf (ref μ) hj).2⟩
  have hfpμ (μ) (hμ : μ ∈ S) (j : ℕ) : finitePart (μ + (j : Ordinal.{0})) = j :=
    finitePart_add_nat_of_limit (hS μ hμ) j
  have hlpμ (μ) (hμ : μ ∈ S) (j : ℕ) : limitPart (μ + (j : Ordinal.{0})) = μ :=
    limitPart_add_nat_of_limit (hS μ hμ) j
  have hlim (μ) (_ : μ ∈ S) : limitPart (strip μ) = strip μ := limitPart_idem _
  have hle (μ) (hμ : μ ∈ S) : strip μ + req.N ≤ h := by
    obtain ⟨j, hjN, hτs⟩ := hsrc' μ hμ
    exact hstrip _ _ hτs (by rw [hfpμ μ hμ]; exact hjN)
  have hstrict (μ) (hμ : μ ∈ S) (μ') (hμ' : μ' ∈ S) (hlt : μ < μ') : strip μ < strip μ' := by
    obtain ⟨j, hjN, hτs⟩ := hsrc' μ hμ
    obtain ⟨j', hjN', hτs'⟩ := hsrc' μ' hμ'
    exact strip_lt_of_read hτ hτs hτs' (by rw [hfpμ μ hμ]; exact hjN)
      (by rw [hfpμ μ' hμ']; exact hjN') (by rw [hlpμ μ hμ, hlpμ μ' hμ']; exact hlt)
  set B : BlockCode := BlockCode.ofFinset req.N req.R req.R_lt_N S strip h hlim hle hstrict hRh
  have hBtop : B.code ⊤ = ofOrd h := rfl
  have hcode (p) (hp : limitPart p ∈ S) (hfp : finitePart p ≤ req.N) :
      B.code (ofOrd p) = ofOrd (strip (limitPart p) + finitePart p) :=
    B.code_listed hp
      (BlockCode.ofFinset_Λ_listed req.N req.R req.R_lt_N S strip h hlim hle hstrict hRh hp) hfp
  have hevr (μ) (hμ : μ ∈ S) (i) : extVisibilityReplace (semA.E req.C (ref μ)) req.N i =
      ofOrd (strip μ + i) := by
    obtain ⟨j, hjN, hj⟩ := href μ hμ
    obtain ⟨hs, hτs⟩ := hordOf (ref μ) hj
    rw [hs, extVisibilityReplace_of_finitePart_lt
      (read_finitePart hτ hτs (by rw [hfpμ μ hμ]; exact hjN)).1]
  have ha_ne' : u₀ req.a.1 ≠ ⊥ := by rw [ha_top]; exact top_ne_bot
  have hh' : extVisibilityReplace (e req.a) req.N req.R = ofOrd h := by
    rw [he_eq _ ha_ne', hsa]; exact hh
  have hvish : SelfVis req.R (extVisibilityReplace (e req.a) req.N req.R) := by
    rw [hh']; exact extVisibilityReplace_of_le_finitePart hRh _
  have hbotP (d) (hd : B.code (P d) = ⊥) : P d = ⊥ := by
    rcases ExtOrd.cases (P d) with h0 | h0 | ⟨p, h0⟩
    · exact h0
    · rw [h0, hBtop] at hd; exact absurd hd (ofOrd_ne_bot _)
    · obtain ⟨hp, hfp⟩ := hblocks d p h0
      rw [h0, hcode p hp hfp.le] at hd
      exact absurd hd (ofOrd_ne_bot _)
  have hroot_cap (r : DQ.below root) :
      min (B.code (P r.1)) (ofOrd h) = min (e (κ r)) (ofOrd h) := by
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
      obtain ⟨hs, hτs⟩ := hordOf (κ r) h0
      obtain ⟨j, hjN, hτref⟩ := hsrc' _ hp
      have hlp : limitPart (ordOf (semA.E req.C (κ r))) = strip (limitPart p) :=
        strip_unique_of_read hτ hτs hτref hfp (by rw [hfpμ _ hp]; exact hjN) (by rw [hlpμ _ hp])
      rw [hP0, hcode p hp hfp.le, he_eq _ (by rw [h0]; exact ofOrd_ne_bot _), hs, ← hlp,
        ← (read_finitePart hτ hτs hfp).2, limitPart_add_finitePart]
  have hρ_ne (f) (hf : f ∈ req.F) : u₀ (req.ρ f).1 ≠ ⊥ := by
    obtain ⟨p, hPf, hρ, -⟩ := hF f hf
    obtain ⟨j, -, hj⟩ := href _ (hblocks f p hPf).1
    rw [hρ, hj]; exact ofOrd_ne_bot _
  have hF' (f) (hf : f ∈ req.F) : B.code (P f) =
      extVisibilityReplace (e (req.ρ f)) req.N (req.off f) := by
    obtain ⟨p, hPf, hρ, hoff⟩ := hF f hf
    obtain ⟨hp, hfp⟩ := hblocks f p hPf
    rw [hPf, hcode p hp hfp.le, he_eq _ (hρ_ne f hf), hρ, hoff, hevr _ hp]
  have hFlt (f) (hf : f ∈ req.F) : extVisibilityReplace (e (req.ρ f)) req.N (req.off f) <
      extVisibilityReplace (e req.a) req.N req.R := by
    obtain ⟨p, hPf, hρ, hoff⟩ := hF f hf
    obtain ⟨hp, hfp⟩ := hblocks f p hPf
    rw [he_eq _ (hρ_ne f hf), hρ, hoff, hevr _ hp, hh', ofOrd_lt_ofOrd]
    exact ((add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hfp)).trans_le (hle _ hp)
  have hT' (y) (hy : y ∈ req.T) : B.code (P y) = extVisibilityReplace (e req.a) req.N req.R := by
    rw [hT y hy, hBtop, hh']
  have ha_ne : e req.a ≠ ⊥ := by rw [he_eq _ ha_ne', hsa]; exact ofOrd_ne_bot _
  obtain ⟨V, hVr, hVroot, hVcorr, hframe, hVF, hVT, hVZ⟩ := template_of_encoding_capped req e he
    ha_ne hP root_mem top_mem root_le root_ne below_top top_le_R κ hroot bountiful
    B.boundedMap_code hbotP hvish (by rw [hh']; exact hroot_cap) hZ hF' hFlt hT'
  have hoff_lt (f) (hf : f ∈ req.F) : req.off f ≤ req.N := by
    obtain ⟨p, hPf, -, hoff⟩ := hF f hf
    rw [hoff]; exact (hblocks f p hPf).2.le
  exact ⟨mkRelativeData req grade_C hrow hu₀ hC ha_ne' hρ_ne hoff_lt root_mem top_mem root_le
    root_ne below_top (top_le_R.trans req.R_lt_N.le) κ hroot bountiful cover V hVr hVroot hVcorr
    hframe, rfl, rfl, rfl, HEq.rfl, HEq.rfl, fun _ => rfl,
    fun f hf => he_eq _ (hρ_ne f hf) ▸ hVF f hf,
    fun y hy => he_eq _ ha_ne' ▸ hVT y hy, hVZ⟩
