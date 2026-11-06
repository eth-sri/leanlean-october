/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLiftData
-- Ported from V-C 4d2e8cb. Only the unrelated model-side GuardActivation
-- import is removed; its scalar cancellation helper is proved locally.

/-! # The relative lifting theorem from one lawful reference template

The reviewer's notes3 relative lifting lemma (`guarded_probe_construction.md` §4), in full:
**every allowed pair has every relative old-face lift.**  Given an allowed pair `(u, v)`
(`RelativeData.Allowed`) and an arbitrary lawful replacement `u'` of the entire old face
agreeing with `u` below an `N`-visible cap `γ`, there is a lawful candidate labelling `v'`
with the literal root `u'|_B`, the same `γ`-reading as `v`, and `(u', v')` allowed
(`relative_lift`).  The four cases:

* **Case 0** — `u'` is outside the distinguished bottom-pattern class: install the new root by
  the candidate's bountifulness at `γ`; correctness is vacuous (`lift_case0`).
* **Case 1** — `u'` in the class, `c' = u'(C) ≤ γ`: the same lift; every relation at `c'` is
  retained since `c' ≤ γ`, `c'` is `N`-visible, and the references agree at `c'`
  (`correct_of_cap_le`).
* **Case 2** — in the class, `c' > γ`, high values requested, `d' = d(u') < γ`: the frame puts
  every exact value below `γ`, so the lift at `γ` fixes them literally; the high values keep a
  reading at least `d'` (`correct_of_dOf_lt`).
* **Case 3** — in the class, `c' > γ`, and no high values or `γ ≤ d'`: the **template image**
  `w = θ ∘ V` under the capped decoder of `u'` at the cap is lawful by same-bottom-pattern
  transport (long rows harmless: every reference is nonbottom in the class), has the
  `γ`-reading of `v`, and its root is `u'|_B ∧ c'`; the candidate's bountifulness at `c'`
  restores the literal root, retaining every `c'`-reading and hence the `γ`-reading
  (`template_image_respects`, `lift_case3`).  At `γ = ⊥` the `γ`-agreement is trivial and
  the lawfulness of `w` comes from its bottom pattern, not from a positive-cap argument.

The proof uses the **original candidate's** bountifulness and the template only; no
controller is added and no row changed.  Existence of the template and existence of the
legal guarded probe are separate conclusions, not supplied here.

**General cap (notes7).**  The cap is a full-scope grade-`N` cell of a possibly larger private
context; the pattern test, the donor and the decoder live on its lower domain, and the
correctness relations read only cells there (`Requests.sec`).  The marker reads at offset
`R < N`.  Cells above the cap are carried along untouched by `u'`, which is a lawful labelling
of the whole private scheme.  The selector's cap is retained by every lift
(`RelativeData.selector_cap_agree`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## Meets under nested caps -/

theorem min_cap_of_le {x x' c' γ : ExtOrd} (h : c' ≤ γ) (hag : min x γ = min x' γ) :
    min x c' = min x' c' := by
  calc min x c' = min (min x γ) c' := by rw [min_assoc, min_eq_right h]
    _ = min (min x' γ) c' := by rw [hag]
    _ = min x' c' := by rw [min_assoc, min_eq_right h]

theorem min_min_of_le {x c c' : ExtOrd} (h : c' ≤ c) : min (min x c) c' = min x c' := by
  rw [min_assoc, min_eq_right h]

/-- `min e c = v` with `v < c` forces `e = v`. -/
theorem eq_of_min_eq_of_lt' {e c v : ExtOrd} (h : min e c = v) (hv : v < c) : e = v :=
by
  rcases le_total e c with he | he
  · simpa only [min_eq_left he] using h
  · exact (hv.ne ((min_eq_right he).symm.trans h).symm).elim

namespace RelativeData

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

theorem correct_sec_iff (u : Cell DA → ExtOrd) (v : Cell DQ → ExtOrd) :
    X.req.Correct (X.req.sec u) v ↔
      (∀ z ∈ X.req.Z, min (v z) (u X.req.C) = ⊥) ∧
      (∀ f ∈ X.req.F, min (v f) (u X.req.C) = X.req.tOf (X.req.sec u) f) ∧
      ∀ y ∈ X.req.T, X.req.dOf (X.req.sec u) ≤ min (v y) (u X.req.C) := Iff.rfl

/-- **The relative lifting theorem** (notes3 §4): every allowed pair has every relative
old-face lift at every `N`-visible comparison cap, bottom included. -/
theorem relative_lift {u v u' : _} (hall : X.Allowed u v) (hu' : RespectsSemantics semA u')
    {γ : ExtOrd} (hγ : SelfVis X.req.N γ) (hag : ∀ d, min (u' d) γ = min (u d) γ) :
    ∃ v' : Cell DQ → ExtOrd, X.Allowed u' v' ∧ ∀ d, min (v' d) γ = min (v d) γ := by
  obtain ⟨hu, hv, hroot, hcorr⟩ := hall
  have hlift_γ := X.lift_root hu' hv hγ (fun r => by rw [hroot r]; exact (hag _).symm)
  by_cases hcls' : InClass X.ZA u'
  swap
  · obtain ⟨v', hv', hr', hcap⟩ := hlift_γ
    exact ⟨v', ⟨hu', hv', hr', fun h => absurd h hcls'⟩, hcap⟩
  obtain ⟨θ, hθ, hθle, hθe⟩ := X.decoder hu' hcls'
  have hc'ne := X.cap_ne_bot hcls'
  have hvisc' : SelfVis X.req.N (u' X.req.C) := X.grade_C ▸ (hu'.orderly X.req.C).symm
  have hclsu (hγne : γ ≠ ⊥) : InClass X.ZA u := fun d => by
    rw [← bottom_pattern_of_cap_agreement hγne hag d.1]; exact hcls' d
  have hR : X.req.R ≤ X.req.N := X.req.R_lt_N.le
  have htOf_cap {c : ExtOrd} (hc : SelfVis X.req.N c) (hc1 : c ≤ u' X.req.C) (hc2 : c ≤ u X.req.C)
      (hag_c : ∀ d, min (u' d) c = min (u d) c) {f : Cell DQ} (hf : f ∈ X.req.F) :
      min (X.req.tOf (X.req.sec u') f) c = min (X.req.tOf (X.req.sec u) f) c := by
    have hi := X.off_lt f hf
    change min (min (extVisibilityReplace (u' (X.req.ρ f).1) X.req.N (X.req.off f)) (u' X.req.C)) c =
      min (min (extVisibilityReplace (u (X.req.ρ f).1) X.req.N (X.req.off f)) (u X.req.C)) c
    rw [min_min_of_le hc1, min_min_of_le hc2, ← evr_min_of_selfVis hc le_rfl hi, hag_c,
      evr_min_of_selfVis hc le_rfl hi]
  have hdOf_cap {c : ExtOrd} (hc : SelfVis X.req.N c) (hc1 : c ≤ u' X.req.C) (hc2 : c ≤ u X.req.C)
      (hag_c : ∀ d, min (u' d) c = min (u d) c) :
      min (X.req.dOf (X.req.sec u')) c = min (X.req.dOf (X.req.sec u)) c := by
    change min (min (extVisibilityReplace (u' X.req.a.1) X.req.N X.req.R) (u' X.req.C)) c =
      min (min (extVisibilityReplace (u X.req.a.1) X.req.N X.req.R) (u X.req.C)) c
    rw [min_min_of_le hc1, min_min_of_le hc2, ← evr_min_of_selfVis hc le_rfl hR, hag_c,
      evr_min_of_selfVis hc le_rfl hR]
  by_cases hc'γ : u' X.req.C ≤ γ
  · -- Case 1
    have hγne : γ ≠ ⊥ := fun h => hc'ne (le_bot_iff.mp (h ▸ hc'γ))
    have hC := (X.correct_sec_iff u v).mp (hcorr (hclsu hγne))
    obtain ⟨v', hv', hr', hcap⟩ := hlift_γ
    have hc'c : u' X.req.C ≤ u X.req.C := by
      have h := hag X.req.C; rw [min_eq_left hc'γ] at h; exact h.trans_le (min_le_left _ _)
    have hag_c' (d) : min (u' d) (u' X.req.C) = min (u d) (u' X.req.C) :=
      min_cap_of_le hc'γ (hag d)
    refine ⟨v', ⟨hu', hv', hr', fun _ => (X.correct_sec_iff u' v').mpr
      ⟨fun z hz => ?_, fun f hf => ?_, fun y hy => ?_⟩⟩, hcap⟩
    · rw [min_cap_of_le hc'γ (hcap z), ← min_min_of_le hc'c, hC.1 z hz, min_eq_left bot_le]
    · rw [min_cap_of_le hc'γ (hcap f), ← min_min_of_le hc'c, hC.2.1 f hf,
        ← htOf_cap hvisc' le_rfl hc'c hag_c' hf]
      exact min_eq_left (min_le_right _ _)
    · rw [min_cap_of_le hc'γ (hcap y), ← min_min_of_le hc'c]
      exact (min_eq_left (min_le_right _ _)).symm.trans_le
        ((hdOf_cap hvisc' le_rfl hc'c hag_c').le.trans (min_le_min_right _ (hC.2.2 y hy)))
  have hγc' : γ < u' X.req.C := not_le.mp hc'γ
  have hθ_cap : θ (X.e X.req.capCell) = u' X.req.C := by
    rw [hθe, Requests.sec_capCell, min_self]
  have hθ_tOf {f : Cell DQ} (hf : f ∈ X.req.F) :
      θ (X.req.tOf X.e f) = X.req.tOf (X.req.sec u') f := by
    change θ (min (extVisibilityReplace (X.e (X.req.ρ f)) X.req.N (X.req.off f)) (X.e X.req.capCell)) =
      min (extVisibilityReplace (u' (X.req.ρ f).1) X.req.N (X.req.off f)) (u' X.req.C)
    rw [hθ.mono.map_min, hθ.comm _ X.req.N _ le_rfl (X.off_lt f hf), hθ_cap, hθe,
      Requests.sec_apply, evr_min_of_selfVis hvisc' le_rfl (X.off_lt f hf), min_assoc, min_self]
  have hθ_dOf : θ (X.req.dOf X.e) = X.req.dOf (X.req.sec u') := by
    change θ (min (extVisibilityReplace (X.e X.req.a) X.req.N X.req.R) (X.e X.req.capCell)) =
      min (extVisibilityReplace (u' X.req.a.1) X.req.N X.req.R) (u' X.req.C)
    rw [hθ.mono.map_min, hθ.comm _ X.req.N _ le_rfl hR, hθ_cap, hθe,
      Requests.sec_apply, evr_min_of_selfVis hvisc' le_rfl hR, min_assoc, min_self]
  by_cases hcase2 : X.req.T.Nonempty ∧ X.req.dOf (X.req.sec u') < γ
  · -- Case 2
    obtain ⟨hT, hd'⟩ := hcase2
    have hγne : γ ≠ ⊥ := ne_bot_of_gt hd'
    have hcls := hclsu hγne
    have hC := (X.correct_sec_iff u v).mp (hcorr hcls)
    have hcne := X.cap_ne_bot hcls
    have hcγ : γ ≤ u X.req.C := by
      have h := hag X.req.C; rw [min_eq_right hγc'.le] at h; exact min_eq_right_iff.mp h.symm
    obtain ⟨v', hv', hr', hcap⟩ := hlift_γ
    refine ⟨v', ⟨hu', hv', hr', fun _ => (X.correct_sec_iff u' v').mpr
      ⟨fun z hz => ?_, fun f hf => ?_, fun y hy => ?_⟩⟩, hcap⟩
    · have hvz : v z = ⊥ := (min_eq_bot.mp (hC.1 z hz)).resolve_right hcne
      have h := hcap z; rw [hvz, min_eq_left bot_le] at h
      rw [(min_eq_bot.mp h).resolve_right hγne, min_eq_left bot_le]
    · have ht' : X.req.tOf (X.req.sec u') f < γ := by
        rw [← hθ_tOf hf]; rw [← hθ_dOf] at hd'
        exact (hθ.mono (X.frame hT f hf)).trans_lt hd'
      have hmin : min (v' f) γ = X.req.tOf (X.req.sec u') f := by
        rw [hcap f, ← min_min_of_le hcγ, hC.2.1 f hf, ← htOf_cap hγ hγc'.le hcγ hag hf,
          min_eq_left ht'.le]
      rw [eq_of_min_eq_of_lt' hmin ht', min_eq_left (ht'.trans hγc').le]
    · have h1 : X.req.dOf (X.req.sec u') ≤ min (v' y) γ := by
        rw [hcap y, ← min_min_of_le hcγ, ← min_eq_left hd'.le, hdOf_cap hγ hγc'.le hcγ hag]
        exact min_le_min_right _ (hC.2.2 y hy)
      exact le_min (h1.trans (min_le_left _ _)) (hd'.trans hγc').le
  -- Case 3
  have hT (hT : X.req.T.Nonempty) : γ ≤ X.req.dOf (X.req.sec u') :=
    not_lt.mp fun h => hcase2 ⟨hT, h⟩
  set w : Cell DQ → ExtOrd := fun d => θ (X.V d)
  have hwle (d) : w d ≤ u' X.req.C := hθle _
  have himg_tOf {f : Cell DQ} (hf : f ∈ X.req.F) :
      min (w f) (u' X.req.C) = X.req.tOf (X.req.sec u') f := by
    change min (θ (X.V f)) (u' X.req.C) = _
    rw [← hθ_cap, ← hθ.mono.map_min, X.V_correct.2.1 f hf, hθ_tOf hf]
  have himg_dOf {y : Cell DQ} (hy : y ∈ X.req.T) :
      X.req.dOf (X.req.sec u') ≤ min (w y) (u' X.req.C) := by
    change _ ≤ min (θ (X.V y)) (u' X.req.C)
    rw [← hθ_cap, ← hθ.mono.map_min, ← hθ_dOf]
    exact hθ.mono (X.V_correct.2.2 y hy)
  have hV_bot {z : Cell DQ} (hz : z ∈ X.req.Z) : X.V z = ⊥ :=
    (min_eq_bot.mp (X.V_correct.1 z hz)).resolve_right fun h => X.C_notin ((X.e_bot _).mp h)
  have himg_root (r : DQ.below X.root) : w r.1 = min (u' (X.κ r).1) (u' X.req.C) := by
    change θ (X.V r.1) = _; rw [X.V_root r, hθe, Requests.sec_apply]
  have hwr : RespectsSemantics semQ w := by
    refine RespectsSemantics.of_below_top X.below_top
      (map_respects_of_same_bottom_pattern (X.V_respects.toBelow X.top)
        (X.V_respects.toBelow X.top) (fun d => X.grade_le d.1) hθ fun d => ⟨fun h => ?_, fun h => ?_⟩)
    · rcases X.cover d.1 with hz | hf | hy | ⟨r, hr⟩
      · exact hV_bot hz
      · have h1 : X.req.tOf (X.req.sec u') d.1 = ⊥ := by
          have h0 := (himg_tOf hf).symm; rwa [show w d.1 = ⊥ from h, min_eq_left bot_le] at h0
        rcases min_eq_bot.mp h1 with h2 | h2
        · exact (X.ρ_notin _ hf ((hcls' _).mp ((evr_eq_bot_iff _ _).mp h2))).elim
        · exact (hc'ne h2).elim
      · have h1 : X.req.dOf (X.req.sec u') = ⊥ := by
          have h0 := himg_dOf hy; rwa [show w d.1 = ⊥ from h, min_eq_left bot_le, le_bot_iff] at h0
        rcases min_eq_bot.mp h1 with h2 | h2
        · exact (X.a_notin ((hcls' _).mp ((evr_eq_bot_iff _ _).mp h2))).elim
        · exact (hc'ne h2).elim
      · have h' : min (u' (X.κ r).1) (u' X.req.C) = ⊥ :=
          (himg_root r).symm.trans (congrArg w hr ▸ h)
        rcases min_eq_bot.mp h' with h2 | h2
        · exact congrArg X.V hr ▸ (X.V_root r).trans ((X.e_bot _).mpr ((hcls' _).mp h2))
        · exact (hc'ne h2).elim
    · rw [h, hθ.bot]
  obtain ⟨v', hv', hr', hcap'⟩ := X.lift_root hu' hwr hvisc'
    (fun r => by rw [himg_root r, min_assoc, min_self])
  have hcapw (d) : min (v' d) (u' X.req.C) = w d := (hcap' d).trans (min_eq_left (hwle d))
  refine ⟨v', ⟨hu', hv', hr', fun _ => (X.correct_sec_iff u' v').mpr
    ⟨fun z hz => ?_, fun f hf => ?_, fun y hy => ?_⟩⟩, fun d => ?_⟩
  · rw [hcapw z]; change θ (X.V z) = ⊥; rw [hV_bot hz, hθ.bot]
  · rw [hcapw f, ← himg_tOf hf, min_eq_left (hwle f)]
  · rw [hcapw y]; exact (himg_dOf hy).trans (min_le_left _ _)
  · rw [← min_min_of_le hγc'.le (x := v' d), hcapw d]
    rcases eq_or_ne γ ⊥ with rfl | hγne
    · simp
    have hcls := hclsu hγne
    have hC := (X.correct_sec_iff u v).mp (hcorr hcls)
    have hcne := X.cap_ne_bot hcls
    have hcγ : γ ≤ u X.req.C := by
      have h := hag X.req.C; rw [min_eq_right hγc'.le] at h; exact min_eq_right_iff.mp h.symm
    rcases X.cover d with hz | hf | hy | ⟨r, hr⟩
    · have h1 : w d = ⊥ := by change θ (X.V d) = ⊥; rw [hV_bot hz, hθ.bot]
      rw [h1, (min_eq_bot.mp (hC.1 d hz)).resolve_right hcne]
    · rw [← min_min_of_le hγc'.le (x := w d), himg_tOf hf, htOf_cap hγ hγc'.le hcγ hag hf,
        ← hC.2.1 d hf, min_min_of_le hcγ]
    · have hγd := hT ⟨d, hy⟩
      have hu'a : γ ≤ u' X.req.a.1 := le_of_le_evr hγ X.req.R_lt_N (hγd.trans (min_le_left _ _))
      have hua : γ ≤ u X.req.a.1 := by
        have h := hag X.req.a.1; rw [min_eq_right hu'a] at h; exact min_eq_right_iff.mp h.symm
      have hdu : γ ≤ X.req.dOf (X.req.sec u) :=
        le_min (le_evr_of_le hγ hua _) hcγ
      rw [min_eq_right (hγd.trans ((himg_dOf hy).trans (min_le_left _ _))),
        min_eq_right (hdu.trans ((hC.2.2 d hy).trans (min_le_left _ _)))]
    · rw [← hr, himg_root r, min_min_of_le hγc'.le, hag, hroot r]

