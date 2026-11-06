module

public import Chazelle.Core.OracleDeg

/-!
# Lemma 3.6 (WP-H), part 21: the ray up to the stopping point

Two facts of the main phase of the query:

* `chord_free`: before the chord next to the origin (the first chord at the ray's height ahead
  of the effective origin `ζ`), the ray meets no chord of the normal form.
* `cand_of_stop`: every arc whose closed point set contains the stopping point is a candidate:
  the arc located for one of the four walk positions of the stopping point, or its successor or
  predecessor on the spine.
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)

@[expose] public section

variable {P : Polygon} {C : Chain} {V : QV} {m : ℕ → ℕ} {N : NF}

/-- **The chord table lists every chord.** -/
theorem ChordRecOK.surj (h : ChordRecOK P C V m N) {i : ℕ} (hi : i < V.K) :
    ∃ q, q < V.K ∧ chAt m V q = i := by
  classical
  have hsub : (Finset.range V.K).image (chAt m V) ⊆ Finset.range V.K := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (h.lt q (Finset.mem_range.1 hq))
  have hcard : ((Finset.range V.K).image (chAt m V)).card = V.K := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact h.inj a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have : i ∈ (Finset.range V.K).image (chAt m V) := by rw [heq]; exact Finset.mem_range.2 hi
  obtain ⟨q, hq, hqi⟩ := Finset.mem_image.1 this
  exact ⟨q, Finset.mem_range.1 hq, hqi⟩

/-- **No chord before the stopping point.** -/
theorem chord_free (h : ChordRecOK P C V m N) {z : Point} (hs : SemOK P C V z)
    (hnp : NotPast C V z) {t : ℕ} (hpart : PartC P C V m t) {x : ℝ}
    (h1 : 0 < sgnOf V.σb * (x - ζOf C V z))
    (h2 : FoundC V m t → sgnOf V.σb * (x - xv P C V (nearC V m t) V.hz) < 0) :
    ((x, ((Qof P).vtx V.hz).2) : Point) ∉ ⋃₀ N.F (chainModel C) (Qof P) := by
  rintro ⟨c, ⟨r, hr, rfl⟩, hmem⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hiK : i < V.K := by rw [h.K]; exact hi
  have hrec : N.chords[i] = N.chord i := by unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]
  rw [hrec] at hmem
  obtain ⟨q, hq, rfl⟩ := h.surj hiK
  obtain ⟨hhn, -, hC, hS, EL, ER⟩ := h.facts (h.lt q hq)
  rw [hS] at hmem
  obtain ⟨hy, hxa, hxb⟩ := hmem
  simp only at hy hxa hxb
  have hhz : chH m V (chAt m V q) = V.hz :=
    ((heights_ne h.hT hhn hs.hv.hz_lt).1 hy.symm)
  rw [hhz] at hxa hxb EL ER hC
  obtain ⟨ht, hpre, hpost⟩ := hpart
  by_cases hσ : V.σb = 1
  · rw [sgnOf_one hσ, one_mul] at h1
    rw [sgnOf_one hσ, one_mul] at h2
    by_cases hqt : q < t
    · -- behind the origin: the right end is not ahead
      have := hpre q hqt
      rw [chPr_iff] at this
      rcases this.2 with h' | ⟨-, h', -⟩
      · omega
      · have hb := not_lt.1 (fun hh => h' hσ ((endGtZ_iff hσ hs.zo hnp ER.good).2 hh))
        linarith
    · -- ahead: the chord at `t` is found, and its left end is not after ours
      push Not at hqt
      have htK : t < V.K := by omega
      have hle := h.sorted t q hqt hq
      have hnot := hpost htK
      rw [← Bool.not_eq_true, chPr_iff] at hnot
      have hHt : chH m V (chAt m V t) = V.hz := by
        rcases hle with hlt | ⟨hh, -⟩
        · by_contra hne
          exact hnot ⟨h.lt t htK, Or.inl (by omega)⟩
        · rw [hh, hhz]
      have hf : FoundC V m t := by
        refine ⟨by rw [ite_eq_left hσ]; exact htK, ?_⟩
        unfold jCOf; rw [ite_eq_left hσ]; exact hHt
      have hnear := h2 hf
      unfold nearC jCOf at hnear; rw [ite_eq_left hσ, ite_eq_left hσ] at hnear
      obtain ⟨-, -, -, -, ELt, -⟩ := h.facts (h.lt t htK)
      have hx := chLe_xv ELt.good (by rw [hhz]; exact EL.good) hle (by rw [hHt, hhz])
      rw [hHt, hhz] at hx
      linarith
  · rw [sgnOf_ne hσ] at h1 h2
    by_cases hqt : t ≤ q
    · -- behind the origin: the left end is not ahead (the predicate fails from `t` on)
      have hnot : chPr P C V m (chAt m V q) = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have := chPr_mono h t q hqt hq hc
        rw [hpost (by omega)] at this; exact Bool.false_ne_true this
      rw [← Bool.not_eq_true, chPr_iff] at hnot
      have ha : ¬ EndLtZ P C V (chL m V (chAt m V q)) V.hz := fun hh =>
        hnot ⟨h.lt q hq, Or.inr ⟨hhz, fun h' => absurd h' hσ, fun _ => hh⟩⟩
      have ha' := not_lt.1 (fun hh => ha ((endLtZ_iff hσ hs.zo hnp EL.good).2 hh))
      linarith
    · push Not at hqt
      have hle := h.sorted q (t - 1) (by omega) (by omega)
      have hpt := hpre (t - 1) (by omega)
      rw [chPr_iff] at hpt
      have hHt : chH m V (chAt m V (t - 1)) = V.hz := by
        rcases hle with hlt | ⟨hh, -⟩
        · rcases hpt.2 with h' | ⟨h', -⟩ <;> omega
        · rw [← hh, hhz]
      have hf : FoundC V m t := by
        refine ⟨by rw [ite_eq_right hσ]; omega, ?_⟩
        unfold jCOf; rw [ite_eq_right hσ]; exact hHt
      have hnear := h2 hf
      unfold nearC jCOf at hnear; rw [ite_eq_right hσ, ite_eq_right hσ] at hnear
      obtain ⟨-, -, hCt, -, ELt, ERt⟩ := h.facts (h.lt (t - 1) (by omega))
      rw [hHt] at ELt ERt hCt
      have hx := chLe_xv (by rw [hhz]; exact EL.good) (by rw [hHt]; exact ELt.good) hle (by rw [hHt, hhz])
      rw [hHt, hhz] at hx
      -- the right end of our chord is not after the right end of the found chord
      have hr : xv P C V (chR m V (chAt m V q)) V.hz ≤ xv P C V (chR m V (chAt m V (t - 1))) V.hz := by
        by_cases hq' : chAt m V q = chAt m V (t - 1)
        · rw [hq']
        · have := chord_disjoint h (h.lt q hq) (h.lt (t - 1) (by omega)) hq' (by rw [hhz, hHt])
            (by rw [hhz, hHt]; exact hx)
          rw [hhz, hHt] at this
          linarith [hCt.lt]
      linarith

/-- **The candidates of the stopping point.** -/
theorem cand_of_stop (hN : IsNF (chainModel C) (Qof P) N) (hP : C.P.Simple)
    {q : ℕ × ℕ × ℕ × ℕ} {X : Point} (hst : StopOK P C V q X) {pk : ℕ → ℕ}
    (hloc : ∀ k, k < 4 → pk k < N.arcs.length ∧
      LocFacts P (chainModel C) N V.hz (posK q k) (pk k))
    {v : ℕ} (hv : v < N.arcs.length)
    (hX : X ∈ (chainModel C).arcSet (sk (chainModel C) (Qof P) N v) (ek (chainModel C) (Qof P) N v)) :
    ∃ k, k < 4 ∧ (v = pk k ∨ v = succP N.arcs.length (pk k) ∨ v = predP N.arcs.length (pk k)) := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  by_cases hne : (N.F (chainModel C) (Qof P)).Nonempty
  · obtain ⟨p, t, hp, ht0, ht1, hin, rfl⟩ := hX
    rw [walk_n] at hp
    obtain ⟨k, hk, hkey⟩ := hst.2 p t hp ht0 ht1 rfl
    rw [hkey] at hin
    obtain ⟨hpk, l1, l2⟩ := hloc k hk
    exact ⟨k, hk, candidate hN hGM hne hv hpk hin l1 l2⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 := arcs_le_one_of_empty hN hGM hne
    have := (hloc 0 (by omega)).1
    exact ⟨0, by omega, Or.inl (by omega)⟩

/-- The facts of the stopping point of the main phase. -/
structure SelFacts (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ) (bD : Option ℕ)
    (z : Point) (X : Point) : Prop where
  stop : StopOK P C V (mainPos P C V m t bD) X
  y : X.2 = ((Qof P).vtx V.hz).2
  on : X ∈ C.set ∨ |X.1| = C.radius
  le : |X.1| ≤ C.radius
  ahead : NotPast C V z → 0 < sgnOf V.σb * (X.1 - ζOf C V z)
  dhit : ∀ cD, bD = some cD → sgnOf V.σb * X.1 ≤ sgnOf V.σb * xe (Qof P) (eIdx P.n V.s cD) V.hz
  near : FoundC V m t → sgnOf V.σb * X.1 ≤ sgnOf V.σb * xv P C V (nearC V m t) V.hz

theorem xe_mem_edge (hT : TopOK P C V) {e : ℕ} (he : e < P.n) (hsp : Spans (Qof P) e V.hz)
    (hn2 : 2 ≤ P.n) :
    ((xe (Qof P) e V.hz, ((Qof P).vtx V.hz).2) : Point) ∈ (Qof P).edge e := by
  have := (rayPt_mem_edge_iff (Qof P) (edge_nonhoriz hT.hD he hn2)
    (z := ((xe (Qof P) e V.hz, ((Qof P).vtx V.hz).2) : Point)) rfl (Or.inl rfl) 0).2
    ⟨hsp, by simp⟩
  simpa [rayPt] using this

/-- **The stopping point of the main phase.** -/
theorem sel_facts (h : ChordRecOK P C V m N) {z : Point} (hs : SemOK P C V z) (hP : C.P.Simple)
    {t : ℕ} (hpart : PartC P C V m t) (hnd : ¬ (FoundC V m t ∧ DegC P C V m t))
    {bD : Option ℕ} {SD : Set Point}
    (hD : Sweep.FirstHitOpt SD z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z bD))
    (hbD : ∀ cb, bD = some cb → cb < V.m) :
    ∃ X, SelFacts P C V m t bD z X := by
  have hv := h.hT.hv
  have hT := h.hT
  have hR := C.radius_pos
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn2 : 2 ≤ P.n := by
    have := C.add_one_le; have := C.one_le; rw [hv.CQ, hQn] at *; omega
  -- the hit on `D*`
  have hDf : ∀ cD, bD = some cD → Spans (Qof P) (eIdx P.n V.s cD) V.hz ∧
      0 < sgnOf V.σb * (xe (Qof P) (eIdx P.n V.s cD) V.hz - z.1) ∧
      ((xe (Qof P) (eIdx P.n V.s cD) V.hz, ((Qof P).vtx V.hz).2) : Point) ∈ C.chainEdge cD ∧
      |xe (Qof P) (eIdx P.n V.s cD) V.hz| < C.radius := by
    intro cD hcD
    subst hcD
    have hpos : 0 < vOf (Qof P) V.s V.hz (sgnOf V.σb) z cD := (show FirstHit _ _ _ _ from hD).1
    have hsp := spans_of_vOf_pos hpos
    rw [vOf_of_spans hsp] at hpos
    rw [hQn] at hsp hpos
    have hmem : ((xe (Qof P) (eIdx P.n V.s cD) V.hz, ((Qof P).vtx V.hz).2) : Point) ∈
        C.chainEdge cD := by
      rw [chainEdge_eq_edge hv]
      exact xe_mem_edge hT (Nat.mod_lt _ (by omega)) hsp hn2
    have hc := hbD cD rfl
    rw [hv.m] at hc
    exact ⟨hsp, hpos, hmem, abs_fst_lt_radius_of_mem ⟨cD, hc, hmem⟩⟩
  have hsσ := sgnOf_cases V.σb
  have htK := hpart.1
  by_cases hA : FoundC V m t ∧ (bD = none ∨ CBof P C V bD (nearC V m t))
  · -- the near end of the chord next to the origin
    have hsel : selOf C V bD (FoundC V m t) (nearC V m t) (CBof P C V bD (nearC V m t)) =
        chordSel C V (nearC V m t) := by unfold selOf; rw [ite_eq_left hA]
    obtain ⟨hK, hH⟩ := hA.1
    have hj : jCOf V t < V.K := by
      unfold jCOf; split_ifs at hK ⊢ with hσ <;> omega
    obtain ⟨-, -, hC, -, EL, ER⟩ := h.facts (h.lt _ hj)
    rw [hH] at hC EL ER
    have hnd' : ¬ DegC P C V m t := fun hd => hnd ⟨hA.1, hd⟩
    unfold DegC at hnd'
    have hEN : EndFacts P C V (nearC V m t) V.hz ∧ xpClass (nearC V m t) = 1 := by
      unfold nearC
      by_cases hσ : V.σb = 1
      · rw [ite_eq_left hσ] at hnd' ⊢
        refine ⟨EL, ?_⟩
        unfold nearC at hnd'; rw [ite_eq_left hσ, not_not] at hnd'
        rcases hnd' with h2 | ⟨h1, -⟩
        · exfalso
          have := xv_c2 (P := P) (C := C) (V := V) (h := V.hz) h2
          have := xv_le P C V ER.good
          linarith [hC.lt]
        · exact h1
      · rw [ite_eq_right hσ] at hnd' ⊢
        refine ⟨ER, ?_⟩
        unfold nearC at hnd'; rw [ite_eq_right hσ, not_not] at hnd'
        rcases hnd' with h0 | ⟨h1, -⟩
        · exfalso
          have := xv_c0 (P := P) (C := C) (V := V) (h := V.hz) h0
          have := xv_ge P C V EL.good
          linarith [hC.lt]
        · exact h1
    obtain ⟨EN, hc1⟩ := hEN
    obtain ⟨c, hc, hsel2, hmem⟩ := near_stop hv EN hc1
    have hX := EN.1
    refine ⟨(chainModel C).pos (Qof P) ⟨nearC V m t, V.hz + 1⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · unfold mainPos; rw [hsel, hsel2]; exact stop_chain hT hP hc hmem (by rw [hX])
    · rw [hX]
    · exact Or.inl ⟨c, hc, hmem⟩
    · exact (abs_fst_lt_radius_of_mem ⟨c, hc, hmem⟩).le
    · intro hnp
      rw [hX]; simp only
      by_cases hσ : V.σb = 1
      · rw [ite_eq_left hσ, not_not] at hnd'
        rw [sgnOf_one hσ, one_mul]
        linarith [(endGtZ_iff hσ hs.zo hnp EN.good).1 hnd']
      · rw [ite_eq_right hσ, not_not] at hnd'
        rw [sgnOf_ne hσ]
        linarith [(endLtZ_iff hσ hs.zo hnp EN.good).1 hnd']
    · intro cD hcD
      obtain ⟨-, -, -, hxD⟩ := hDf cD hcD
      have hcb : CBof P C V bD (nearC V m t) := by
        rcases hA.2 with h0 | h0
        · rw [hcD] at h0; exact absurd h0 (by simp)
        · exact h0
      rw [hcD] at hcb
      have hcb' : if V.σb = 1 then EndLtD P C V (eIdx P.n V.s cD) (nearC V m t) V.hz
          else EndGtD P C V (eIdx P.n V.s cD) (nearC V m t) V.hz := hcb
      clear hcb
      have hcb := hcb'
      rw [hX]; simp only
      by_cases hσ : V.σb = 1
      · rw [ite_eq_left hσ] at hcb
        rw [sgnOf_one hσ, one_mul, one_mul]
        exact ((endLtD_iff EN.good hxD).1 hcb).le
      · rw [ite_eq_right hσ] at hcb
        rw [sgnOf_ne hσ]
        linarith [(endGtD_iff EN.good hxD).1 hcb]
    · intro _; rw [hX]
  by_cases hB : ∃ cD, bD = some cD
  · -- the hit on `D*`
    obtain ⟨cD, rfl⟩ := hB
    have hsel : selOf C V (some cD) (FoundC V m t) (nearC V m t)
        (CBof P C V (some cD) (nearC V m t)) = (0, cD) := by
      unfold selOf; rw [ite_eq_right hA]
    obtain ⟨hsp, hpos, hmem, hxD⟩ := hDf cD rfl
    refine ⟨((xe (Qof P) (eIdx P.n V.s cD) V.hz, ((Qof P).vtx V.hz).2) : Point),
      ⟨?_, rfl, Or.inl ⟨cD, (by rw [← hv.m]; exact hbD cD rfl), hmem⟩, hxD.le, ?_, ?_, ?_⟩⟩
    · unfold mainPos; rw [hsel]; exact stop_chain hT hP (by rw [← hv.m]; exact hbD cD rfl) hmem rfl
    · intro hnp
      simp only
      have hx := abs_lt.1 hxD
      unfold ζOf
      by_cases hσ : V.σb = 1
      · rw [ite_eq_left hσ]; rw [sgnOf_one hσ, one_mul] at hpos ⊢
        have := max_lt (show z.1 < _ by linarith) hx.1
        linarith
      · rw [ite_eq_right hσ]; rw [sgnOf_ne hσ] at hpos ⊢
        have := lt_min (show _ < z.1 by linarith) hx.2
        linarith
    · intro cD' hcD'; cases hcD'; exact le_rfl
    · intro hf
      simp only
      have hcb : ¬ CBof P C V (some cD) (nearC V m t) := fun hc => hA ⟨hf, Or.inr hc⟩
      obtain ⟨hK, hH⟩ := hf
      have hj : jCOf V t < V.K := by
        unfold jCOf; split_ifs at hK ⊢ with hσ <;> omega
      obtain ⟨-, -, -, -, EL, ER⟩ := h.facts (h.lt _ hj)
      rw [hH] at EL ER
      have hcb' : ¬ (if V.σb = 1 then EndLtD P C V (eIdx P.n V.s cD) (nearC V m t) V.hz
          else EndGtD P C V (eIdx P.n V.s cD) (nearC V m t) V.hz) := hcb
      clear hcb
      have hcb := hcb'
      unfold nearC at hcb ⊢
      by_cases hσ : V.σb = 1
      · rw [ite_eq_left hσ] at hcb ⊢; rw [ite_eq_left hσ] at hcb
        rw [sgnOf_one hσ, one_mul, one_mul]
        exact not_lt.1 (fun hh => hcb ((endLtD_iff EL.good hxD).2 hh))
      · rw [ite_eq_right hσ] at hcb ⊢; rw [ite_eq_right hσ] at hcb
        rw [sgnOf_ne hσ]
        have := not_lt.1 (fun hh => hcb ((endGtD_iff ER.good hxD).2 hh))
        linarith
  · -- the side of the box
    push Not at hB
    have hbn : bD = none := by
      cases bD with
      | none => rfl
      | some cD => exact absurd rfl (hB cD)
    subst hbn
    have hnf : ¬ FoundC V m t := fun hf => hA ⟨hf, Or.inl rfl⟩
    have hsel : selOf C V none (FoundC V m t) (nearC V m t) (CBof P C V none (nearC V m t)) =
        (1, if V.σb = 1 then 3 else 1) := by
      unfold selOf; rw [ite_eq_right hA]; rfl
    have hw : (if V.σb = 1 then 3 else 1) = 1 ∨ (if V.σb = 1 then 3 else 1) = 3 := by
      split_ifs <;> simp
    refine ⟨((if (if V.σb = 1 then 3 else 1) = 3 then C.radius else -C.radius),
      ((Qof P).vtx V.hz).2), ⟨?_, rfl, Or.inr ?_, ?_, ?_, fun cD h' => absurd h' (by simp),
      fun hf => absurd hf hnf⟩⟩
    · unfold mainPos; rw [hsel]; exact stop_box hT hw rfl
    · split_ifs <;> simp [abs_of_pos hR]
    · split_ifs <;> simp [abs_of_pos hR]
    · intro hnp
      unfold ζOf
      by_cases hσ : V.σb = 1
      · simp only [ite_eq_left hσ, ite_true]; rw [sgnOf_one hσ, one_mul]
        have := max_lt (hnp.1 hσ) (show -C.radius < C.radius by linarith)
        linarith
      · simp only [ite_eq_right hσ, show ¬ (1 : ℕ) = 3 by omega, ite_false]; rw [sgnOf_ne hσ]
        have := lt_min (hnp.2 hσ) (show -C.radius < C.radius by linarith)
        linarith

end

end OracleR

end Chazelle.Core
