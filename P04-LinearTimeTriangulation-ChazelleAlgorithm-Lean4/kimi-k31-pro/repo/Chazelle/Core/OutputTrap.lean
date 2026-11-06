module

public import Chazelle.Core.OutputNF
public import Chazelle.RewriteTactics

/-!
# WP-N, part 4: the trapezoid record of a region, computed from its chord records

`accOf b n N r` scans the exit chords of region `r` (its chord list): a chord with `dn = r` is a
top chord (its vertex is the top vertex), any other a bottom chord; an end whose walk edge does
not start at the chord's vertex gives the walk edge of a side edge (`inp` maps it to the edge of
`Q`).  `finish` completes the record when a side or a corner was not seen:

* no left end seen: the top vertex is the upper end of the left edge (its walk edge starts
  there), or, with no top chord either, the left walk edge follows the right one (a peak);
* no right end seen: symmetric at the bottom (a valley);
* no top (bottom) chord: the top (bottom) vertex is the end of the right (left) walk edge.

`trapOf_eq`: the result is the record `trapRecOf D` of the trapezoid data of the region, and
`table_ok`: the records of all regions form a trapezoid table of `Q`.
-/

namespace Chazelle.Core

namespace OutTrap

open Chazelle.Visibility
open Chazelle.Geometry (point_ext)
open Chazelle.Mountain (TrapData exists_trapData)
open OutWalk OutNF

@[expose] public section

/-- The state of the scan of a region's exit chords: flags (top chord seen, bottom chord seen,
left side edge seen, right side edge seen) and the values found. -/
structure Acc where
  /-- A top chord was seen. -/
  hT : Bool
  /-- A bottom chord was seen. -/
  hB : Bool
  /-- A left end inside the left side edge was seen. -/
  hL : Bool
  /-- A right end inside the right side edge was seen. -/
  hR : Bool
  /-- The top vertex. -/
  vt : ℕ
  /-- The bottom vertex. -/
  vb : ℕ
  /-- The walk edge of the left side edge. -/
  pl : ℕ
  /-- The walk edge of the right side edge. -/
  pr : ℕ

/-- The initial state. -/
def Acc.init : Acc := ⟨false, false, false, false, 0, 0, 0, 0⟩

/-- One chord record. -/
def accStep (b : Bool) (n ri : ℕ) (a : Acc) (c : CRec) : Acc where
  hT := a.hT || decide (c.dn = ri)
  hB := a.hB || !decide (c.dn = ri)
  hL := a.hL || !decide (wv b n c.lp = c.h)
  hR := a.hR || !decide (wv b n c.rp = c.h)
  vt := if c.dn = ri then c.h else a.vt
  vb := if c.dn = ri then a.vb else c.h
  pl := if wv b n c.lp = c.h then a.pl else c.lp
  pr := if wv b n c.rp = c.h then a.pr else c.rp

/-- The scan of the exit chords of region `ri`. -/
def accOf (b : Bool) (n : ℕ) (N : NF) (ri : ℕ) : Acc :=
  ((N.region ri).chords.map N.chord).foldl (accStep b n ri) Acc.init

/-- Completion of the record. -/
def finish (b : Bool) (n : ℕ) (a : Acc) : Final.TrapRec :=
  let pl := if a.hL then a.pl else if a.hT then wv b n a.vt else nxt n a.pr
  let pr := if a.hR then a.pr else if a.hB then wv b n a.vb else nxt n pl
  ⟨inp b n pl, inp b n pr, if a.hT then a.vt else wv b n (nxt n pr),
    if a.hB then a.vb else wv b n (nxt n pl)⟩

/-- **The trapezoid record of region `ri`.** -/
def trapOf (b : Bool) (n : ℕ) (N : NF) (ri : ℕ) : Final.TrapRec := finish b n (accOf b n N ri)

/-! ## The scan -/

/-- The flags of the scan. -/
theorem fold_flags (b : Bool) (n ri : ℕ) (L : List CRec) (a : Acc) :
    ((L.foldl (accStep b n ri) a).hT = true ↔ a.hT = true ∨ ∃ c ∈ L, c.dn = ri) ∧
      ((L.foldl (accStep b n ri) a).hB = true ↔ a.hB = true ∨ ∃ c ∈ L, c.dn ≠ ri) ∧
      ((L.foldl (accStep b n ri) a).hL = true ↔ a.hL = true ∨ ∃ c ∈ L, wv b n c.lp ≠ c.h) ∧
      ((L.foldl (accStep b n ri) a).hR = true ↔ a.hR = true ∨ ∃ c ∈ L, wv b n c.rp ≠ c.h) := by
  induction L generalizing a with
  | nil => simp
  | cons c L ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (accStep b n ri a c)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1]; simp only [accStep, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨c', hc', h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, Or.inl rfl, h⟩
        · exact Or.inr ⟨c', Or.inr hc', h'⟩
      · rintro (h | ⟨c', (rfl | hc'), h'⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨c', hc', h'⟩
    · rw [h2]; simp only [accStep, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨c', hc', h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, Or.inl rfl, h⟩
        · exact Or.inr ⟨c', Or.inr hc', h'⟩
      · rintro (h | ⟨c', (rfl | hc'), h'⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨c', hc', h'⟩
    · rw [h3]; simp only [accStep, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨c', hc', h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, Or.inl rfl, h⟩
        · exact Or.inr ⟨c', Or.inr hc', h'⟩
      · rintro (h | ⟨c', (rfl | hc'), h'⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨c', hc', h'⟩
    · rw [h4]; simp only [accStep, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨c', hc', h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, Or.inl rfl, h⟩
        · exact Or.inr ⟨c', Or.inr hc', h'⟩
      · rintro (h | ⟨c', (rfl | hc'), h'⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨c', hc', h'⟩

/-- The values of the scan, when every record satisfies the facts of `chord_facts`. -/
theorem fold_vals (b : Bool) (n ri T B pI pJ : ℕ) (L : List CRec)
    (hL : ∀ c ∈ L, (c.dn = ri → c.h = T) ∧ (c.dn ≠ ri → c.h = B) ∧
      (wv b n c.lp ≠ c.h → c.lp = pI) ∧ (wv b n c.rp ≠ c.h → c.rp = pJ))
    (a : Acc) (ha : (a.hT = true → a.vt = T) ∧ (a.hB = true → a.vb = B) ∧
      (a.hL = true → a.pl = pI) ∧ (a.hR = true → a.pr = pJ)) :
    let a' := L.foldl (accStep b n ri) a
    (a'.hT = true → a'.vt = T) ∧ (a'.hB = true → a'.vb = B) ∧
      (a'.hL = true → a'.pl = pI) ∧ (a'.hR = true → a'.pr = pJ) := by
  induction L generalizing a with
  | nil => exact ha
  | cons c L ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc'))
    obtain ⟨h1, h2, h3, h4⟩ := hL c List.mem_cons_self
    obtain ⟨a1, a2, a3, a4⟩ := ha
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      simp only [accStep, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at h ⊢
    · split_ifs with hc
      · exact h1 hc
      · exact a1 (h.resolve_right hc)
    · split_ifs with hc
      · exact a2 (h.resolve_right (not_not.2 hc))
      · exact h2 hc
    · split_ifs with hc
      · exact a3 (h.resolve_right (not_not.2 hc))
      · exact h3 hc
    · split_ifs with hc
      · exact a4 (h.resolve_right (not_not.2 hc))
      · exact h4 hc

/-! ## Correctness of the record -/

variable {Q : Polygon} {N : NF} {reg : ℕ → Set Point}

/-- **The computed record of a region is its trapezoid record.** -/
theorem trapOf_eq (H : RegCtx Q N reg) {ri : ℕ} (hr : ri < N.nRegions) (D : TrapData Q)
    (hD : D.region = reg ri) : trapOf (revOf Q) Q.n N ri = Final.trapRecOf D := by
  have hQ := H.simple
  have hn3 : 3 ≤ Q.n := hQ.1
  have hi := D.isTrap.hi
  have hj := D.isTrap.hj
  have hpi := inp_lt (b := revOf Q) hi
  have hpj := inp_lt (b := revOf Q) hj
  have htn := D.top_lt hQ
  have hbn := D.bot_lt hQ
  have hy1 := D.bot_snd hQ
  have hy2 := D.top_snd hQ
  set L := (N.region ri).chords.map N.chord with hL
  have hfacts : ∀ c ∈ L, (c.dn = ri → c.h = D.top) ∧ (c.dn ≠ ri → c.h = D.bot) ∧
      (wv (revOf Q) Q.n c.lp ≠ c.h → c.lp = inp (revOf Q) Q.n D.i) ∧
      (wv (revOf Q) Q.n c.rp ≠ c.h → c.rp = inp (revOf Q) Q.n D.j) := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    have hkN : k < N.nChords := (((H.regs ri hr).1 k).1 hk).1
    obtain ⟨f1, f2, f3, f4⟩ := H.facts hr D hD hk
    obtain ⟨hlp, hrp, -⟩ := rec_attach H.nf hkN
    refine ⟨f1, f2, fun h => ?_, fun h => ?_⟩
    · rw [← f3 h, inp_inp hlp]
    · rw [← f4 h, inp_inp hrp]
  obtain ⟨vT, vB, vL, vR⟩ := fold_vals (revOf Q) Q.n ri D.top D.bot (inp (revOf Q) Q.n D.i)
    (inp (revOf Q) Q.n D.j) L hfacts Acc.init (by simp [Acc.init])
  obtain ⟨fT, fB, fL, fR⟩ := fold_flags (revOf Q) Q.n ri L Acc.init
  simp only [show Acc.init.hT = false from rfl, show Acc.init.hB = false from rfl,
    show Acc.init.hL = false from rfl, show Acc.init.hR = false from rfl, Bool.false_eq_true,
    false_or] at fT fB fL fR
  have hacc : accOf (revOf Q) Q.n N ri = L.foldl (accStep (revOf Q) Q.n ri) Acc.init := rfl
  set a := accOf (revOf Q) Q.n N ri with ha
  rw [← hacc] at vT vB vL vR fT fB fL fR
  have hmemk : ∀ k ∈ (N.region ri).chords, N.chord k ∈ L := fun k hk => List.mem_map_of_mem hk
  -- the four geometric situations
  have peak : a.hT = false → wv (revOf Q) Q.n (inp (revOf Q) Q.n D.i) = D.top ∧
      wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.j)) = D.top := by
    intro h
    have hno : ∀ k ∈ (N.region ri).chords, (N.chord k).dn ≠ ri := fun k hk hdn => by
      have := fT.2 ⟨_, hmemk k hk, hdn⟩; rw [h] at this; exact Bool.false_ne_true this
    obtain ⟨e1, e2⟩ := OutGeom.top_empty hQ H.dh D (H.no_top hr D hD hno)
    exact ⟨walk_left_upper hQ D (OutGeom.top_left_upper hQ D e1),
      walk_right_upper hQ D (OutGeom.top_right_upper hQ D e2)⟩
  have valley : a.hB = false → wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.i)) = D.bot ∧
      wv (revOf Q) Q.n (inp (revOf Q) Q.n D.j) = D.bot := by
    intro h
    have hno : ∀ k ∈ (N.region ri).chords, (N.chord k).dn = ri := fun k hk => by
      by_contra hdn
      have := fB.2 ⟨_, hmemk k hk, hdn⟩; rw [h] at this; exact Bool.false_ne_true this
    obtain ⟨e1, e2⟩ := OutGeom.bot_empty hQ H.dh D (H.no_bot hr D hD hno)
    exact ⟨walk_left_lower hQ D (OutGeom.bot_left_lower hQ D e1),
      walk_right_lower hQ D (OutGeom.bot_right_lower hQ D e2)⟩
  have noL : a.hL = false → wv (revOf Q) Q.n (inp (revOf Q) Q.n D.i) = D.top ∧
      wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.i)) = D.bot := by
    intro h
    have hall : ∀ k ∈ (N.region ri).chords,
        wv (revOf Q) Q.n (N.chord k).lp = (N.chord k).h := fun k hk => by
      by_contra hne
      have := fL.2 ⟨_, hmemk k hk, hne⟩; rw [h] at this; exact Bool.false_ne_true this
    obtain ⟨e1, e2⟩ := H.all_left hr D hD hall
    exact ⟨walk_left_upper hQ D (OutGeom.top_left_upper hQ D (point_ext e1 hy2)),
      walk_left_lower hQ D (OutGeom.bot_left_lower hQ D (point_ext e2 hy1))⟩
  have noR : a.hR = false → wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.j)) = D.top ∧
      wv (revOf Q) Q.n (inp (revOf Q) Q.n D.j) = D.bot := by
    intro h
    have hall : ∀ k ∈ (N.region ri).chords,
        wv (revOf Q) Q.n (N.chord k).rp = (N.chord k).h := fun k hk => by
      by_contra hne
      have := fR.2 ⟨_, hmemk k hk, hne⟩; rw [h] at this; exact Bool.false_ne_true this
    obtain ⟨e1, e2⟩ := H.all_right hr D hD hall
    exact ⟨walk_right_upper hQ D (OutGeom.top_right_upper hQ D (point_ext e1 hy2)),
      walk_right_lower hQ D (OutGeom.bot_right_lower hQ D (point_ext e2 hy1))⟩
  -- not a peak and a valley at once
  have hTB : a.hT = true ∨ a.hB = true := by
    by_contra hcon
    push Not at hcon
    simp only [Bool.not_eq_true] at hcon
    obtain ⟨p1, p2⟩ := peak hcon.1
    obtain ⟨v1, v2⟩ := valley hcon.2
    have e1 : inp (revOf Q) Q.n D.i = nxt Q.n (inp (revOf Q) Q.n D.j) :=
      wv_inj hpi (nxt_lt hpj) (p1.trans p2.symm)
    have e2 : inp (revOf Q) Q.n D.j = nxt Q.n (inp (revOf Q) Q.n D.i) :=
      wv_inj hpj (nxt_lt hpi) (v2.trans v1.symm)
    rw [e2] at e1
    unfold nxt at e1
    split_ifs at e1 <;> omega
  have hLR : a.hL = true ∨ a.hR = true := by
    by_contra hcon
    push Not at hcon
    simp only [Bool.not_eq_true] at hcon
    have hempty : ∀ k ∈ (N.region ri).chords, False := fun k hk => by
      have hkN : k < N.nChords := (((H.regs ri hr).1 k).1 hk).1
      refine H.not_both hkN ?_ ?_
      · by_contra hne
        have := fL.2 ⟨_, hmemk k hk, hne⟩; rw [hcon.1] at this; exact Bool.false_ne_true this
      · by_contra hne
        have := fR.2 ⟨_, hmemk k hk, hne⟩; rw [hcon.2] at this; exact Bool.false_ne_true this
    rcases hTB with h | h
    · obtain ⟨c, hc, -⟩ := fT.1 h
      obtain ⟨k, hk, -⟩ := List.mem_map.1 hc
      exact hempty k hk
    · obtain ⟨c, hc, -⟩ := fB.1 h
      obtain ⟨k, hk, -⟩ := List.mem_map.1 hc
      exact hempty k hk
  -- the walk edge of the left side
  have hpl : (if a.hL then a.pl else if a.hT then wv (revOf Q) Q.n a.vt else nxt Q.n a.pr) =
      inp (revOf Q) Q.n D.i := by
    cases hLa : a.hL
    · cases hTa : a.hT
      · have hRa : a.hR = true := hLR.resolve_left (by rwd [hLa])
        simp only [Bool.false_eq_true, ite_false]
        rw [vR hRa]
        exact (wv_inj (nxt_lt hpj) hpi ((peak hTa).2.trans (peak hTa).1.symm))
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        rw [vT hTa, ← (noL hLa).1, wv_wv hpi]
    · simp only [ite_true]; exact vL hLa
  have hpr : (if a.hR then a.pr else if a.hB then wv (revOf Q) Q.n a.vb
      else nxt Q.n (inp (revOf Q) Q.n D.i)) = inp (revOf Q) Q.n D.j := by
    cases hRa : a.hR
    · cases hBa : a.hB
      · simp only [Bool.false_eq_true, ite_false]
        exact wv_inj (nxt_lt hpi) hpj ((valley hBa).1.trans (valley hBa).2.symm)
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        rw [vB hBa, ← (noR hRa).2, wv_wv hpj]
    · simp only [ite_true]; exact vR hRa
  simp only [trapOf, finish, ← ha]
  rw [hpl, hpr]
  simp only [Final.trapRecOf, Final.TrapRec.mk.injEq]
  refine ⟨inp_inp hi, inp_inp hj, ?_, ?_⟩
  · cases hTa : a.hT
    · simp only [Bool.false_eq_true, ite_false]; exact (peak hTa).2
    · simp only [ite_true]; exact vT hTa
  · cases hBa : a.hB
    · simp only [Bool.false_eq_true, ite_false]; exact (valley hBa).1
    · simp only [ite_true]; exact vB hBa

/-- **The records of all regions form a trapezoid table of `Q`.** -/
theorem table_ok (H : RegCtx Q N reg) :
    Final.IsTrapTable Q ((List.range N.nRegions).map (trapOf (revOf Q) Q.n N)) := by
  have hQ := H.simple
  have hregQ : ∀ s, s < N.nRegions → reg s ∈ regions Q := fun s hs => by
    rw [← model_regions H.full]; exact H.corr.1 s hs
  set Dof : ∀ s, s ∈ List.range N.nRegions → TrapData Q := fun s hs =>
    Classical.choose (exists_trapData hQ (hregQ s (List.mem_range.1 hs))) with hDof
  have hDspec : ∀ s hs, (Dof s hs).region = reg s := fun s hs =>
    Classical.choose_spec (exists_trapData hQ (hregQ s (List.mem_range.1 hs)))
  refine ⟨(List.range N.nRegions).pmap Dof (fun _ => id), ?_, ?_, fun R => ⟨fun hR => ?_, ?_⟩⟩
  · rw [List.map_pmap]
    rw [List.pmap_congr_left (q := fun s => s ∈ List.range N.nRegions)
      (g := fun s _ => trapOf (revOf Q) Q.n N s) _ (H₂ := fun _ => id)
      (fun s hs h1 _ => (trapOf_eq H (List.mem_range.1 hs) (Dof s h1) (hDspec s h1)).symm)]
    exact List.pmap_eq_map _
  · rw [List.map_pmap]
    rw [List.pmap_congr_left (q := fun s => s ∈ List.range N.nRegions) (g := fun s _ => reg s) _
      (H₂ := fun _ => id) (fun s _ h1 _ => hDspec s h1), List.pmap_eq_map]
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    exact H.corr.2.1 x y (List.mem_range.1 hx) (List.mem_range.1 hy) hxy
  · rw [← model_regions H.full] at hR
    obtain ⟨s, hs, rfl⟩ := H.corr.2.2 R hR
    exact ⟨Dof s (List.mem_range.2 hs), List.mem_pmap.2 ⟨s, List.mem_range.2 hs, rfl⟩,
      hDspec s (List.mem_range.2 hs)⟩
  · rintro ⟨D, -, rfl⟩
    exact D.region_mem_regions hQ

/-- **No vertex-to-vertex chords** (distinct heights): the empty vertex-chord table is valid. -/
theorem vtxChordTable_nil (hQ : Q.Simple) (hdh : DistinctHeights Q) :
    Final.IsVtxChordTable Q [] := by
  refine ⟨fun c => ⟨fun h => absurd h List.not_mem_nil, fun ⟨h1, h2, h3, h4⟩ => ?_⟩, List.nodup_nil⟩
  exfalso
  have hy : (Q.vtx c.dst).2 = (Q.vtx c.src).2 := by rw [← h4, chordEnd_snd]
  have hsd : c.dst = c.src := by
    by_contra hne; exact hdh _ _ h2 h1 hne hy
  exact chordEnd_ne_vtx hQ h1 h3 (by rw [h4, hsd])

/-- **A region has at most four exit chords** (two at the top vertex, two at the bottom
vertex). -/
theorem chords_length_le (H : RegCtx Q N reg) {ri : ℕ} (hr : ri < N.nRegions) :
    (N.region ri).chords.length ≤ 4 := by
  classical
  have hQ := H.simple
  have hregQ : reg ri ∈ regions Q := by rw [← model_regions H.full]; exact H.corr.1 ri hr
  obtain ⟨D, hD⟩ := exists_trapData hQ hregQ
  set f : ℕ → Set Point := fun k => (N.chord k).toSet (interiorModel Q) Q with hf
  set T : Finset (Set Point) := {chordSet Q D.top 1, chordSet Q D.top (-1), chordSet Q D.bot 1,
    chordSet Q D.bot (-1)} with hT
  have hnd : ((N.region ri).chords.map f).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) ((H.regs ri hr).2.1)
    exact H.nf.2.1 x y (((H.regs ri hr).1 x).1 hx).1 (((H.regs ri hr).1 y).1 hy).1 hxy
  have hsub : ((N.region ri).chords.map f).toFinset ⊆ T := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkN  := (((H.regs ri hr).1 k).1 hk).1
    obtain ⟨v, σ, hv, hσ, -, hS, -⟩ := chords_spec hQ (rec_chords H.full hkN)
    have hvh : v = (N.chord k).h := by
      have e : hseg (Q.vtx v).2 (min (Q.vtx v).1 (chordEnd Q v σ).1)
          (max (Q.vtx v).1 (chordEnd Q v σ).1) = hseg (Q.vtx (N.chord k).h).2
            ((interiorModel Q).pos Q (N.chord k).lpos).1
            ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
        rwr [← chordSet_eq_hseg, ← hS]
      obtain ⟨e1, -⟩ := Merge.hseg_inj (min_le_max) e
      by_contra hne
      exact H.dh _ _ hv (H.hlt k hkN) hne e1
    obtain ⟨f1, f2, -, -⟩ := H.facts hr D hD hk
    have hfk : f k = chordSet Q (N.chord k).h σ := by rw [hf]; simp only; rw [hS, hvh]
    rw [hfk, hT]
    by_cases hdn : (N.chord k).dn = ri
    · rw [f1 hdn]; rcases hσ with rfl | rfl <;> simp
    · rw [f2 hdn]; rcases hσ with rfl | rfl <;> simp
  have hT4 : T.card ≤ 4 := by
    rw [hT]
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
  omega

end

end OutTrap

end Chazelle.Core
