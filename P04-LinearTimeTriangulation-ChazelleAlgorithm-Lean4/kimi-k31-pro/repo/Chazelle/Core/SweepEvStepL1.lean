module

public import Chazelle.Core.SweepEvStepL0
public import Chazelle.Core.SweepEvTasks4
public import Chazelle.Core.SweepEvCand5
public import Chazelle.Core.SweepEvWinM
public import Chazelle.Core.SweepEvStopM2
public import Chazelle.Core.SweepEvOrigin
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# The sweep (WP-D), stage 3: no cut between two keys (step 1 of Tasks L1 and L2)

* `attach_far`: the chord seen from a point of `C₂` (not the shared vertex) is attached on the
  `C₁` part only at its far end;
* `whole_lt_right`: a non-stop chord seen from an end of a chord of `S₂` on `C₂`, attached on the
  `C₁` part beyond the start, ends strictly before the far end of the chord of `S₂` (otherwise
  the far end is on `C₂`, the shared vertex, or a box-wall end, whose chord is a wall piece);
* **`no_cut_core`/`no_cut_between`**: in an iteration of the event loop (`LoopInv` at `c`, the
  window `WinOut c cw`, the reset `cs`, the batch of origins `co`), every chord of `F₂⁺` attached
  beyond the key of `c` is attached at or after a stop not yet passed, or at or after the best
  candidate, or strictly after the window end.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)

@[expose] public section

section Math

variable {J : Merge.Junction}

theorem stp_gW_lt : gW J < (chainModel J.whole).W.n := by
  have := tpos_lt J.whole J.m₁
  ruo [cm_n J.whole] gW

/-- **The chord seen from a point of `C₂` is attached on the `C₁` part only at its far end.** -/
theorem attach_far (hP : J.P.Simple) {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hfree : FreeAt J.whole a σ) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) p t)
    (hoff : (Lst J : ℝ) ≤ oW J (p + t)) :
    sidePt (chainModel J.whole).W p t = rayPt a σ (J.whole.hitParam a σ) := by
  have hM  := FactsChain.walkAx J.whole hP
  have ha2  := J.whole.snd_le_top_of_mem_set (J.right_set_subset haR)
  obtain ⟨hτ, -, hint⟩ := Merge.hit_of_freeAt J.whole ha2 hσ hfree
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1,
      lerp a (rayPt a σ (J.whole.hitParam a σ)) s ∈ (chainModel J.whole).D := fun s hs => by
    rw [lerp_rayPt]
    exact hint _ (mul_pos hs.1 hτ) (by nlinarith [hs.2])
  rcases hM.attach_endpoint hopen hA with h | h
  · exfalso
    have := off_right_pt J hP (S₂ := ∅) (empty_subset _) finite_empty hA.1 hA.2.1 hA.2.2.1
      (by rwx [h]) (by rwx [h])
    rw [← oW_eq, ← Lst_eq] at this
    linarith [this.2]
  · exact h

/-- **A non-stop chord from an end of a chord of `S₂` on `C₂`, attached beyond the start, ends
strictly before the far end of that chord.** -/
theorem whole_lt_right (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : (σ = 1 ∧ a = Merge.lend c) ∨ (σ = -1 ∧ a = Merge.rend c))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hfree : FreeAt J.whole a σ)
    (hns : ¬ StopChord2 J S₂ (Merge.shoot J.whole a σ)) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W (Merge.shoot J.whole a σ) p t)
    (hoff : (Lst J : ℝ) < oW J (p + t)) :
    J.whole.hitParam a σ < J.right.hitParam a σ := by
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨-, ha₂, -, hR, hl2, hr2⟩ := right_hit_end (hS₂ hc) ha
  have hle : J.whole.hitParam a σ ≤ J.right.hitParam a σ := by
    rw [whole_hitParam_eq_min J (le_trans ha₂ J.right_top_le) hσ, right_hitParam_eq J ha₂]
    exact min_le_right _ _
  refine lt_of_le_of_ne hle fun heq => ?_
  have ha2  := le_trans ha₂ J.right_top_le
  obtain ⟨hτ, hwD, -⟩ := Merge.hit_of_freeAt J.whole ha2 hσ hfree
  have hpt := attach_far hP hσ haR hav hfree hA hoff.le
  have hAdm  := F₂plus_subset J hS₂ (shoot_end_mem hc ha hfree)
  set τ := J.whole.hitParam a σ with hτd
  -- the far end of `c`
  obtain ⟨b, σ', hσ', hb, hwb⟩ : ∃ (b : Point) (σ' : ℝ), σ' = -σ ∧
      ((σ' = 1 ∧ b = Merge.lend c) ∨ (σ' = -1 ∧ b = Merge.rend c)) ∧ rayPt a σ τ = b := by
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨Merge.rend c, -1, rfl, Or.inr ⟨rfl, rfl⟩, point_ext ?_ ?_⟩
      · rwring [rayPt_fst, heq, hR]
      · rw [rayPt_snd, hr2]
    · refine ⟨Merge.lend c, 1, by norm_num, Or.inl ⟨rfl, rfl⟩, point_ext ?_ ?_⟩
      · rwring [rayPt_fst, heq, hR]
      · rw [rayPt_snd, hl2]
  have hbmem : b ∈ Merge.shoot J.whole a σ := by
    rw [← hwb]; exact Chazelle.Geometry.right_mem_segment _ _
  have hbD : b ∉ J.whole.dom := by rwx [← hwb]
  by_cases hbR : b ∈ J.right.set
  · by_cases hbv : b = J.shared
    · rw [hbv] at hbmem hbD
      obtain ⟨σ'', hσ'', hfr, he⟩ := chord_eq_shoot_of_end J.whole hAdm hbmem hbD
      exact hns (Or.inl (Or.inl ⟨σ'', hσ'', hfr, he⟩))
    · have := off_right_pt J hP (S₂ := ∅) (empty_subset _) finite_empty hA.1 hA.2.1 hA.2.2.1
        (by rwx [hpt, hwb]) (by rwx [hpt, hwb])
      rw [← oW_eq, ← Lst_eq] at this
      linarith [this.2]
  · obtain ⟨σ'', hσ'', hfr, he⟩ := chord_eq_shoot_of_end J.whole hAdm hbmem hbD
    -- the direction from `b` is back towards `a`
    have hb2 : b.2 ≤ J.whole.top.2 := by rwx [← hwb, rayPt_snd]
    obtain ⟨hτ'', -, -⟩ := Merge.hit_of_freeAt J.whole hb2 hσ'' hfr
    have haIn  := he ▸ origin_mem J
    unfold Merge.shoot at haIn
    obtain ⟨s, hs0, hs1, has⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 haIn
    rw [lerp_rayPt] at has
    have hx := congrArg Prod.fst has
    rw [rayPt_fst] at hx
    have hb1 : b.1 = a.1 + σ * τ := by rw [← hwb, rayPt_fst]
    generalize J.whole.hitParam b σ'' = τ'' at hx hτ''
    have hσσ : σ'' = σ' := by
      rw [hσ']
      rcases hσ with rfl | rfl <;> rcases hσ'' with rfl | rfl
      · nlinarith [mul_nonneg hs0 hτ''.le]
      · norm_num
      · norm_num
      · nlinarith [mul_nonneg hs0 hτ''.le]
    rw [hσσ] at hfr he
    exact hns (Or.inl (Or.inr ⟨c, hc, b, σ', hb, hbR, hfr, he⟩))

end Math

section Iter

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config}

/-- The registers kept by the window computation. -/
theorem stp_win_keep (hregW : ∀ r, bandOf r ∉ oracleBands → ¬ WR r → r ≠ ALLOC → cw.nreg r = c.nreg r)
    {k : ℕ} (hk : (600 ≤ k ∧ k < 700) ∨ (2400 ≤ k ∧ k ≤ 2406) ∨ (2430 ≤ k ∧ k ≤ 2459) ∨
      (2600 ≤ k ∧ k ≤ 2699)) : cw.nreg (sw k) = c.nreg (sw k) :=
  hregW _ (band_sw_not ⟨by ufo sw, by ufo sw⟩) (by ufo WR sw)
    (by ufo ALLOC sw)

/-- The registers kept by the reset and the batch of origins. -/
theorem stp_batch_keep (hR : ResetRel cw cs)
    (hregB : ∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → ¬ LR r → r ≠ ALLOC → co.nreg r = cs.nreg r)
    {k : ℕ} (hk : (600 ≤ k ∧ k < 700) ∨ (2400 ≤ k ∧ k ≤ 2409) ∨ (2418 ≤ k ∧ k ≤ 2459) ∨
      (2600 ≤ k ∧ k ≤ 2699)) : cs.nreg (sw k) = cw.nreg (sw k) ∧ co.nreg (sw k) = cw.nreg (sw k) := by
  have h1 : cs.nreg (sw k) = cw.nreg (sw k) :=
    hR.2.2.2 _ (by ufo bF sw) (by ufo bN sw)
  refine ⟨h1, (hregB _ (band_sw_not ⟨by ufo sw, by ufo sw⟩) ?_ ?_
    (by ufo ALLOC sw)).trans h1⟩
  · ufo OrgR CandR BestR LblR bF bE bH bN bL sw
  · ufo LR oK oS sw

/-- **No cut before the candidates (core)**: a chord of `F₂⁺` attached beyond the key of `c`, with
no cut strictly between the key and it, is a stop not yet passed, or is accepted (so the best
candidate is at or before it), or lies beyond the window end. -/
theorem no_cut_core (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs)
    (hB : BatchInv P J N₂ cs
      (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) (cs.nreg wGK) [])
      (iterO N₂ cs) co)
    {e : Set Point} (he : e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P))) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hlt : keyOff P J c < oW J (p + t))
    (hgap : ∀ e' ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)), ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e' q s →
        ¬ (keyOff P J c < oW J (q + s) ∧ oW J (q + s) < oW J (p + t))) :
    (∃ i, c.nreg sP ≤ i ∧ i < c.nreg sC ∧ stopOff P J c i = oW J (p + t)) ∨
    (co.nreg bF = 1 ∧ offK P J (co.nreg bE) (co.nreg bH) ≤ oW J (p + t)) ∨
    (cw.nreg wX = 0 ∧ offK P J (cw.nreg wE) (cw.nreg wH) < oW J (p + t)) := by
  classical
  set S₂ := N₂.F (chainModel J.right) (Qof P) with hS₂d
  have hP := E.hP
  have hS₂  := E.hNF₂.1
  have hS₂a  := hS₂.2.1
  have hF := F₂plus_chordFamily E
  have hLst  := lt_of_le_of_lt L.keyL hlt
  -- a stop chord at the position is a stop not yet passed
  have stopCase : ∀ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s p t → StopChord2 J S₂ s →
      ∃ i, c.nreg sP ≤ i ∧ i < c.nreg sC ∧ stopOff P J c i = oW J (p + t) := by
    intro s hs hsA hss
    obtain ⟨rs, ax, hlen, -, hrec, -, hok, -⟩ := L.stops
    have hmem := hok.2.1 s hs hss p t hsA hLst.le
    obtain ⟨r, hr, hreq⟩ := List.mem_map.1 hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    simp [Prod.mk.injEq] at hreq
    obtain ⟨h1, h2, -⟩ := hreq
    obtain ⟨e0, e1, -⟩ := hrec i hi
    rw [List.getD_eq_getElem _ _ hi] at e0 e1
    have hoff : stopOff P J c i = oW J (p + t) := by
      show offK P J (c.nmem (c.nreg sB + 5 * i)) (c.nmem (c.nreg sB + 5 * i + 1)) = _
      rw [e0, e1]
      show oW J ((rs[i].1 : ℝ) + (chainModel J.whole).param (Qof P) ⟨rs[i].1, rs[i].2.1⟩) = _
      rw [h2, h1]
    have hic  := hlen ▸ hi
    refine ⟨i, ?_, hic, hoff⟩
    by_contra hlt'
    push Not at hlt'
    have := (L.ptrL i hic).1 hlt'
    rw [hoff] at this
    exact absurd hlt (not_lt.2 this)
  by_cases hst : StopChord2 J S₂ e
  · exact Or.inl (stopCase e he hA hst)
  obtain ⟨ch, hch, a, σ, ha, haR, hav, hat, hfree, rfl, hsrc⟩ :=
    nonstop_found hP hS₂ hF L.keyL L.inv hA.1 hA.2.1 hA.2.2.1 hlt hgap he hA hst
  rcases hsrc with ⟨V, hV, hVΛ, hT⟩ | ⟨s, hs, hsA, hss, -⟩
  swap
  · exact Or.inl (stopCase s hs hsA hss)
  by_cases hwin : cw.nreg wX = 0 ∧ offK P J (cw.nreg wE) (cw.nreg wH) < oW J (p + t)
  · exact Or.inr (Or.inr hwin)
  right; left
  have hσ : σ = 1 ∨ σ = -1 := by rcases ha with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hlt' := whole_lt_right hP hS₂a hch ha haR hav hfree hst hA hLst
  have hpt := attach_far hP hσ haR hav hfree hA hLst.le
  have hnv : sidePt (chainModel J.whole).W p t ≠ J.shared := by
    intro h
    have hm  := h ▸ hA.2.2.2.1
    have hvD : J.shared ∉ J.whole.dom := fun hd =>
      J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset J.shared_mem_left)
    obtain ⟨σ', hσ', hfr, he'⟩ := chord_eq_shoot_of_end J.whole (F₂plus_subset J hS₂a he) hm hvD
    exact hst (Or.inl (Or.inl ⟨σ', hσ', hfr, he'⟩))
  have ha₁ : a.2 ≤ J.left.top.2 := by
    rcases SweepStop.hit_cases (J := J) (right_hit_end (hS₂a hch) ha).2.1 hσ with h | h
    · exact absurd h hlt'.ne
    · exact h.1
  obtain ⟨-, -, d, hMV, hmE, hArr⟩ := cand_prep hP hS₂a hch ha haR hav ha₁ hA hpt hLst hnv hlt'
  -- the endpoint query
  obtain ⟨i, hi, hci⟩ := Restore.mem_F_iff hch
  obtain ⟨j, hj, hji, hjO, hjD⟩ : ∃ j, j < 2 * N₂.nChords ∧ (∃ s, s ≤ 1 ∧ j = 2 * i + s) ∧
      endOrigin J (Qof P) N₂ j = a ∧ endDir j = σ := by
    unfold endOrigin endDir
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨2 * i, by omega, ⟨0, by omega, by omega⟩, ?_, ?_⟩
      · rw [ite_eq_left (by omega), show 2 * i / 2 = i by omega, ← hci]
      · rw [ite_eq_left (by omega)]
    · refine ⟨2 * i + 1, by omega, ⟨1, le_rfl, rfl⟩, ?_, ?_⟩
      · rw [ite_eq_right (by omega), show (2 * i + 1) / 2 = i by omega, ← hci]
      · rw [ite_eq_right (by omega)]
  -- the registers through the window, the reset and the batch
  obtain ⟨rs₁, -, -, hgk, -, -, -, -, -, hcov, -, hregW⟩ := hW
  obtain ⟨hregB, -, A, hBA⟩ := hB
  have kW := fun {k : ℕ} hk => stp_win_keep (c := c) (cw := cw) hregW (k := k) hk
  have kB := fun {k : ℕ} hk => stp_batch_keep (cs := cs) (co := co) hR hregB (k := k) hk
  have ekE : cs.nreg kE = c.nreg kE := (kB (k := 2400) (by omega)).1.trans (kW (by omega))
  have ekH : cs.nreg kH = c.nreg kH := (kB (k := 2401) (by omega)).1.trans (kW (by omega))
  have ekN : cs.nreg kN = c.nreg kN := (kB (k := 2402) (by omega)).1.trans (kW (by omega))
  have ekL : ∀ u, u < 4 → cs.nreg (kL + u) = c.nreg (kL + u) := fun u hu => by
    have := (kB (k := 2403 + u) (by omega)).1.trans (kW (by omega))
    rwa [show sw (2403 + u) = kL + u by ufo kL sw] at this
  have egN : cs.nreg gN = c.nreg gN := (kB (k := 2440) (by omega)).1.trans (kW (by omega))
  have egR : ∀ u, u < 2 → cs.nreg (gR + u) = c.nreg (gR + u) := fun u hu => by
    have := (kB (k := 2441 + u) (by omega)).1.trans (kW (by omega))
    rwa [show sw (2441 + u) = gR + u by ufo gR sw] at this
  have eGB : cs.nreg wGB = cw.nreg wGB := (kB (k := 2420) (by omega)).1
  have eGK : cs.nreg wGK = cw.nreg wGK := (kB (k := 2421) (by omega)).1
  -- the query is tried in this iteration
  have hRO := (regOf_spec E.hNF₂).2.2.2.1
  have hreg : ∀ l, l < N₂.nRegions → regOf (chainModel J.right) (Qof P) N₂ l = V →
      j ∈ regO N₂ l := by
    intro l hl hlV
    refine ⟨i, ((hRO l hl).1 i).2 ⟨hi, ?_⟩, hji⟩
    rwx [← hci, hlV]
  have hjO' : j ∈ iterO N₂ cs := by
    rcases hVΛ with ⟨l, hl, hlV⟩ | hg
    · obtain ⟨u, hu, hu4, rfl⟩ : ∃ u, u < c.nreg kN ∧ u < 4 ∧ l = c.nreg (kL + u) := by
        rcases hl with h | h | h | h
        · exact ⟨0, h.1, by norm_num, by rw [add_zero]; exact h.2⟩
        · exact ⟨1, h.1, by norm_num, h.2⟩
        · exact ⟨2, h.1, by norm_num, h.2⟩
        · exact ⟨3, h.1, by norm_num, h.2⟩
      refine Or.inl (Or.inl ⟨u, by rwo [ekN], ?_⟩)
      rw [ekL u hu4]
      exact hreg _ (L.labR u hu) hlV
    · obtain ⟨u, hu, hlV⟩ := L.gap V hg
      have hu2 : u < 2 := by have := L.gapN; omega
      refine Or.inl (Or.inr ⟨u, by rw [egN]; have := L.gapN; omega, ?_⟩)
      rw [egR u hu2]
      exact hreg _ (L.gapR u hu) hlV
  -- the hit is on the gathered arcs
  have hoffd : (Lst J : ℝ) + ψ J d + t = oW J (p + t) := by
    rw [oW_def, off_key' stp_gW_lt hA.1 hA.2.1 hA.2.2.1, ← hmE]
    unfold mEdge
    rw [dOf_add_mod stp_gW_lt (Lst_ψ_lt hP hMV.1)]
    pcr
  have hlo : rayPt a σ (J.whole.hitParam a σ) ∈
      ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) (cs.nreg wGK) [] := by
    have hin := hcov d t hMV hA.2.1 hA.2.2.1 (by rwx [hoffd]) (fun h0 => by
      rw [hoffd]; by_contra hc; exact hwin ⟨h0, not_le.1 hc⟩)
    rw [hArr.2.2.2.1, ← hgk] at hin
    rw [hR.1, eGB, eGK]
    exact hin
  -- accepted, so the best candidate is at or before it
  obtain ⟨h, hh, hmA⟩ := hBA.comp j hjO' hj ⟨by rwx [hjO], by rwx [hjO],
    by rwx [hjO]⟩ p t (by rwx [hjO, hjD]) (by rwx [hjO, hjD]) hLst
    hnv (by rwx [hjO, hjD]) (by rwx [hjO, hjD])
  have hoT : offT P J (j, p, h) = oW J (p + t) := by
    show oW J (p + (chainModel J.whole).param (Qof P) ⟨p, h⟩) = _
    rw [hh]
  obtain ⟨hbF, hle⟩ := hBA.bMin _ hmA (by rwx [hoT, ekE, ekH])
  exact ⟨hbF, hle.trans hoT.le⟩

/-- **No cut before the candidates**: every chord of `F₂⁺` attached beyond the key of `c` is
attached at or after a stop not yet passed, or at or after the best candidate, or strictly after
the window end. -/
theorem no_cut_between (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs)
    (hB : BatchInv P J N₂ cs
      (ShotList.loSet (chainModel J.left) (Qof P) cs.nmem (cs.nreg wGB) (cs.nreg wGK) [])
      (iterO N₂ cs) co)
    {e : Set Point} (he : e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P))) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hlt : keyOff P J c < oW J (p + t)) :
    (∃ i, c.nreg sP ≤ i ∧ i < c.nreg sC ∧ stopOff P J c i ≤ oW J (p + t)) ∨
    (co.nreg bF = 1 ∧ offK P J (co.nreg bE) (co.nreg bH) ≤ oW J (p + t)) ∨
    (cw.nreg wX = 0 ∧ offK P J (cw.nreg wE) (cw.nreg wH) < oW J (p + t)) := by
  classical
  set S₂ := N₂.F (chainModel J.right) (Qof P) with hS₂d
  have hM  := FactsChain.walkAx J.whole E.hP
  have hF := F₂plus_chordFamily E
  set K := {x : ℝ | (chainModel J.whole).IsCut (F₂plus J S₂) x ∧ keyOff P J c < oW J x} with hK
  have hKf : K.Finite := (hM.finite_cuts hF.2.1 hF.1).subset fun x hx => hx.1
  have hKm : ((p : ℝ) + t) ∈ K := ⟨⟨e, he, p, t, hA, rfl⟩, hlt⟩
  obtain ⟨x, ⟨⟨e', he', p', t', hA', rfl⟩, hx⟩, hmin⟩ := Set.exists_min_image K (oW J) hKf ⟨_, hKm⟩
  have hle : oW J (p' + t') ≤ oW J (p + t) := hmin _ hKm
  have hgap : ∀ e'' ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e'' q s →
      ¬ (keyOff P J c < oW J (q + s) ∧ oW J (q + s) < oW J (p' + t')) := by
    rintro e'' he'' q s hq ⟨h1, h2⟩
    exact absurd (hmin _ ⟨⟨e'', he'', q, s, hq, rfl⟩, h1⟩) (not_le.2 h2)
  rcases no_cut_core E L hW hR hB he' hA' hx hgap with ⟨i, h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨i, h1, h2, h3.le.trans hle⟩
  · exact Or.inr (Or.inl ⟨h1, h2.trans hle⟩)
  · exact Or.inr (Or.inr ⟨h1, h2.trans_le hle⟩)

/-- The facts of an iteration seen at the configuration after the origins: the stop pointer and
the stops, the window. -/
theorem iter_stops (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') :
    co.nreg sP = c.nreg sP ∧ co.nreg sC = c.nreg sC ∧
    (∀ i, i < c.nreg sC → stopOff P J co i = stopOff P J c i) ∧
    co.nreg wX = cw.nreg wX ∧ co.nreg wE = cw.nreg wE ∧ co.nreg wH = cw.nreg wH := by
  obtain ⟨hW, hAl, hR, hB, -⟩ := hI
  obtain ⟨rs₁, -, -, -, -, -, -, -, -, -, hmW, hregW⟩ := hW
  obtain ⟨hregB, -, A, hBA⟩ := hB
  have kW := fun {k : ℕ} hk => stp_win_keep (c := c) (cw := cw) hregW (k := k) hk
  have kB := fun {k : ℕ} hk => stp_batch_keep (cs := cs) (co := co) hR hregB (k := k) hk
  have esP : co.nreg sP = c.nreg sP := (kB (k := 2450) (by omega)).2.trans (kW (by omega))
  have esC : co.nreg sC = c.nreg sC := (kB (k := 2601) (by omega)).2.trans (kW (by omega))
  have esB : co.nreg sB = c.nreg sB := (kB (k := 2600) (by omega)).2.trans (kW (by omega))
  have eTB : cs.nreg cTB = c.nreg cTB := (kB (k := 661) (by omega)).1.trans (kW (by omega))
  have eAs : cs.nreg ALLOC = cw.nreg ALLOC := hR.2.2.2 _ (by ufo ALLOC bF sw)
    (by ufo ALLOC bN sw)
  have hmem : ∀ x, x < c.nreg ALLOC → c.nreg cTB + 6 * N₂.nChords ≤ x → co.nmem x = c.nmem x := by
    intro x hx hx'
    rw [hBA.memT x (by omega) (Or.inr (by omega)), hR.1, hmW x hx]
  have hlay := L.lay1
  have hlay2 := L.lay2
  have hlay4 := L.lay4
  refine ⟨esP, esC, fun i hi => ?_, (kB (k := 2425) (by omega)).2,
    (kB (k := 2423) (by omega)).2, (kB (k := 2424) (by omega)).2⟩
  unfold stopOff stopE stopH
  rw [esB, hmem _ (by omega) (by omega), hmem _ (by omega) (by omega)]

/-- **No cut strictly between the key of an iteration and the next key** (Task L1, step 1). -/
theorem no_cut_iter (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') :
    NoCutIn J (N₂.F (chainModel J.right) (Qof P)) (keyOff P J c) (keyOff P J c') := by
  rintro x ⟨e, he, p, t, hA, rfl⟩ - - ⟨h1, h2⟩
  obtain ⟨esP, esC, est, ewX, ewE, ewH⟩ := iter_stops L hI
  obtain ⟨hW, -, hR, hB, hK⟩ := hI
  obtain ⟨-, -, -, hK4⟩ := hK
  rcases no_cut_between E L hW hR hB he hA h1 with ⟨i, hi1, hi2, hi3⟩ | ⟨hbF, hb⟩ | ⟨hwX, hw⟩
  · obtain ⟨-, -, -, hKs, -⟩ := hK4 (Or.inr (Or.inl (by rwo [esP, esC])))
    have h3 := hKs (by rwo [esP, esC])
    rw [esP] at h3
    change keyOff P J c' ≤ stopOff P J co (c.nreg sP) at h3
    rw [est _ (by omega)] at h3
    have h4 := L.sorted (c.nreg sP) i hi1 hi2
    exact absurd (h3.trans (h4.trans hi3)) (not_le.2 h2)
  · obtain ⟨-, -, hKb, -⟩ := hK4 (Or.inl hbF)
    exact absurd ((hKb hbF).trans hb) (not_le.2 h2)
  · obtain ⟨-, -, -, -, hKw, -⟩ := hK4 (Or.inr (Or.inr (by rwx [ewX])))
    have h3 := hKw (by rwx [ewX])
    rw [ewE, ewH] at h3
    exact absurd (h3.trans hw.le) (not_le.2 h2)

/-- **No cut after the last key** (Task L2, `DoneNoCut`): when the iteration finishes, no cut lies
beyond the key. -/
theorem no_cut_done (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 1) :
    NoCutIn J (N₂.F (chainModel J.right) (Qof P)) (keyOff P J c) (chainModel J.whole).W.n := by
  rintro x ⟨e, he, p, t, hA, rfl⟩ - - ⟨h1, -⟩
  obtain ⟨esP, esC, -, ewX, -, -⟩ := iter_stops L hI
  obtain ⟨hW, -, hR, hB, hK⟩ := hI
  obtain ⟨-, -, -, hK4⟩ := hK
  have hnone : ¬ (co.nreg bF = 1 ∨ co.nreg sP < co.nreg sC ∨ co.nreg wX = 0) := fun h => by
    have := (hK4 h).1; omega
  rcases no_cut_between E L hW hR hB he hA h1 with ⟨i, hi1, hi2, -⟩ | ⟨hbF, -⟩ | ⟨hwX, -⟩
  · exact hnone (Or.inr (Or.inl (by rwo [esP, esC])))
  · exact hnone (Or.inl hbF)
  · exact hnone (Or.inr (Or.inr (by rwx [ewX])))

end Iter

end

end SweepEv

end Chazelle.Core
