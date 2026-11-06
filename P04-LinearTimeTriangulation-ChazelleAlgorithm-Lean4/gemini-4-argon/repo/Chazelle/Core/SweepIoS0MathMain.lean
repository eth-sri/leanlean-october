module

public import Chazelle.Core.SweepIoS0MathC

/-!
# The side-0 answer cases (sweep): `SweepIo.side0Math`

**`SweepIo.side0Math : SweepIo.Side0MathSpec`**.  For a side-0 query `z` (on `C₁`, not the
shared vertex, not above the top of `C₂`, free direction `σ`) with arrival position `(pz, tz)`:

* the position is beyond the start (`Lst_lt_of_dom`: `z` is in the domain of `C₂`);
* if the hit point of `C` is on `C₁` or off `C₂`, it is the first hit of `C₁` (C1);
* otherwise it is the first hit of `C₂`, and either the ray runs along a chord of `F₂⁺`
  (`along_end`): the chord is shot from the hit point, which is the top of `C₂` (a stop chord,
  (C3), `case_C3`) or an end of a chord of `S₂` (the endpoint table, (C4), `case_C4`); or the ray
  starts in a region `U` of `F₂⁺` (`leave_region`), the region `V` of `S₂` it starts in is a label
  of `U` (`query_right`), and the labels of `U` are in the log (`labels_of_log`) (C2).
-/

namespace Chazelle.Core

namespace S0Math

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep

@[expose] public section

variable (J : Merge.Junction)

/-- An end of a chord of `C₂` is off the domain of `C₂`, not above its top. -/
theorem end_off_right {c : Set Point} (hc : c ∈ Merge.augChords J.right) :
    Merge.lend c ∉ J.right.dom ∧ Merge.rend c ∉ J.right.dom ∧
      (Merge.lend c).2 ≤ J.right.top.2 ∧ (Merge.rend c).2 ≤ J.right.top.2 := by
  obtain ⟨y, l, r, hH, hy, -, hl, hr⟩ := Merge.augChords_spec hc
  rw [hl, hr]
  exact ⟨hH.left_not, hH.right_not, hy, hy⟩

/-- **(C4): the endpoint table.** -/
theorem case_C4 (hP : J.P.Simple) {Q : Polygon} {N₂ : NF} {T : ℕ → Option (ℕ × ℝ)}
    (hT : TabOK J Q N₂ T) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hzR : z ∈ J.right.dom)
    {c : Set Point} (hc : c ∈ N₂.F (chainModel J.right) Q) {o : Point} {d : ℝ}
    (ho : (d = 1 ∧ o = Merge.lend c) ∨ (d = -1 ∧ o = Merge.rend c)) (hfo : FreeAt J.whole o d)
    (hoR : o ∈ J.right.set) (hov : o ≠ J.shared) (hot : o ≠ J.right.top) (hdσ : d = -σ)
    (hoz : rayPt o d (J.whole.hitParam o d) = z) {pz : ℕ} {tz : ℝ}
    (hA : Arrival (chainModel J.whole).W z (-σ) pz tz)
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ Merge.shoot J.whole o d) :
    ∃ j, j < 2 * N₂.nChords ∧ T j = some (pz, tz) ∧ endDir j = -σ ∧
      endOrigin J Q N₂ j ∈ J.right.set ∧ endOrigin J Q N₂ j ≠ J.shared ∧
      endOrigin J Q N₂ j ≠ J.right.top ∧ endOrigin J Q N₂ j = o := by
  have hd : d = 1 ∨ d = -1 := by rcases ho with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have ho2 : o.2 ≤ J.right.top.2 := J.right.snd_le_top_of_mem_set hoR
  have ho2' : o.2 ≤ J.whole.top.2 := ho2.trans J.right_top_le
  have key : ∀ j, j < 2 * N₂.nChords → endOrigin J Q N₂ j = o → endDir j = d →
      ∃ j, j < 2 * N₂.nChords ∧ T j = some (pz, tz) ∧ endDir j = -σ ∧
        endOrigin J Q N₂ j ∈ J.right.set ∧ endOrigin J Q N₂ j ≠ J.shared ∧
        endOrigin J Q N₂ j ≠ J.right.top ∧ endOrigin J Q N₂ j = o := by
    intro j hj hoj hdj
    obtain ⟨-, hm⟩ := hT j hj (by rwa [hoj]) (by rwa [hoj])
      (by rwa [hoj])
    rw [hoj, hdj] at hm
    rcases hTj : T j with _ | ⟨p, t⟩
    · rw [hTj] at hm
      exfalso
      have hfr₂ : FreeAt J.right o d := by
        filter_upwards [hfo] with s hs
        exact dom_right J hs (by rwa [rayPt_snd])
      obtain ⟨-, hD₂, -⟩ := Merge.hit_of_freeAt J.right ho2 hd hfr₂
      have hm' : J.whole.hitParam o d = J.right.hitParam o d := hm
      rw [← hm', hoz] at hD₂
      exact hD₂ hzR
    · rw [hTj] at hm
      obtain ⟨hatt, hpt, -⟩ := hm
      rw [hoz] at hpt
      have harr : Arrival (chainModel J.whole).W z (-σ) p t := arrival_of_attach hσ hatt hpt hev
      have hg : Genuine J.whole o d (J.whole.hitParam o d) :=
        (genuine_iff J.whole ho2' hd).2 ⟨hfo, rfl⟩
      have h1 : Arrival (chainModel J.whole).W (rayPt o d (J.whole.hitParam o d)) d p t := by
        rwa [hoz, hdσ]
      have h2 : Arrival (chainModel J.whole).W (rayPt o d (J.whole.hitParam o d)) d pz tz := by
        rwa [hoz, hdσ]
      obtain ⟨rfl, rfl⟩ := arrival_unique hP ho2' hd hg h1 h2
      exact ⟨j, hj, hTj, by rw [hdj, hdσ], by rwa [hoj], by rwa [hoj],
        by rwa [hoj], hoj⟩
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 hr
  have hck : N₂.chord k = r := by unfold NF.chord; rw [List.getD_eq_getElem _ _ hk, hkr]
  have hkn : k < N₂.nChords := hk
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine key (2 * k) (by omega) ?_ ?_
    · unfold endOrigin
      rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega, hck]
    · unfold endDir; rw [ite_eq_left (by omega)]
  · refine key (2 * k + 1) (by omega) ?_ ?_
    · unfold endOrigin
      rw [ite_eq_right (by omega), show (2 * k + 1) / 2 = k by omega, hck]
    · unfold endDir; rw [ite_eq_right (by omega)]

/-- **(C3): the top chords.** -/
theorem case_C3 (hP : J.P.Simple) {Q : Polygon} {N₂ : NF}
    (hN : IsNF (chainModel J.right) Q N₂) {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hS : StopsOK J (N₂.F (chainModel J.right) Q) (stopsOf J Q N₂ rs)) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hzR : z ∈ J.right.dom) {e : Set Point}
    (he : e ∈ F₂plus J (N₂.F (chainModel J.right) Q)) (hfo : FreeAt J.whole J.right.top (-σ))
    (heo : e = Merge.shoot J.whole J.right.top (-σ)) (hze : z ∈ e)
    (hends : ∀ p ∈ e, p ∉ J.whole.dom → p = z ∨ p = J.right.top) (hey : ∀ p ∈ e, p.2 = z.2)
    (htopL : J.right.top ∉ J.left.set) (hT0 : 0 < J.whole.hitParam z σ)
    (hw : rayPt z σ (J.whole.hitParam z σ) = J.right.top) {pz : ℕ} {tz : ℝ}
    (hA : Arrival (chainModel J.whole).W z (-σ) pz tz) (hLst : (Lst J : ℝ) ≤ oW J (pz + tz))
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) :
    ∃ r ∈ rs, r.1 = pz ∧ (chainModel J.whole).param Q ⟨r.1, r.2.1⟩ = tz ∧
      dirOf r.2.2.2.2 = -σ ∧
      SweepIo.stopOrig J Q N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 = J.right.top := by
  have hS₂ : N₂.F (chainModel J.right) Q ⊆ Merge.augChords J.right := hN.1.2.1
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hstop : StopChord2 J (N₂.F (chainModel J.right) Q) e := Or.inr ⟨-σ, hnσ, hfo, heo⟩
  have hatt : SideAttach (chainModel J.whole).W e pz tz := by
    obtain ⟨hp, ht0, ht1, hpt, hsec⟩ := hA
    rw [neg_neg] at hsec
    refine sideAttach_of_along J.whole hP (F₂plus_subset J hS₂ he) hp ht0 ht1 hσ ?_ ?_
    · rwa [hpt]
    · rwa [hpt]
  obtain ⟨r, hr, hre⟩ := List.mem_map.1 (hS.2.1 e he hstop pz tz hatt hLst)
  simp only [Prod.mk.injEq] at hre
  obtain ⟨h1, h2, h3⟩ := hre
  refine ⟨r, hr, h1, h2, ?_⟩
  set o' := SweepIo.stopOrig J Q N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 with ho'
  set d' := dirOf r.2.2.2.2
  have hsh : Merge.shoot J.whole o' d' = e := (stopSet_eq J Q N₂ _ _ _).symm.trans h3
  have ho'e : o' ∈ e := by rw [← hsh]; exact origin_mem J
  have htope : J.right.top ∈ e := by rw [heo]; exact origin_mem J
  have hsh_off : J.shared ∉ J.whole.dom := fun h =>
    J.whole.not_mem_set_of_mem_dom h (J.left_set_subset J.shared_mem_left)
  -- the origin of the record is the top of `C₂`
  have ho'top : o' = J.right.top := by
    rw [ho']
    unfold SweepIo.stopOrig
    by_cases hk0 : r.2.2.1 = 0
    · rw [ite_eq_left hk0]
      exfalso
      have hsm : J.shared ∈ e := by
        have := ho'e; rw [ho'] at this; unfold SweepIo.stopOrig at this
        rwa [ite_eq_left hk0] at this
      rcases hends _ hsm hsh_off with h | h
      · exact J.right.not_mem_set_of_mem_dom (h ▸ hzR) J.shared_mem_right
      · exact htopL (h ▸ J.shared_mem_left)
    by_cases hk1 : r.2.2.1 = 1
    swap
    · rw [ite_eq_right hk0, ite_eq_right hk1]
    rw [ite_eq_right hk0, ite_eq_left hk1]
    · have hme : endOrigin J Q N₂ (2 * r.2.2.2.1 + if dirOf r.2.2.2.2 = 1 then 0 else 1) ∈ e := by
        have := ho'e; rw [ho'] at this; unfold SweepIo.stopOrig at this
        rwa [ite_eq_right hk0, ite_eq_left hk1] at this
      set j := 2 * r.2.2.2.1 + if dirOf r.2.2.2.2 = 1 then 0 else 1 with hj
      have hj2 : j / 2 = r.2.2.2.1 := by rw [hj]; split_ifs <;> omega
      by_cases hk : r.2.2.2.1 < N₂.nChords
      · -- a chord of `S₂`: its end is off the domain of `C₂`
        have hcF : (N₂.chord (j / 2)).toSet (chainModel J.right) Q ∈
            N₂.F (chainModel J.right) Q := by
          refine ⟨N₂.chord (j / 2), ?_, rfl⟩
          unfold NF.chord
          rw [hj2, List.getD_eq_getElem _ _ hk]
          exact List.getElem_mem _
        obtain ⟨hl, hr', hl2, hr2⟩ := end_off_right J (hS₂ hcF)
        have hoff : endOrigin J Q N₂ j ∉ J.right.dom ∧
            (endOrigin J Q N₂ j).2 ≤ J.right.top.2 := by
          unfold endOrigin; split_ifs
          · exact ⟨hl, hl2⟩
          · exact ⟨hr', hr2⟩
        have hD : endOrigin J Q N₂ j ∉ J.whole.dom := fun h =>
          hoff.1 (J.mem_right_dom_of_whole hoff.2 h)
        rcases hends _ hme hD with h | h
        · exact absurd (h ▸ hzR) hoff.1
        · exact h
      · -- out of range: the slit top's vertical line
        push Not at hk
        have h1' := endOrigin_big J Q N₂ (j := j) (by rwa [hj2])
        exact Prod.ext h1' (by rw [hey _ hme, hey _ htope])
  -- the direction
  have hd'c : d' = 1 ∨ d' = -1 := dirOf_cases _
  rw [ho'top] at hsh
  have hzs : z ∈ Merge.shoot J.whole J.right.top d' := by rwa [hsh]
  unfold Merge.shoot at hzs
  obtain ⟨lam, hlam0, hlam1, hzl⟩ := Geometry.mem_segment_iff_lerp.1 hzs
  have hz1 := congrArg Prod.fst hzl
  rw [Geometry.lerp_fst, rayPt_fst] at hz1
  have hw1 := congrArg Prod.fst hw
  rw [rayPt_fst] at hw1
  have hτ' := Merge.hitParam_nonneg J.whole J.right.top d'
  refine ⟨?_, ho'top⟩
  show d' = -σ
  rcases hd'c with h | h <;> rcases hσ with rfl | rfl <;> rw [h] at hz1 hτ' ⊢ <;>
    first | rfl | (exfalso; nlinarith [mul_nonneg hlam0 hτ']) | norm_num

end

end S0Math

namespace SweepIo

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Merge (FreeAt)
open WalkEmbed Sweep S0Math

@[expose] public section

/-- **The cases of the first hit of a side-0 query.** -/
theorem side0Math : Side0MathSpec := by
  intro P J N₂ rs ls T _hG hP hN hlog hstops htab z σ hσ hzL hzv hz2 hfree pz tz hA
  have hS₂ : N₂.F (chainModel J.right) (Qof P) ⊆ Merge.augChords J.right := hN.1.2.1
  have hS₂f : (N₂.F (chainModel J.right) (Qof P)).Finite := hN.1.1
  have hzR := left_pt_right_dom J hP hzL hzv hz2
  obtain ⟨hpz, htz0, htz1, hpt, hsec⟩ := hA
  have hLst : (Lst J : ℝ) < oW J (pz + tz) :=
    Lst_lt_of_dom hP hpz htz0 htz1 (by rwa [hpt])
  refine ⟨hLst.le, fun i hi => ?_⟩
  have hz₁ : z.2 ≤ J.left.top.2 := J.left.snd_le_top_of_mem_set hzL
  have hzD : z ∉ J.whole.dom := fun h =>
    J.whole.not_mem_set_of_mem_dom h (J.left_set_subset hzL)
  by_cases hc : rayPt z σ (J.whole.hitParam z σ) ∈ J.right.set ∧
      rayPt z σ (J.whole.hitParam z σ) ∉ J.left.set
  swap
  · exact Or.inl (left_hit_of J hz₁ hσ hfree hc)
  have hR2 := right_hit_of J hz2 hσ hfree hc.1
  by_cases hB : ∃ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)),
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e
  · -- the ray runs along a chord of `F₂⁺`
    obtain ⟨e, he, hev⟩ := hB
    obtain ⟨o, d, hd, hfo, heo, hkind⟩ := F₂plus_origin J he
    have hoe : o ∈ e := by rw [heo]; exact origin_mem J
    have ho2 : o.2 ≤ J.right.top.2 := F₂plus_snd_le J hS₂ he hoe
    have hoR' : o ∉ J.right.dom := by
      rcases hkind with rfl | rfl | ⟨c, hc', ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
      · exact fun h => J.right.not_mem_set_of_mem_dom h J.shared_mem_right
      · exact fun h => J.right.not_mem_set_of_mem_dom h J.right.top_mem_set
      · exact (end_off_right J (hS₂ hc')).1
      · exact (end_off_right J (hS₂ hc')).2.1
    have hoD : o ∉ J.whole.dom := fun h => hoR' (J.mem_right_dom_of_whole ho2 h)
    have hzo : z ≠ o := fun h => hoR' (h ▸ hzR)
    obtain ⟨hwo, hdσ, hoz, hT0, hends, hey⟩ :=
      along_end J (F₂plus_subset J hS₂ he) hσ hd hzD hoD hzo heo hfo hev
    have hze : z ∈ e := by rw [heo, ← hoz]; exact Geometry.right_mem_segment _ _
    rw [hwo] at hc
    by_cases hot : o = J.right.top
    · -- (C3): a top chord
      subst hot
      right; right; left
      have heo' : e = Merge.shoot J.whole J.right.top (-σ) := by rw [heo, hdσ]
      have hfo' : FreeAt J.whole J.right.top (-σ) := by rwa [← hdσ]
      obtain ⟨r, hr, h1, h2, h3, h4⟩ := case_C3 J hP hN hstops hσ hzR he hfo' heo' hze
        (fun p hp hpD => hends p hp hpD) hey hc.2 hT0 hwo ⟨hpz, htz0, htz1, hpt, hsec⟩ hLst.le hev
      exact ⟨r, hr, h1, h2, h3, by rw [h4, hwo]⟩
    · rcases hkind with rfl | rfl | ⟨c, hc', hco⟩
      · exact absurd J.shared_mem_left hc.2
      · exact absurd rfl hot
      · -- (C4): an endpoint query
        right; right; right
        have hov : o ≠ J.shared := fun h => hc.2 (h ▸ J.shared_mem_left)
        obtain ⟨j, hj, hTj, hdj, h1, h2, h3, h4⟩ := case_C4 J hP htab hσ hzR hc' hco hfo hc.1
          hov hot hdσ hoz ⟨hpz, htz0, htz1, hpt, hsec⟩ (by rwa [← heo])
        exact ⟨j, hj, hTj, hdj, h1, h2, h3, by rw [h4, hwo]⟩
  · -- the ray starts in a region of `F₂⁺`
    rw [neg_neg] at hsec
    have hFam := chordFamily_hPoly J.whole (F₂plus_finite J hS₂f) (F₂plus_subset J hS₂)
    obtain ⟨U, hU, hray, hface⟩ := leave_region J.whole hP hFam hσ hpz htz0 htz1 hpt hsec
      (left_pt_abs J hzL) (fun e he h => hB ⟨e, he, h⟩)
    have hface' : AfterFaces (chainModel J.whole) pz tz U ∨
        BeforeFaces (chainModel J.whole) pz tz U := by
      rcases hface with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨V, hV, hVray, hlab⟩ := query_right J hP hS₂ hS₂f hU hz2 hσ hray hc.1 hc.2
    obtain ⟨hil, hlo, hhi⟩ := hi
    have hlen : (logOf J (Qof P) N₂ ls).length = ls.length := List.length_map _
    have hres := labels_of_log J hP hS₂ hS₂f hlog (i := i) (by rwa [hlen]) hpz htz0
      htz1 hLst hlo (fun h => hhi (by rwa [hlen] at h)) hU hface' V hV hlab
    right; left
    exact ⟨hR2, V, hV, hres, hVray⟩

end

end SweepIo

end Chazelle.Core
