module

public import Chazelle.Core.SweepEvStepL6

/-!
# The sweep (WP-D), stage 3: the label set at the next key (Task L1)

**`SCtx.labels`**: the labels of the next key are region indices of `N₂`, and the label set of the
next key satisfies the invariant of the event loop there (`evInv_step`):

* a pocket chord at the key: any label set;
* an anchored chord at the key (`An`, the best candidate at the key or an anchored skipped stop):
  every anchored chord at the key is a skipped stop (labels of its auxiliary record, `AuxOK`) or
  the chord of an accepted triple (labels `up`, `dn` of its chord, `evSideLab_fused`); at most
  two chords at the key, each with at most two labels (`labsOf_card`), so the list of at most four
  labels holds them all (`addLs_all`, `mem_full`);
* otherwise only bracket stops are at the key and the label set is kept.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The entries of a label list are register values. -/
theorem stp_lblOf_mem {c : Config} {x : ℕ} (hx : x ∈ lblOf c kN kL) :
    ∃ i, i < c.nreg kN ∧ i < 4 ∧ c.nreg (kL + i) = x := by
  unfold lblOf at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hi
  exact ⟨i, by omega, by omega, rfl⟩

namespace SCtx

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set (ℕ × ℕ × ℕ)} {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

/-- The auxiliary records after the origins. -/
theorem auxRecs_co : AuxRecsAt co.nmem (co.nreg aB) ax := by
  obtain ⟨hlen, hax, -, hrecA, -⟩ := S.hD
  have eaB : co.nreg aB = c.nreg aB := stp_co_keep S.hI (k := 2602) (by omega)
  have l1 := S.L.lay1
  have l3 := S.L.lay3
  have l5 := S.L.lay5
  intro i hi
  have hi' : i < c.nreg sC := by rw [← hlen, ← hax]; exact hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hrecA i hi
  rw [eaB]
  have hm : ∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → co.nmem x = c.nmem x :=
    fun x h1 h2 => stp_co_mem S.L S.hI x (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm _ (by omega) (by omega)]; exact a0
  · rw [hm _ (by omega) (by omega)]; exact a1
  · rw [hm _ (by omega) (by omega)]; exact a2
  · rw [hm _ (by omega) (by omega)]; exact a3
  · rw [hm _ (by omega) (by omega)]; exact a4

/-- The label list of the key is kept until the next-key step. -/
theorem lblOf_co : lblOf co kN kL = lblOf c kN kL ∧ co.nreg kN = c.nreg kN := by
  have ekN : co.nreg kN = c.nreg kN := stp_co_keep S.hI (k := 2402) (by omega)
  refine ⟨?_, ekN⟩
  unfold lblOf
  rw [ekN]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := stp_co_keep S.hI (k := 2403 + i) (by omega)
  rwa [show sw (2403 + i) = kL + i by unfold kL sw; omega] at this

/-- The auxiliary facts of a skipped stop. -/
theorem skip_aux {i : ℕ} (h1 : c.nreg sP ≤ i) (h2 : i < c'.nreg sP) :
    ∃ hi : i < rs.length, ∃ hia : i < ax.length,
      co.nmem (co.nreg aB + 5 * i) = ax[i].1 ∧
      AuxOK P J N₂ (stopSet J (Qof P) N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2) ax[i] := by
  obtain ⟨hi, -⟩ := S.skip_at h1 h2
  have hax := S.hD.2.1
  have hia : i < ax.length := by rw [hax]; exact hi
  obtain ⟨a0, -⟩ := S.auxRecs_co i hia
  rw [List.getD_eq_getElem _ _ hia] at a0
  have hok := S.hD.2.2.2.2.2.2.1 i hi
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hia] at hok
  exact ⟨hi, hia, a0, hok⟩

set_option maxHeartbeats 4000000 in
/-- **The labels at the next key.** -/
theorem labels :
    (∀ i, i < c'.nreg kN → c'.nreg (kL + i) < N₂.nRegions) ∧
    EvInv J (N₂.F (chainModel J.right) (Qof P)) (keyOff P J c') (curLab P J N₂ c') := by
  classical
  have hP := S.E.hP
  have hS₂ : (chainModel J.right).ChordFamily (Qof P) (N₂.F (chainModel J.right) (Qof P)) :=
    S.E.hNF₂.1
  have hF := F₂plus_chordFamily S.E
  have hM : WalkAx (chainModel J.whole) := FactsChain.walkAx J.whole hP
  obtain ⟨hlt, hpw, -⟩ := stp_next_key S.E S.L S.hI S.hd
  have hsome := stp_key_some S.hI S.hd
  obtain ⟨esP, -, -, -, -, -⟩ := iter_stops S.L S.hI
  obtain ⟨-, -, -, -, -, -, -, -, -, hkN4, hlab1, hlab2, -⟩ := S.hI.2.2.2.2.2.2.2 hsome
  have hrecA := S.auxRecs_co
  obtain ⟨hLco, ekN⟩ := S.lblOf_co
  have hCS := (regOf_spec S.E.hNF₂).2.1
  set pK := c'.nreg kE with hpK
  set tK := (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩ with htK
  -- the label universe at the key
  obtain ⟨e₁, e₂, h12⟩ := stp_two_chords hM hF.2.1 pK tK
  obtain ⟨hf₁, hc₁⟩ := S.labsOf_card e₁
  obtain ⟨hf₂, hc₂⟩ := S.labsOf_card e₂
  set U : Finset ℕ := hf₁.toFinset ∪ hf₂.toFinset with hU
  have hUc : U.card ≤ 4 := by
    refine (Finset.card_union_le _ _).trans ?_
    rw [← ncard_eq_toFinset_card _ hf₁, ← ncard_eq_toFinset_card _ hf₂]
    omega
  have inU : ∀ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)),
      SideAttach (chainModel J.whole).W e pK tK → ∀ x, x ∈ labsOf P J N₂ c co c' A rs e →
      x ∈ U := by
    intro e he heK x hx
    rcases h12 e he heK with rfl | rfl
    · exact Finset.mem_union_left _ (hf₁.mem_toFinset.2 hx)
    · exact Finset.mem_union_right _ (hf₂.mem_toFinset.2 hx)
  -- the best list and the stop labels
  set Bst := co.nreg bF = 1 ∧
    offK P J (co.nreg bE) (co.nreg bH) = offK P J (c'.nreg kE) (c'.nreg kH) with hBst
  set L0 : List ℕ := if Bst then lblOf co bN bL else [] with hL0
  set vs : List ℕ := (List.range' (co.nreg sP) (c'.nreg sP - co.nreg sP)).flatMap
    (stopLabs co.nmem (co.nreg aB)) with hvs
  have mem_vs : ∀ x, x ∈ vs ↔ ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
      x ∈ stopLabs co.nmem (co.nreg aB) i := by
    intro x
    rw [hvs, List.mem_flatMap]
    constructor
    · rintro ⟨i, hi, hx⟩
      rw [List.mem_range'_1, esP] at hi
      exact ⟨i, hi.1, by omega, hx⟩
    · rintro ⟨i, h1, h2, hx⟩
      exact ⟨i, by rw [List.mem_range'_1, esP]; omega, hx⟩
  have hL0src : ∀ x ∈ L0, ∃ t ∈ A, offT P J t = keyOff P J c' ∧ (x = upOf N₂ t.1 ∨ x = dnOf N₂ t.1) := by
    intro x hx
    rw [hL0] at hx
    split_ifs at hx with hb
    · obtain ⟨t, ht, hto, hx'⟩ := S.hBA.lSrc hb.1 x hx
      exact ⟨t, ht, hto.trans hb.2, hx'⟩
    · exact absurd hx (List.not_mem_nil)
  have hL0U : ∀ x ∈ L0, x ∈ U := by
    intro x hx
    obtain ⟨t, ht, hto, hx'⟩ := hL0src x hx
    obtain ⟨hmF, hat, -, -⟩ := S.triple_at ht hto
    exact inU _ hmF hat x (Or.inl ⟨t, ht, hto, rfl, hx'⟩)
  have hvsU : ∀ x ∈ vs, x ∈ U := by
    intro x hx
    obtain ⟨i, h1, h2, hx'⟩ := (mem_vs x).1 hx
    obtain ⟨hi, hmF, -, hat, -⟩ := S.skip_at h1 h2
    exact inU _ hmF hat x (Or.inr ⟨i, hi, h1, h2, rfl, hx'⟩)
  have hL0nd : L0.Nodup := by
    rw [hL0]; split_ifs with hb
    · exact S.hBA.lNd hb.1
    · exact List.nodup_nil
  have hL0len : L0.length ≤ 4 := by
    rw [hL0]; split_ifs
    · exact lblOf_len co
    · simp
  obtain ⟨-, -, -, hinL0, hinvs⟩ := stp_addLs_all hUc vs L0 hL0nd hL0len hL0U hvsU
  -- the label set of the next key
  have hΛ' := stp_curLab_eq (P := P) (J := J) (N₂ := N₂) hkN4
  have toΛ : ∀ l, l ∈ lblOf c' kN kL →
      regOf (chainModel J.right) (Qof P) N₂ l ∈ curLab P J N₂ c' := fun l hl => by
    rw [hΛ']; exact ⟨l, hl, rfl⟩
  -- the bounds of the stop labels
  have hvs_lt : ∀ x ∈ vs, x < N₂.nRegions := by
    intro x hx
    obtain ⟨i, h1, h2, hx'⟩ := (mem_vs x).1 hx
    obtain ⟨hi, hia, -, hok⟩ := S.skip_aux h1 h2
    obtain ⟨-, -, -, hb0, hb1, -⟩ := hok
    rcases ((stp_mem_stopLabs hrecA hia).1 hx').2 with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact hb0 h
    · exact hb1 h
  have hL0_lt : ∀ x ∈ L0, x < N₂.nRegions := by
    intro x hx
    obtain ⟨t, ht, -, hx'⟩ := hL0src x hx
    have hj := (S.hBA.acc t ht).2.1
    obtain ⟨hu, hd', -⟩ := hCS (t.1 / 2) (by omega)
    rcases hx' with rfl | rfl
    · exact hu
    · exact hd'
  -- the rule of the labels
  set An := Bst ∨ ∃ i, co.nreg sP ≤ i ∧ i < c'.nreg sP ∧ co.nmem (co.nreg aB + 5 * i) = 1
    with hAnd
  refine ⟨fun i hi => ?_, ?_⟩
  · -- the labels are region indices
    have hmem : c'.nreg (kL + i) ∈ lblOf c' kN kL := stp_mem_lblOf hi hkN4
    by_cases hAn : An
    · rw [hlab1 hAn] at hmem
      rcases stp_addLs_sub vs L0 hmem with h | h
      · exact hL0_lt _ h
      · exact hvs_lt _ h
    · obtain ⟨h1, -⟩ := hlab2 hAn
      rw [h1, hLco] at hmem
      obtain ⟨i', hi', -, hx⟩ := stp_lblOf_mem hmem
      rw [← hx]
      exact S.L.labR i' hi'
  · have hLst : (Lst J : ℝ) ≤ oW J (pK + tK) := le_trans S.L.keyL hlt.le
    refine evInv_step hP hS₂ hF S.L.inv hpw.1 hpw.2.1.1 hpw.2.1.2.1 hLst hlt.le S.gapK ?_
    by_cases hpock : ∃ e ∈ F₂plus J (N₂.F (chainModel J.right) (Qof P)),
        SideAttach (chainModel J.whole).W e pK tK ∧
        ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J (q + s) = 0
    · exact Or.inl hpock
    push Not at hpock
    by_cases hAn : An
    · right; left
      have hlist : lblOf c' kN kL = addLs L0 vs := hlab1 hAn
      refine ⟨?_, fun e he heK hnb => ?_⟩
      · -- an anchored chord at the key
        rcases hAn with ⟨hbF, hbo⟩ | ⟨i, h1, h2, hfl⟩
        · obtain ⟨⟨j, hj⟩, -⟩ := S.hBA.bAcc hbF
          obtain ⟨hmF, hat, -, hnb'⟩ := S.triple_at hj hbo
          exact ⟨_, hmF, hat, hnb'⟩
        · rw [esP] at h1
          obtain ⟨hi, hmF, -, hat, -⟩ := S.skip_at h1 h2
          obtain ⟨hi', hia, hfl', hok⟩ := S.skip_aux h1 h2
          exact ⟨_, hmF, hat, hok.2.1.1 (hfl'.symm.trans hfl)⟩
      · -- every anchored chord at the key has its labels
        by_cases hst : StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e
        · obtain ⟨i, hi, h1, h2, hse⟩ := S.stop_idx he heK hst
          obtain ⟨hi', hia, hfl, hok⟩ := S.skip_aux h1 h2
          obtain ⟨-, hiff, hnl, -, -, hlab, -⟩ := hok
          rw [hse] at hiff hlab
          have hanc : ax[i].1 = 1 := hiff.2 hnb
          refine evSideLab_mono ?_ (hlab hanc (fun q s hq => hpock e he heK q s hq))
          rintro _ ⟨l, hl, rfl⟩
          apply toΛ
          rw [hlist]
          apply hinvs
          rw [mem_vs]
          refine ⟨i, h1, h2, (stp_mem_stopLabs hrecA hia).2 ⟨hanc, ?_⟩⟩
          rcases hl with h | h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h.1 (by omega)
          · exact absurd h.1 (by omega)
        · obtain ⟨t, ht, hto, hte, hbF, hbo⟩ := S.nonstop_acc he heK hst
          obtain ⟨-, hj, hfree, -⟩ := S.hBA.acc t ht
          obtain ⟨haR, hav, hat⟩ := S.hval t ht
          obtain ⟨-, ha⟩ := query_chord (J := J) (Q := Qof P) hj
          have hlab := evSideLab_fused hP S.E.hNF₂ hF (k := t.1 / 2) (by omega) ha haR hav hat
            hfree
          rw [hte] at hlab
          have hB : Bst := ⟨hbF, hbo⟩
          have hL0e : L0 = lblOf co bN bL := by rw [hL0, ite_eq_left hB]
          have hinL : ∀ x, (x = upOf N₂ t.1 ∨ x = dnOf N₂ t.1) → x ∈ L0 := by
            intro x hx
            have hxU : x ∈ U := inU _ he heK x (Or.inl ⟨t, ht, hto, hte, hx⟩)
            obtain ⟨c1, c2⟩ := S.hBA.lCov hbF t ht (hto.trans hbo.symm)
            rw [hL0e]
            rcases hx with rfl | rfl
            · rcases c1 with h | h
              · exact h
              · exact stp_mem_full (S.hBA.lNd hbF) h (by rw [← hL0e]; exact hL0U) hUc hxU
            · rcases c2 with h | h
              · exact h
              · exact stp_mem_full (S.hBA.lNd hbF) h (by rw [← hL0e]; exact hL0U) hUc hxU
          refine evSideLab_mono ?_ hlab
          rintro _ ⟨l, hl, rfl⟩
          apply toΛ
          rw [hlist]
          apply hinL0
          rcases hl with h | h | h | h
          · exact hinL _ (Or.inl h.2)
          · exact hinL _ (Or.inr h.2)
          · exact absurd h.1 (by norm_num)
          · exact absurd h.1 (by norm_num)
    · right; right
      refine ⟨fun e he heK => ?_, ?_⟩
      · by_contra hnb
        by_cases hst : StopChord2 J (N₂.F (chainModel J.right) (Qof P)) e
        · obtain ⟨i, hi, h1, h2, hse⟩ := S.stop_idx he heK hst
          obtain ⟨hi', hia, hfl, hok⟩ := S.skip_aux h1 h2
          rw [hse] at hok
          exact hAn (Or.inr ⟨i, by rw [esP]; exact h1, h2, hfl.trans (hok.2.1.2 hnb)⟩)
        · obtain ⟨t, -, -, -, hbF, hbo⟩ := S.nonstop_acc he heK hst
          exact hAn (Or.inl ⟨hbF, hbo⟩)
      · obtain ⟨h1, h2⟩ := hlab2 hAn
        rw [hΛ', stp_curLab_eq S.L.labN, h1, hLco]
end SCtx

end

end SweepEv

end Chazelle.Core
