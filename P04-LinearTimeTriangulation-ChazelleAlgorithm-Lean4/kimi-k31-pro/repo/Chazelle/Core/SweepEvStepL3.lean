module

public import Chazelle.Core.SweepEvStepL2
public import Chazelle.Core.SweepEvCount

/-!
# The sweep (WP-D), stage 3: one iteration, the frame and the next key (Task L1)

For one iteration `c → cw → cs → co → c'` that does not finish:

* `stp_co_keep`, `stp_key_keep`, `stp_co_mem`, `stp_c'_mem`, `stp_alloc_mono`: what is kept;
* `stp_key_some`: some candidate exists;
* `stp_next_key`: the next key is beyond the key, a word position, and one of the possible keys
  (`keyS`);
* `meas_lt`, `lC_lt`: the measure decreases, the log has room;
* `stopOff'`, `stops'`, `ptrL'`: the stops and the stop pointer at the next key.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config}

/-- The registers kept from the start of the iteration to the configuration after the origins. -/
theorem stp_co_keep (hI : IterRel P J N₁ N₂ c cw cs co c') {k : ℕ}
    (hk : (600 ≤ k ∧ k < 700) ∨ (2400 ≤ k ∧ k ≤ 2406) ∨ (2430 ≤ k ∧ k ≤ 2459) ∨
      (2600 ≤ k ∧ k ≤ 2699)) : co.nreg (sw k) = c.nreg (sw k) := by
  obtain ⟨hW, -, hR, hB, -⟩ := hI
  obtain ⟨hkp, -, -, -⟩ := stp_pre_frame hW hR
  obtain ⟨hregB, -, -⟩ := hB
  have h := stp_batch_keep hR hregB (k := k) (by omega)
  exact (h.2.trans h.1.symm).trans (hkp k hk)

/-- The registers kept by the next-key step. -/
theorem stp_key_keep (hK : KeyOut P J co c') {k : ℕ}
    (hk : (600 ≤ k ∧ k < 700) ∨ k = 2430 ∨ (2432 ≤ k ∧ k ≤ 2449) ∨ (2452 ≤ k ∧ k ≤ 2479) ∨
      (2500 ≤ k ∧ k ≤ 2699)) : c'.nreg (sw k) = co.nreg (sw k) :=
  hK.1 _ (band_sw_not ⟨by unfold sw; omega, by unfold sw; omega⟩)
    (by unfold KR kE kH kN kL sP dF lC sw; omega) (by unfold ALLOC sw; omega)

/-- The registers kept by the whole iteration. -/
theorem stp_iter_keep (hI : IterRel P J N₁ N₂ c cw cs co c') {k : ℕ}
    (hk : (600 ≤ k ∧ k < 700) ∨ k = 2430 ∨ (2432 ≤ k ∧ k ≤ 2449) ∨ (2452 ≤ k ∧ k ≤ 2459) ∨
      (2600 ≤ k ∧ k ≤ 2699)) : c'.nreg (sw k) = c.nreg (sw k) :=
  (stp_key_keep hI.2.2.2.2 (by omega)).trans (stp_co_keep hI (by omega))

/-- The memory beyond the table, below the allocator, up to the configuration after the
origins. -/
theorem stp_co_mem (_L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') :
    ∀ x, x < c.nreg ALLOC → c.nreg cTB + 6 * N₂.nChords ≤ x → co.nmem x = c.nmem x := by
  obtain ⟨hW, hAl, hR, hB, -⟩ := hI
  obtain ⟨hkp, hmem, -, -⟩ := stp_pre_frame hW hR
  obtain ⟨-, -, A, hBA⟩ := hB
  have eTB : cs.nreg cTB = c.nreg cTB := hkp 661 (by omega)
  have eAs : cs.nreg ALLOC = cw.nreg ALLOC := hR.2.2.2 _ (by unfold ALLOC bF sw; omega)
    (by unfold ALLOC bN sw; omega)
  intro x hx hx'
  rw [hBA.memT x (by omega) (Or.inr (by omega)), hmem x hx]

/-- The allocator grows. -/
theorem stp_alloc_mono (hI : IterRel P J N₁ N₂ c cw cs co c') :
    c.nreg ALLOC ≤ co.nreg ALLOC ∧ co.nreg ALLOC ≤ c'.nreg ALLOC := by
  obtain ⟨-, hAl, hR, hB, hK⟩ := hI
  have eAs : cs.nreg ALLOC = cw.nreg ALLOC := hR.2.2.2 _ (by unfold ALLOC bF sw; omega)
    (by unfold ALLOC bN sw; omega)
  exact ⟨by have := hB.2.1; omega, hK.2.1⟩

/-- **Some candidate exists** when the iteration does not finish. -/
theorem stp_key_some (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    co.nreg bF = 1 ∨ co.nreg sP < co.nreg sC ∨ co.nreg wX = 0 := by
  by_contra h
  push Not at h
  have := (hI.2.2.2.2.2.2.1 ⟨h.1, by omega, h.2.2⟩).1
  omega

/-- The memory beyond the table, below the allocator, outside the new log record, through the
iteration. -/
theorem stp_c'_mem (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c')
    (hd : c'.nreg dF = 0) :
    ∀ x, x < c.nreg ALLOC → c.nreg cTB + 6 * N₂.nChords ≤ x →
      (x < c.nreg lB + 7 * c.nreg lC ∨ c.nreg lB + 7 * c.nreg lC + 7 ≤ x) →
      c'.nmem x = c.nmem x := by
  intro x hx h1 h2
  have hA := stp_alloc_mono hI
  have elB : co.nreg lB = c.nreg lB := stp_co_keep hI (k := 2430) (by omega)
  have elC : co.nreg lC = c.nreg lC := stp_co_keep hI (k := 2431) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmK⟩ :=
    hI.2.2.2.2.2.2.2 (stp_key_some hI hd)
  rw [hmK x (by omega) (by rw [elB, elC]; exact h2), stp_co_mem L hI x hx h1]

/-- The stop offsets after the origins. -/
theorem stp_stopOff_co (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') {i : ℕ}
    (hi : i < c.nreg sC) : stopOff P J co i = stopOff P J c i :=
  ((iter_stops L hI).2.2.1 i hi)

/-- The stop records after the origins. -/
theorem stp_stopEH_co (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') {i : ℕ}
    (hi : i < c.nreg sC) : stopE co i = stopE c i ∧ stopH co i = stopH c i := by
  have esB : co.nreg sB = c.nreg sB := stp_co_keep hI (k := 2600) (by omega)
  have hlay := L.lay1
  have hlay2 := L.lay2
  have hlay4 := L.lay4
  unfold stopE stopH
  rw [esB, stp_co_mem L hI _ (by omega) (by omega), stp_co_mem L hI _ (by omega) (by omega)]
  exact ⟨rfl, rfl⟩

/-- **The next key**: beyond the key, a word position, one of the possible keys. -/
theorem stp_next_key (_E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    keyOff P J c < keyOff P J c' ∧ PosW P J (c'.nreg kE) (c'.nreg kH) ∧
      keyOff P J c' ∈ keyS P J N₁ N₂ := by
  have hsome := stp_key_some hI hd
  obtain ⟨esP, esC, -, ewX, ewE, ewH⟩ := iter_stops L hI
  have hst := fun {i : ℕ} (hi : i < c.nreg sC) => stp_stopEH_co L hI hi
  obtain ⟨hW, -, hR, hB, hK⟩ := hI
  obtain ⟨hkp, -, -, -⟩ := stp_pre_frame hW hR
  obtain ⟨-, -, A, hBA⟩ := hB
  obtain ⟨-, hkey, -⟩ := hK.2.2.2 hsome
  have ekE : cs.nreg kE = c.nreg kE := hkp 2400 (by omega)
  have ekH : cs.nreg kH = c.nreg kH := hkp 2401 (by omega)
  rcases hkey with ⟨hbF, h1, h2⟩ | ⟨hsp, h1, h2⟩ | ⟨hwx, h1, h2⟩
  · -- the best candidate
    obtain ⟨⟨j, hj⟩, hlt⟩ := hBA.bAcc hbF
    obtain ⟨-, hmemF, hAt, -, -, hpw, -⟩ := (hBA.acc _ hj).2.2
    have ho' : keyOff P J c' = offK P J (co.nreg bE) (co.nreg bH) := by
      unfold keyOff; rw [h1, h2]
    refine ⟨?_, by rw [h1, h2]; exact hpw, ?_⟩
    · rw [ho']; rw [ekE, ekH] at hlt; exact hlt
    · rw [ho']
      have hp0 := hpw.2.1.1
      have hp1 := hpw.2.1.2.1
      have hpn := hpw.1
      refine Or.inl ⟨_, ⟨_, hmemF, _, _, hAt, rfl⟩, by positivity, ?_, rfl⟩
      have : ((co.nreg bE : ℕ) : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hpn
      linarith
  · -- the next stop
    have hi : c.nreg sP < c.nreg sC := by rw [← esP, ← esC]; exact hsp
    obtain ⟨eE, eH⟩ := hst hi
    have ho' : keyOff P J c' = stopOff P J c (c.nreg sP) := by
      unfold keyOff stopOff; rw [h1, h2, esP, eE, eH]
    refine ⟨?_, ?_, ?_⟩
    · rw [ho']
      by_contra h
      have := (L.ptrL _ hi).2 (not_lt.1 h)
      omega
    · rw [h1, h2, esP, eE, eH]
      obtain ⟨rs, ax, hlen, -, hrec, -, -, hpw, -⟩ := L.stops
      have hi' : c.nreg sP < rs.length := hlen ▸ hi
      obtain ⟨e0, e1, -⟩ := hrec _ hi'
      unfold stopE stopH
      rw [e0, e1, List.getD_eq_getElem _ _ hi']
      exact (hpw _ (List.getElem_mem hi')).1
    · rw [ho']
      obtain ⟨e, he, p, t, hA, hoff, -⟩ := stp_stop_cut L hi
      rw [hoff]
      refine Or.inl ⟨_, ⟨e, he, p, t, hA, rfl⟩, by have := hA.2.1; positivity, ?_, rfl⟩
      have : ((p : ℕ) : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hA.1
      linarith [hA.2.2.1]
  · -- the window end
    rw [ewX] at hwx
    obtain ⟨rs₁, -, -, -, -, -, -, -, hwin, -⟩ := hW
    obtain ⟨hpw, hlt, hcut⟩ := hwin hwx
    have ho' : keyOff P J c' = offK P J (cw.nreg wE) (cw.nreg wH) := by
      unfold keyOff; rw [h1, h2, ewE, ewH]
    refine ⟨by rw [ho']; exact hlt, by rw [h1, h2, ewE, ewH]; exact hpw, ?_⟩
    rw [ho']
    right
    rcases hcut with h | ⟨d, t, hv, ht0, ht1, ho, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨d, t, hv, ht0, ht1, hc, ho⟩

/-- **The measure decreases** and the log has room. -/
theorem stp_meas_step (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c')).ncard < (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard ∧
    c'.nreg lC + (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c')).ncard ≤ (keyS P J N₁ N₂).ncard + 1 ∧
    c.nreg lC + 1 ≤ logCap N₁ N₂ ∧ c'.nreg lC = c.nreg lC + 1 := by
  obtain ⟨hlt, -, hmem⟩ := stp_next_key E L hI hd
  obtain ⟨hfin, hcard⟩ := countTask P J N₁ N₂ E.hP E.hNF₁ E.hNF₂
  have hfin' : (keyS P J N₁ N₂).Finite := hfin
  have hsub : keyS P J N₁ N₂ ∩ Ioi (keyOff P J c') ⊂ keyS P J N₁ N₂ ∩ Ioi (keyOff P J c) :=
    ⟨fun x hx => ⟨hx.1, lt_trans hlt hx.2⟩, fun h => lt_irrefl _ (h ⟨hmem, hlt⟩).2⟩
  have hlt' := ncard_lt_ncard hsub (hfin'.subset inter_subset_left)
  have hpos : 0 < (keyS P J N₁ N₂ ∩ Ioi (keyOff P J c)).ncard :=
    (ncard_pos (hfin'.subset inter_subset_left)).2 ⟨_, hmem, hlt⟩
  have elC : co.nreg lC = c.nreg lC := stp_co_keep hI (k := 2431) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlC, -⟩ := hI.2.2.2.2.2.2.2 (stp_key_some hI hd)
  have hm := L.meas
  have hcard' : (keyS P J N₁ N₂).ncard ≤ 4 * N₂.nChords + 2 * N₁.nChords + 9 := hcard
  refine ⟨hlt', by omega, ?_, by omega⟩
  unfold logCap
  omega

/-- The stop and auxiliary arrays at the next key. -/
theorem stp_arrays_c' (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    c'.nreg sB = c.nreg sB ∧ c'.nreg aB = c.nreg aB ∧ c'.nreg sC = c.nreg sC ∧
    (∀ x, c.nreg sB ≤ x → x < c.nreg sB + 5 * c.nreg sC → c'.nmem x = c.nmem x) ∧
    (∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x) := by
  have hcap := (stp_meas_step E L hI hd).2.2.1
  have l1 := L.lay1
  have l2 := L.lay2
  have l3 := L.lay3
  have l4 := L.lay4
  have l5 := L.lay5
  refine ⟨stp_iter_keep hI (k := 2600) (by omega), stp_iter_keep hI (k := 2602) (by omega),
    stp_iter_keep hI (k := 2601) (by omega), fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
  · exact stp_c'_mem L hI hd x (by omega) (by omega) (Or.inr (by omega))
  · exact stp_c'_mem L hI hd x (by omega) (by omega) (Or.inr (by omega))

/-- **The stops at the next key.** -/
theorem stp_stops_c' (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    (∃ rs ax, StopData P J N₂ c' rs ax) ∧
    ∀ i, i < c.nreg sC → stopE c' i = stopE c i ∧ stopH c' i = stopH c i ∧
      stopOff P J c' i = stopOff P J c i := by
  obtain ⟨esB, eaB, esC, hmS, hmA⟩ := stp_arrays_c' E L hI hd
  obtain ⟨rs, ax, hlen, hax, hrec, hrecA, hok, hpw, hauxOK, hbd⟩ := L.stops
  have hEH : ∀ i, i < c.nreg sC → stopE c' i = stopE c i ∧ stopH c' i = stopH c i := by
    intro i hi
    unfold stopE stopH
    rw [esB, hmS _ (by omega) (by omega), hmS _ (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨rs, ax, by rw [esC]; exact hlen, hax, fun i hi => ?_, fun i hi => ?_, hok, hpw,
    hauxOK, hbd⟩, fun i hi => ⟨(hEH i hi).1, (hEH i hi).2, by
      unfold stopOff; rw [(hEH i hi).1, (hEH i hi).2]⟩⟩
  · have hi' : i < c.nreg sC := hlen ▸ hi
    obtain ⟨a0, a1, a2, a3, a4⟩ := hrec i hi
    rw [esB]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hmS _ (by omega) (by omega)]; exact a0
    · rw [hmS _ (by omega) (by omega)]; exact a1
    · rw [hmS _ (by omega) (by omega)]; exact a2
    · rw [hmS _ (by omega) (by omega)]; exact a3
    · rw [hmS _ (by omega) (by omega)]; exact a4
  · have hi' : i < c.nreg sC := by rw [← hlen, ← hax]; exact hi
    obtain ⟨a0, a1, a2, a3, a4⟩ := hrecA i hi
    rw [eaB]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hmA _ (by omega) (by omega)]; exact a0
    · rw [hmA _ (by omega) (by omega)]; exact a1
    · rw [hmA _ (by omega) (by omega)]; exact a2
    · rw [hmA _ (by omega) (by omega)]; exact a3
    · rw [hmA _ (by omega) (by omega)]; exact a4

/-- **The stop pointer at the next key.** -/
theorem stp_ptr_c' (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    c.nreg sP ≤ c'.nreg sP ∧ c'.nreg sP ≤ c'.nreg sC ∧
    (∀ i, i < c'.nreg sC → (i < c'.nreg sP ↔ stopOff P J c' i ≤ keyOff P J c')) ∧
    (∀ i, c.nreg sP ≤ i → i < c'.nreg sP → stopOff P J c i = keyOff P J c') := by
  obtain ⟨-, -, esC', -, -⟩ := stp_arrays_c' E L hI hd
  have hso := (stp_stops_c' E L hI hd).2
  have hlt := (stp_next_key E L hI hd).1
  obtain ⟨esP, esC, -, -, -, -⟩ := iter_stops L hI
  have hco := fun {i : ℕ} (hi : i < c.nreg sC) => stp_stopOff_co L hI hi
  obtain ⟨-, -, -, k1, k2, k3, k4, -⟩ := (hI.2.2.2.2.2.2.2 (stp_key_some hI hd)).2.2
  rw [esP] at k1 k3
  rw [esC] at k2 k4
  rw [esC']
  have k3' : ∀ i, c.nreg sP ≤ i → i < c'.nreg sP → stopOff P J c i = keyOff P J c' := by
    intro i h1 h2
    rw [← hco (by omega)]
    exact k3 i h1 h2
  refine ⟨k1, k2, fun i hi => ?_, k3'⟩
  rw [(hso i hi).2.2]
  constructor
  · intro h
    by_cases h' : i < c.nreg sP
    · have := (L.ptrL i hi).1 h'
      linarith
    · exact (k3' i (by omega) h).le
  · intro h
    by_contra h'
    have hlt' : c'.nreg sP < c.nreg sC := by omega
    have hle : stopOff P J c (c'.nreg sP) ≤ keyOff P J c' :=
      (L.sorted _ i (by omega) hi).trans h
    have hge : keyOff P J c' ≤ stopOff P J c (c'.nreg sP) := by
      rcases (show c'.nreg sP = c.nreg sP ∨ c.nreg sP < c'.nreg sP by omega) with h0 | h0
      · obtain ⟨-, -, -, hKs, -⟩ := (hI.2.2.2.2.2.2.2 (stp_key_some hI hd))
        have := hKs (by rw [esP, esC]; omega)
        rw [esP, ← h0] at this
        change keyOff P J c' ≤ stopOff P J co (c'.nreg sP) at this
        rwa [hco hlt'] at this
      · rw [← k3' (c'.nreg sP - 1) (by omega) (by omega)]
        exact L.sorted _ _ (by omega) hlt'
    have := k4 hlt'
    change stopOff P J co (c'.nreg sP) ≠ keyOff P J c' at this
    exact this (by rw [hco hlt']; linarith)

end

end SweepEv

end Chazelle.Core
