module

public import Chazelle.Core.DownPhaseDrvDCall3

/-!
# Down-phase restoration rounds (D8), part 10: the region loop

`regS sF` visits the regions `r < R` of the current normal form; a region with more than `4`
exit chords gets a sound chord and the buckets of its ends (`call_step`).

**`reg_exec`**: after the loop, the new chords are paired with exactly the high regions
(`Restore.NewOK`), their triples are at `B₀`, the buckets at `BK` (`BktOK`), in at most
`(Bf + 2) R + 2` steps within the relative frame.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam

@[expose] public section

/-- The degree word of region `r`. -/
theorem RegI.deg_word {E : REnv} {c₀ : Config} {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config}
    (hE : RGood E c₀) (hI : RegI E c₀ newL c) (hr : c.nreg 216030 < E.R) :
    c.nmem (c.nreg 216031) = Restore.degOf E.N (c.nreg 216030) := by
  have hrN : c.nreg 216030 < E.N.nRegions := by rwa [E.nRegions_N]
  have hareas := (Gran.nf_areas hE.hNW).2.2.1 _ hrN
  rw [hI.ptr, hI.low _ (by omega)]
  have := ((hE.hNW.nfAt).2.2.2.2.2.2.2.1 _ hrN).2.1
  unfold Restore.degOf
  rw [← this]
  congr 1
  ring

/-- The invariant survives a change of the scratch register `216032`. -/
theorem RegI.load {E : REnv} {c₀ : Config} {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config}
    (hI : RegI E c₀ newL c) (v : ℕ) (hv : v ≤ E.W) :
    RegI E c₀ newL { c with nreg := upd c.nreg 216032 v } := by
  have g : ∀ q, q ≠ 216032 → (upd c.nreg 216032 v) q = c.nreg q := fun q hq => by simp [hq]
  refine ⟨Machine.WordsBounded.upd_nreg hI.wb hv c.pc, ?_, ?_, ?_, hI.hgood, hI.hbk, ?_, ?_, ?_,
    hI.list, hI.low, fun q hq => ?_, ?_, ?_, ?_⟩ <;> simp only
  · rw [g _ (by norm_num)]; exact hI.r_le
  · rw [g _ (by norm_num), g _ (by norm_num)]; exact hI.ptr
  · rw [g _ (by norm_num)]; exact hI.hfst
  · rw [g _ (by norm_num)]; exact hI.cnt
  · rw [g _ (by norm_num)]; exact hI.dst
  · rw [g _ (by norm_num)]; exact hI.dstB
  · rw [g q (by unfold FixR at hq; omega)]; exact hI.regs q hq
  · rw [g _ (by norm_num)]; exact hI.rctx
  · rw [g _ (by unfold ALLOC; norm_num)]; exact hI.alloc
  · rw [g _ (by unfold ALLOC; norm_num), g _ (by norm_num)]; exact hI.room

set_option maxHeartbeats 8000000 in
/-- **One step of the region loop.** -/
theorem regBody_step {E : REnv} {c₀ : Config} (hE : RGood E c₀)
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 216030 < E.R) :
    ∃ c' k newL', Exec E.P E.W (regBody E.sF) c c' k ∧ RegI E c₀ newL' c' ∧
      Restore.RF DrvR.drvBands E.B₀ c c' k ∧ k ≤ E.Bf ∧ c'.nreg 216030 = c.nreg 216030 + 1 := by
  have hdw := hI.deg_word hE hr
  obtain ⟨r, hrd⟩ : ∃ r, c.nreg 216030 = r := ⟨_, rfl⟩
  rw [hrd] at hr hdw
  -- load the degree
  have e₁ := Exec.loadN (P := E.P) hI.wb 216032 216031
  set c₁ : Config := { c with nreg := upd c.nreg 216032 (c.nmem (c.nreg 216031)) } with hc₁
  have hI₁ : RegI E c₀ newL c₁ := hI.load _ (hI.wb.2 _)
  have r1 : c₁.nreg 216030 = r := by rw [hc₁]; simp [hrd]
  have d1 : c₁.nreg 216032 = Restore.degOf E.N r := by rw [hc₁]; simp [hdw]
  have c04 : c₁.nreg 216004 = 4 :=
    (hI₁.regs _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r04
  have RF₁ : Restore.RF DrvR.drvBands E.B₀ c c₁ 1 :=
    rf_of_frameB (inDrv_eq (q := 216032) (by norm_num) (by norm_num) (by unfold ALLOC; norm_num))
      (exec_frameB e₁ (by decide))
  -- the conditional call
  obtain ⟨c₂, k₂, newL', e₂, hk₂, RF₂, hI₂', h30, h31⟩ :
      ∃ (c₂ : Config) (k₂ : ℕ) (newL' : List (ℕ × (ℕ × ℕ × ℕ))),
      Exec E.P E.W (.ifLtN 216004 216032 (callS E.sF) .skip) c₁ c₂ k₂ ∧ k₂ + 8 ≤ E.Bf ∧
      Restore.RF DrvR.drvBands E.B₀ c₁ c₂ k₂ ∧
      (newL'.map Prod.fst = Restore.highList E.N 4 (r + 1) ∧
        (∀ p ∈ newL', Restore.FoundOK E.M E.Q E.N E.reg p.1 p.2) ∧
        BktOK E.M E.Q E.N newL' (fun q => c₂.nmem (E.BK + q)) ∧
        c₂.nreg 216020 = newL'.length ∧ c₂.nreg 216021 = E.B₀ + 3 * newL'.length ∧
        c₂.nreg 216022 = E.BK + 2 * newL'.length ∧
        ChordListAt c₂.nmem E.B₀ (newL'.map Prod.snd) ∧
        (∀ a, a < E.B₀ → c₂.nmem a = c₁.nmem a) ∧ (∀ q, FixR q → c₂.nreg q = c₁.nreg q) ∧
        c₂.nreg 230001 = c₁.nreg 230001 ∧ WordsBounded E.W c₂) ∧
      c₂.nreg 216030 = r ∧ c₂.nreg 216031 = c₁.nreg 216031 := by
    by_cases hhigh : 4 < Restore.degOf E.N r
    · obtain ⟨c₂, k₂, t, e₂, hk₂, RF₂, w₂, hfound, hbk, h20, h21, h22, hlist, hlow, hreg, h30,
        h31, hctx⟩ := call_step hE hI₁ (by rwa [r1]) (by rwa [r1])
      rw [r1] at hfound hbk hlist h30
      refine ⟨c₂, k₂ + 1, newL ++ [(r, t)],
        .ifLtN_true (by rwa [c04, d1]) e₂, by omega,
        RF₂.mono subset_rfl (by omega), ⟨?_, ?_, hbk, ?_, ?_, ?_, hlist, hlow, hreg, hctx, w₂⟩,
        h30, h31⟩
      · rw [List.map_append, hI.hfst, hrd, Restore.highList_succ, ite_eq_left hhigh]; rfl
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hI.hgood p hp
        · simp only [List.mem_singleton] at hp; subst hp; exact hfound
      · rw [h20, List.length_append, List.length_singleton]
      · rw [h21, List.length_append, List.length_singleton]
      · rw [h22, List.length_append, List.length_singleton]
    · refine ⟨c₁, 2, newL, .ifLtN_false (by rwa [c04, d1]) (.skip e₁.wb_right),
        by unfold REnv.Bf; omega, Restore.RF.refl _ _,
        ⟨by rw [hI.hfst, hrd, Restore.highList_succ, ite_eq_right hhigh, List.append_nil], hI.hgood,
          hI₁.hbk, hI₁.cnt, hI₁.dst, hI₁.dstB, hI₁.list, fun _ _ => rfl, fun _ _ => rfl, rfl,
          e₁.wb_right⟩, r1, rfl⟩
  obtain ⟨hfst₂, hgood₂, hbk₂, h20, h21, h22, hlist₂, hlow₂, hreg₂, hctx₂, w₂⟩ := hI₂'
  -- the tail
  have c06 : c₂.nreg 216006 = 5 :=
    ((hreg₂ _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans
      (hI₁.regs _ (Or.inl ⟨by norm_num, by norm_num⟩))).trans hE.r06
  have c02 : c₂.nreg 216002 = 1 :=
    ((hreg₂ _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans
      (hI₁.regs _ (Or.inl ⟨by norm_num, by norm_num⟩))).trans hE.r02
  have hp1 : c₂.nreg 216031 = c₀.nmem (E.H + 5) + 2 + 5 * r := by rw [h31, hI₁.ptr, r1]
  have hRW : E.R + 1 ≤ E.W := by
    have := hE.room
    have : E.R ≤ (E.Bf + 2) * E.R := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hareas := (Gran.nf_areas hE.hNW).2.2.1 r (by rwa [E.nRegions_N])
  have hB₀W : E.B₀ + 5 ≤ E.W := by
    have h1 := hE.alloc; have h2 := hE.wb.1 ALLOC
    have h3 : E.BK = E.B₀ + 3 * E.R := rfl
    omega
  obtain ⟨c₃, k₃, e₃, hk₃, t31, t30, R₃⟩ : ∃ c₃ k₃, Exec E.P E.W
      (block [.addN 216031 216031 216006, .addN 216030 216030 216002]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 216031 = c₂.nreg 216031 + 5 ∧ c₃.nreg 216030 = r + 1 ∧
      c₃ = { c₂ with nreg := upd (upd c₂.nreg 216031 (c₂.nreg 216031 + 5)) 216030 (r + 1) } := by
    exec_block
    · rw [c06, hp1]; omega
    · config_simp; rw [h30, c02]; omega
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · config_simp; rw [c06]
      · config_simp; rw [h30, c02]
      · rw [c06, h30, c02]
  have g3 : ∀ q, q ≠ 216031 → q ≠ 216030 → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
    rw [R₃]; simp [h1, h2]
  have m3 : c₃.nmem = c₂.nmem := by rw [R₃]
  have RF₃ : Restore.RF DrvR.drvBands E.B₀ c₂ c₃ k₃ :=
    rf_of_frameB (B := fun r => decide (r = 216031) || decide (r = 216030))
      (fun q hq => by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hq
        exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩)
      ⟨fun q hq => by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hq
        exact g3 q hq.1 hq.2, fun q _ => by rw [R₃], by rw [R₃], by rw [R₃], by rw [R₃]⟩
  have RFall := RF₁.trans (RF₂.trans RF₃)
  refine ⟨c₃, 1 + (k₂ + k₃), newL', .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, ?_, ?_, ?_, hgood₂,
    by rwa [m3], by rw [g3 _ (by norm_num) (by norm_num), h20],
    by rw [g3 _ (by norm_num) (by norm_num), h21], by rw [g3 _ (by norm_num) (by norm_num), h22],
    by rwa [m3], fun a ha => by rw [m3, hlow₂ a ha]; exact hI.low a ha,
    fun q hq => ?_, by rw [g3 _ (by norm_num) (by norm_num), hctx₂]; exact hI₁.rctx,
    le_trans hI.alloc RFall.2.2.2.2.2.1, ?_⟩, RFall, by omega, by rw [t30, hrd]⟩
  · rw [t30]; omega
  · rw [t31, t30, hp1]; ring
  · rwa [t30]
  · unfold FixR at hq
    rw [g3 q (by omega) (by omega), hreg₂ q hq, hI₁.regs q hq]
  · have h1 := hI.room
    have h2 := RFall.2.2.2.2.2.2
    rw [t30]
    rw [hrd] at h1
    have h3 : (E.Bf + 2) * (E.R - r) = (E.Bf + 2) * (E.R - (r + 1)) + (E.Bf + 2) := by
      rw [show E.R - r = (E.R - (r + 1)) + 1 by omega, Nat.mul_add, Nat.mul_one]
    omega

/-- The invariant at the start of the loop. -/
theorem RGood.regI {E : REnv} {c₀ : Config} (hE : RGood E c₀) : RegI E c₀ [] c₀ :=
  ⟨hE.wb, by rw [hE.r30]; omega, by rw [hE.r30, hE.r31], by rw [hE.r30]; rfl,
    fun p hp => by simp at hp, ⟨fun q hq => by simp at hq, fun q hq => by simp at hq⟩,
    by rw [hE.r20]; rfl, by rw [hE.r21]; simp, by rw [hE.r22]; simp,
    fun i hi => by simp at hi, fun _ _ => rfl, fun _ _ => rfl, hE.rctx, le_rfl,
    by rw [hE.r30]; simp⟩

/-- **The region loop.** -/
theorem reg_exec {E : REnv} {c₀ : Config} (hE : RGood E c₀) :
    ∃ c' k newL, Exec E.P E.W (regS E.sF) c₀ c' k ∧ RegI E c₀ newL c' ∧
      c'.nreg 216030 = E.R ∧ Restore.RF DrvR.drvBands E.B₀ c₀ c' k ∧
      k ≤ (E.Bf + 2) * E.R + 2 := by
  obtain ⟨c', k, e, ⟨newL, I'⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := E.P) (W := E.W)
    (a := 216030) (b := 216013) (body := regBody E.sF) (B := DrvR.drvBands) (A₀ := E.B₀)
    (fun c => ∃ newL, RegI E c₀ newL c) (fun c => E.R - c.nreg 216030) E.Bf
    (fun c ⟨_, h⟩ => h.wb)
    (fun c ⟨newL, I⟩ ht => by
      have t : c.nreg 216030 < E.R := by
        rwa [I.regs 216013 (Or.inl ⟨by norm_num, by norm_num⟩), hE.r13] at ht
      obtain ⟨c', k, newL', e, I', RF', hk, h30⟩ := regBody_step hE I t
      exact ⟨c', k, e, ⟨newL', I'⟩, RF', hk, by omega⟩) ⟨[], hE.regI⟩
  have hR' : c'.nreg 216030 = E.R := by
    rw [I'.regs 216013 (Or.inl ⟨by norm_num, by norm_num⟩), hE.r13] at hx
    have := I'.r_le; omega
  refine ⟨c', k, newL, e, I', hR', RFl, ?_⟩
  rw [hE.r30] at hk
  simpa using hk

end

end DrvD

end Chazelle.Core
