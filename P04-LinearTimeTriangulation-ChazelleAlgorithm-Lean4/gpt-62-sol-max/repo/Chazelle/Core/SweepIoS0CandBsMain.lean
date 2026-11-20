module

public import Chazelle.Core.SweepIoS0CandBsProg

/-!
# The sweep RAM (WP-D), answers: the binary search in the event log, the proof

**`lsearchSpec : LSearchSpec`** with the program `lsearchS` (`SweepIoS0CandBsProg`), cost
`11106 (TLR + 1)`.  Invariant of the loop (`LInv`): the answer `i ≤ E`, every record `< i`
satisfies the predicate, no record `j < E` with `i + 2^k ≤ j + 1` does; each step halves the
power (`lsBody_irs`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

/-- The predicate of the search, read off the configuration `c` at the start. -/
def lsP (P : Polygon) (J : Merge.Junction) (c : Config) (j : ℕ) : Prop :=
  lsPr P J c.nmem (c.nreg 240300) (c.nreg 240040) ⟨c.nreg 244020, c.nreg 244021⟩ j

/-- **The invariant of the search loop.** -/
structure LInv (P : Polygon) (J : Merge.Junction) (c d : Config) : Prop where
  fr : ∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → d.nreg r = c.nreg r
  hA : c.nreg ALLOC ≤ d.nreg ALLOC
  hm : ∀ a, a < c.nreg ALLOC → d.nmem a = c.nmem a
  hk : d.nreg 244001 ≤ c.nreg 240601
  hi : d.nreg 244000 ≤ c.nreg 240301
  hlo : ∀ j, j < d.nreg 244000 → lsP P J c j
  hhi : ∀ j, d.nreg 244000 + 2 ^ d.nreg 244001 ≤ j + 1 → j < c.nreg 240301 → ¬ lsP P J c j

theorem lb_false_of_lset {r : ℕ} (h : ¬ LSet r) : LB r = false := by
  unfold LSet sw at h
  simp only [LB, decide_eq_false_iff_not]; omega

theorem lb_false_of_scr {r : ℕ} (h : ¬ IScr r) : LB r = false := by
  unfold IScr at h
  simp only [LB, decide_eq_false_iff_not]; omega

theorem fix_keep {P : Polygon} {J : Merge.Junction} {c d : Config} (h : LInv P J c d) {r : ℕ}
    (h1 : 240000 ≤ r) (h2 : r < 244000 ∨ (244019 < r ∧ r < 250000)) : d.nreg r = c.nreg r :=
  h.fr r (by rw [band_sw h1 (by omega)]; decide) (by unfold LSet sw; omega)
    (by unfold ALLOC; omega)

section

variable {P : Polygon} {W : ℕ} {J : Merge.Junction} {c₀ c : Config}

/-- A straight-line block of the search as a run step. -/
theorem irs_blk {s : Stmt} {d d' : Config} {k : ℕ} (hI : IInv W c₀ d) (ex : Exec P W s d d' k)
    (f : ∀ r, LB r = false → d'.nreg r = d.nreg r) (rr : d'.rreg = d.rreg) (m : d'.nmem = d.nmem)
    (rm : d'.rmem = d.rmem) (o : d'.output = d.output) : IRS P W c₀ s d k (fun x => x = d') :=
  IRS.ofExec hI ex le_rfl (fun r hr _ => f r (lb_false_of_scr hr)) rr (fun a _ => by rw [m]) rm o
    (by rw [f ALLOC (by decide)]) (by rw [f ALLOC (by decide)]; omega) rfl

set_option maxHeartbeats 16000000 in
/-- **One step of the search.** -/
theorem lsBody_irs (hctx : ChainCtx P W c 240002 J.whole)
    (htab : ∀ j, j < c.nreg 240601 → c.nmem (c.nreg 240600 + j) = 2 ^ j)
    (hTB : c.nreg 240600 + c.nreg 240601 ≤ c.nreg ALLOC)
    (hAL : c.nreg 240300 + 7 * c.nreg 240301 ≤ c.nreg ALLOC)
    (hG : c.nreg 240040 < (chainModel J.whole).W.n)
    (hrec : ∀ j, j < c.nreg 240301 → SweepEv.PosW P J (c.nmem (c.nreg 240300 + 7 * j))
      (c.nmem (c.nreg 240300 + 7 * j + 1)))
    (hx : SweepEv.PosW P J (c.nreg 244020) (c.nreg 244021))
    (hdc : ∀ i j, i ≤ j → j < c.nreg 240301 → lsP P J c j → lsP P J c i)
    (k0 : c.nreg 240610 = 0) (k1 : c.nreg 240611 = 1) {d : Config} (hI : IInv W c₀ d)
    (hL : LInv P J c d) (hpos : d.nreg 240610 < d.nreg 244001)
    (hroom : d.nreg ALLOC + 11100 ≤ W) :
    IRS P W c₀ lsBody d 11100 (fun d' => LInv P J c d' ∧ d'.nreg 244001 < d.nreg 244001) := by
  have d0 : d.nreg 240610 = 0 := (fix_keep hL (by norm_num) (by norm_num)).trans k0
  have dK1 : d.nreg 240611 = 1 := (fix_keep hL (by norm_num) (by norm_num)).trans k1
  have dTB : d.nreg 240600 = c.nreg 240600 := fix_keep hL (by norm_num) (by norm_num)
  have dE : d.nreg 240301 = c.nreg 240301 := fix_keep hL (by norm_num) (by norm_num)
  have dAL : d.nreg 240300 = c.nreg 240300 := fix_keep hL (by norm_num) (by norm_num)
  have dD : d.nreg 240002 = c.nreg 240002 := fix_keep hL (by norm_num) (by norm_num)
  have dG : d.nreg 240040 = c.nreg 240040 := fix_keep hL (by norm_num) (by norm_num)
  have dxE : d.nreg 244020 = c.nreg 244020 := fix_keep hL (by norm_num) (by norm_num)
  have dxH : d.nreg 244021 = c.nreg 244021 := fix_keep hL (by norm_num) (by norm_num)
  have hKK : 0 < d.nreg 244001 := by omega
  have hWA : d.nreg ALLOC ≤ W := hI.hw.1 ALLOC
  have hAd := hL.hA
  have hkTL := hL.hk
  -- 1. `k := k - 1`, the power, the room
  obtain ⟨d1, k₁, e1, hk1, a01, a03, a16, a00, f1, rr1, m1, rm1, o1⟩ := lsB1_exec (P := P) d hI.hw
    (I := d.nreg 244000) (KK := d.nreg 244001) rfl rfl dTB dE dK1 (by omega)
  have hpw : d.nmem (c.nreg 240600 + (d.nreg 244001 - 1)) = 2 ^ (d.nreg 244001 - 1) := by
    rw [hL.hm _ (by omega)]; exact htab _ (by omega)
  rw [hpw] at a03
  have h2 : 2 ^ d.nreg 244001 = 2 * 2 ^ (d.nreg 244001 - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hb1 := irs_blk hI e1 f1 rr1 m1 rm1 o1
  -- the frame facts of the step, from `d1` on
  have F1 : ∀ r, ¬ LSet r → d1.nreg r = d.nreg r := fun r hr => f1 r (lb_false_of_lset hr)
  refine (IRS.seq hb1 (K₂ := 11021 + 2) (fun d1' hI1 _ _ h1 => ?_)).mono (by omega)
    (fun _ h => h)
  subst d1'
  have A1 : d1.nreg ALLOC = d.nreg ALLOC := f1 ALLOC (by decide)
  have e101 : d1.nreg 244001 = d.nreg 244001 - 1 := a01
  by_cases hlt : d1.nreg 244016 < d1.nreg 244003
  · -- no room: no record `j < E` above
    refine IRS.ifT hlt (IRS.skip hI1 ⟨⟨fun r hr1 hr2 hr3 => (F1 r hr2).trans (hL.fr r hr1 hr2 hr3),
      by omega, fun a ha => by rw [m1]; exact hL.hm a ha, by omega, by rw [a00]; exact hL.hi,
      by rw [a00]; exact hL.hlo, fun j hj hjE => ?_⟩, by omega⟩)
    exfalso
    rw [a16, a03] at hlt
    rw [a00, a01] at hj
    have := hL.hi
    omega
  refine IRS.ifF hlt ?_
  -- 2. the test
  rw [a16, a03] at hlt
  have hge := hlt
  have hle : d.nreg 244000 + 2 ^ (d.nreg 244001 - 1) ≤ c.nreg 240301 := by
    have := hL.hi; omega
  have hp1 : 1 ≤ 2 ^ (d.nreg 244001 - 1) := Nat.one_le_two_pow
  obtain ⟨d2, k₂, e2, hk2, b04, b12, b13, b00, b01, f2, rr2, m2, rm2, o2⟩ := lsB2_exec (P := P) d1
    hI1.hw (I := d.nreg 244000) (Pv := 2 ^ (d.nreg 244001 - 1)) (E := c.nreg 240301)
    (AL := c.nreg 240300) a00 a03 (by rw [F1 _ (by unfold LSet sw; omega), dAL])
    (by rw [F1 _ (by unfold LSet sw; omega), dK1]) hle (by omega) (by omega)
  have hb2 := irs_blk hI1 e2 f2 rr2 m2 rm2 o2
  have F2 : ∀ r, ¬ LSet r → d2.nreg r = d.nreg r := fun r hr =>
    (f2 r (lb_false_of_lset hr)).trans (F1 r hr)
  refine (IRS.seq hb2 (K₂ := 11008 + (1 + 2)) (fun d2' hI2 _ _ h2' => ?_)).mono (by omega)
    (fun _ h => h)
  subst d2'
  have A2 : d2.nreg ALLOC = d.nreg ALLOC := by rw [f2 ALLOC (by decide), A1]
  -- the record and its key
  set j0 := d.nreg 244000 + 2 ^ (d.nreg 244001 - 1) - 1 with hj0
  have hj0E : j0 < c.nreg 240301 := by omega
  have hmem : ∀ a, a < c.nreg ALLOC → d1.nmem a = c.nmem a := fun a ha => by
    rw [m1]; exact hL.hm a ha
  rw [hmem _ (by omega)] at b12
  rw [hmem _ (by omega)] at b13
  obtain ⟨hpe, hpp, hp6⟩ := hrec j0 hj0E
  obtain ⟨hxe, hxp, hx6⟩ := hx
  have g12 : d2.nreg 244012 = c.nmem (c.nreg 240300 + 7 * j0) := b12
  have g13 : d2.nreg 244013 = c.nmem (c.nreg 240300 + 7 * j0 + 1) := b13
  have g20 : d2.nreg 244020 = c.nreg 244020 := by rw [F2 _ (by unfold LSet sw; omega), dxE]
  have g21 : d2.nreg 244021 = c.nreg 244021 := by rw [F2 _ (by unfold LSet sw; omega), dxH]
  have g40 : d2.nreg 240040 = c.nreg 240040 := by rw [F2 _ (by unfold LSet sw; omega), dG]
  have g02 : d2.nreg 240002 = c.nreg 240002 := by rw [F2 _ (by unfold LSet sw; omega), dD]
  have hmem2 : ∀ a, a < c.nreg ALLOC → d2.nmem a = c.nmem a := fun a ha => by
    rw [m2]; exact hmem a ha
  have hctx2 : ChainCtx P W d2 240002 J.whole :=
    hctx.transport g02 hmem2 (by rw [A2]; exact hAd)
  have hcall := callOff_irs (P := P) (c₀ := c₀) (dsc := 240002) (ex := 244012) (hx := 244013)
    (ey := 244020) (hy := 244021) (g := 240040) (o := 244014) hI2 hctx2 (by norm_num)
    (by norm_num) (by rw [g12]; exact hpe) (by rw [g20]; exact hxe) (by rw [g40]; exact hG)
    (by rw [g12, g13]; exact hpp) (by rw [g20, g21]; exact hxp) (by rw [g12, g13]; exact hp6)
    (by rw [g20, g21]; exact hx6) (by omega)
  refine IRS.seq hcall (fun d3 hI3 _ _ h3 => ?_)
  obtain ⟨bit, -, fr3, A3, m3⟩ := h3
  have F3 : ∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → d3.nreg r = d.nreg r :=
    fun r hr1 hr2 hr3 => (fr3 r hr1 (by unfold LSet sw at hr2; omega)
      (by unfold LSet sw at hr2; omega) hr3).trans (F2 r hr2)
  have hbit : d3.nreg 244014 = 1 ↔ lsP P J c j0 := by
    rw [bit.2, g12, g13, g20, g21, g40]; rfl
  have hb1' := bit.1
  have e10 : d3.nreg 240610 = 0 := by
    rw [F3 _ (by decide) (by unfold LSet sw; omega) (by unfold ALLOC; omega), d0]
  have e01 : d3.nreg 244001 = d.nreg 244001 - 1 := by
    rw [fr3 _ (by decide) (by norm_num) (by norm_num) (by unfold ALLOC; omega),
      b01, a01]
  have e00 : d3.nreg 244000 = d.nreg 244000 := by
    rw [fr3 _ (by decide) (by norm_num) (by norm_num) (by unfold ALLOC; omega), b00]
  have e04 : d3.nreg 244004 = d.nreg 244000 + 2 ^ (d.nreg 244001 - 1) := by
    rw [fr3 _ (by decide) (by norm_num) (by norm_num) (by unfold ALLOC; omega), b04]
  have hmem3 : ∀ a, a < c.nreg ALLOC → d3.nmem a = c.nmem a := fun a ha => by
    rw [m3 a (by omega)]; exact hmem2 a ha
  have hA3 : c.nreg ALLOC ≤ d3.nreg ALLOC := by omega
  by_cases hlt3 : d3.nreg 240610 < d3.nreg 244014
  · -- accept
    refine IRS.ifT hlt3 ?_
    have hlt := hlt3
    rw [e10] at hlt
    have hpr : lsP P J c j0 := hbit.1 (by omega)
    obtain ⟨d4, k₄, e4, hk4, c00, c01, f4, rr4, m4, rm4, o4⟩ := lsB3_exec (P := P) d3 hI3.hw
    refine (irs_blk hI3 e4 f4 rr4 m4 rm4 o4).mono (by omega) (fun x hx' => ?_)
    subst x
    have F4 : ∀ r, ¬ LSet r → d4.nreg r = d3.nreg r := fun r hr => f4 r (lb_false_of_lset hr)
    have e41 : d4.nreg 244001 = d.nreg 244001 - 1 := by
      rw [c01, e01]
    have e40 : d4.nreg 244000 = d.nreg 244000 + 2 ^ (d.nreg 244001 - 1) := by rw [c00, e04]
    refine ⟨⟨fun r hr1 hr2 hr3 => ((F4 r hr2).trans (F3 r hr1 hr2 hr3)).trans (hL.fr r hr1 hr2 hr3),
      by rw [f4 ALLOC (by decide)]; exact hA3, fun a ha => by rw [m4]; exact hmem3 a ha,
      by omega, by omega, fun j hj => ?_, fun j hj hjE => ?_⟩, by omega⟩
    · rw [e40] at hj
      by_cases hji : j < d.nreg 244000
      · exact hL.hlo j hji
      · exact hdc j j0 (by omega) hj0E hpr
    · rw [e40, e41] at hj
      exact hL.hhi j (by omega) hjE
  · -- reject
    refine IRS.ifF hlt3 ?_
    have hge' := hlt3
    rw [e10] at hge'
    have hnpr : ¬ lsP P J c j0 := fun h => by have := hbit.2 h; omega
    refine IRS.skip hI3 ⟨⟨fun r hr1 hr2 hr3 => (F3 r hr1 hr2 hr3).trans (hL.fr r hr1 hr2 hr3),
      hA3, hmem3, by omega, by omega, by rw [e00]; exact hL.hlo, fun j hj hjE hpr => ?_⟩, by omega⟩
    rw [e00, e01] at hj
    exact hnpr (hdc j0 j (by omega) hjE hpr)

end

set_option maxHeartbeats 16000000 in
/-- **The binary search in the log meets its contract.** -/
theorem lsearchSpec : LSearchSpec := by
  refine ⟨lsearchS, 11106, ?_⟩
  intro P W J c₀ c hI hC hctx htab hTB hET hAL hG hrec hx hdc hroom
  obtain ⟨k0, k1, -⟩ := hC.fix hI
  replace k0 : c.nreg 240610 = 0 := k0
  replace k1 : c.nreg 240611 = 1 := k1
  replace hctx : ChainCtx P W c 240002 J.whole := hctx
  replace htab : ∀ j, j < c.nreg 240601 → c.nmem (c.nreg 240600 + j) = 2 ^ j := htab
  replace hTB : c.nreg 240600 + c.nreg 240601 ≤ c.nreg ALLOC := hTB
  replace hET : c.nreg 240301 < 2 ^ c.nreg 240601 := hET
  replace hAL : c.nreg 240300 + 7 * c.nreg 240301 ≤ c.nreg ALLOC := hAL
  replace hG : c.nreg 240040 < (chainModel J.whole).W.n := hG
  replace hrec : ∀ j, j < c.nreg 240301 → SweepEv.PosW P J (c.nmem (c.nreg 240300 + 7 * j))
      (c.nmem (c.nreg 240300 + 7 * j + 1)) := hrec
  replace hx : SweepEv.PosW P J (c.nreg 244020) (c.nreg 244021) := hx
  replace hdc : ∀ i j, i ≤ j → j < c.nreg 240301 → lsP P J c j → lsP P J c i := hdc
  replace hroom : c.nreg ALLOC + 11106 * (c.nreg 240601 + 1) ≤ W := hroom
  show IRS P W c₀ lsearchS c (11106 * (c.nreg 240601 + 1)) (fun c' =>
    c'.nreg 244000 ≤ c.nreg 240301 ∧ (∀ j, j < c'.nreg 244000 → lsP P J c j) ∧
      (∀ j, c'.nreg 244000 ≤ j → j < c.nreg 240301 → ¬ lsP P J c j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a))
  obtain ⟨c1, k₁, e1, hk1, i00, i01, f1, rr1, m1, rm1, o1⟩ := lsInit_exec (P := P) c hI.hw
  have hb := irs_blk hI e1 f1 rr1 m1 rm1 o1
  refine (IRS.seq hb (K₂ := (11100 + 2) * c.nreg 240601 + 2) (fun c1' hI1 _ _ h1 => ?_)).mono
    (by omega) (fun _ h => h)
  subst c1'
  have F1 : ∀ r, ¬ LSet r → c1.nreg r = c.nreg r := fun r hr => f1 r (lb_false_of_lset hr)
  have A1 : c1.nreg ALLOC = c.nreg ALLOC := f1 ALLOC (by decide)
  have hL1 : LInv P J c c1 := ⟨fun r _ hr2 _ => F1 r hr2, by omega, fun a _ => by rw [m1],
    by omega, by omega, fun j hj => by omega, fun j hj hjE => by
      rw [i00, i01] at hj; omega⟩
  have hw := IRS.while (P := P) (c₀ := c₀) (a := 240610) (b := 244001) (body := lsBody)
    (LInv P J c) (fun d => d.nreg 244001) 11100
    (fun d hd hlt => by have := fix_keep hd (r := 240610) (by norm_num) (by norm_num); omega)
    (fun d hId hd hlt hr => lsBody_irs hctx htab hTB hAL hG hrec hx hdc k0 k1 hId hd hlt hr)
    hI1 hL1 (by rw [i01, A1]; omega)
  rw [i01] at hw
  refine hw.mono le_rfl (fun d ⟨hd, hn⟩ => ?_)
  have h10 : d.nreg 240610 = 0 := (fix_keep hd (by norm_num) (by norm_num)).trans k0
  have hk0 : d.nreg 244001 = 0 := by omega
  refine ⟨hd.hi, hd.hlo, fun j hj hjE => hd.hhi j (by rw [hk0]; simp; omega) hjE, hd.fr, hd.hA,
    hd.hm⟩

end

end S0C

end SweepIo

end Chazelle.Core
