module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvDCall2
public import Chazelle.Core.RestoreTestMath

/-!
# Down-phase restoration rounds (D8), part 9: one call of the splitting step, the proof

**`call_step`**: on a region `r` with more than `4` exit chords, `callS sF` finds a sound chord
`t` (`Restore.FoundOK`), appends its triple at `B₀ + 3 i` and the buckets of its two ends at
`BK + 2 i`, `BK + 2 i + 1` (`i` the number of chords found so far), within the relative frame
`Restore.RF drvBands B₀` and `Bf - 10` steps.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam

@[expose] public section

/-- The registers written by the appending part of a call. -/
def Bapp (r : ℕ) : Bool := BappT r || Bscan r || decide (r = 216022)

theorem inDrv_app : InDrv Bapp := by
  intro r hr
  simp only [Bapp, Bool.or_eq_true] at hr
  rcases hr with (h | h) | h
  · exact inDrv_appT r h
  · exact inDrv_scan r h
  · exact inDrv_eq (q := 216022) (by norm_num) (by norm_num) (by omega_nf) r h

section
variable (r : ℕ)
theorem bapp_of_appT (h : BappT r = true) : Bapp r = true := by
  simp [Bapp, h]

theorem bapp_of_scan (h : Bscan r = true) : Bapp r = true := by
  simp [Bapp, h]

theorem bapp_of_22 (h : decide (r = 216022) = true) : Bapp r = true := by
  aesop

theorem bapp_of_40 (h : decide (r = 216040) = true) : Bapp r = true := by
  aesop


end

/-- The degree word of a region of `buildNF` bounds the number of chords. -/
theorem degOf_le {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {r : ℕ}
    (hr : r < L.length + 1) : Restore.degOf (BuildNF.buildNF M Q L E) r ≤ L.length := by
  unfold Restore.degOf
  rw [region_buildNF hr]
  exact (List.length_filter_le _ _).trans (by simp)

set_option maxHeartbeats 16000000 in
/-- **One call of the splitting step.** -/
theorem call_step {E : REnv} {c₀ : Config} (hE : RGood E c₀)
    {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 216030 < E.R) (hhigh : 4 < Restore.degOf E.N (c.nreg 216030)) :
    ∃ c' k t, Exec E.P E.W (callS E.sF) c c' k ∧ k + 10 ≤ E.Bf ∧
      Restore.RF DrvR.drvBands E.B₀ c c' k ∧ WordsBounded E.W c' ∧
      Restore.FoundOK E.M E.Q E.N E.reg (c.nreg 216030) t ∧
      BktOK E.M E.Q E.N (newL ++ [(c.nreg 216030, t)]) (fun q => c'.nmem (E.BK + q)) ∧
      c'.nreg 216020 = newL.length + 1 ∧ c'.nreg 216021 = E.B₀ + 3 * (newL.length + 1) ∧
      c'.nreg 216022 = E.BK + 2 * (newL.length + 1) ∧
      ChordListAt c'.nmem E.B₀ ((newL ++ [(c.nreg 216030, t)]).map Prod.snd) ∧
      (∀ a, a < E.B₀ → c'.nmem a = c.nmem a) ∧
      (∀ q, FixR q → c'.nreg q = c.nreg q) ∧
      c'.nreg 216030 = c.nreg 216030 ∧ c'.nreg 216031 = c.nreg 216031 ∧
      c'.nreg 230001 = c.nreg 230001 := by
  set r := c.nreg 216030 with hrd
  set i := newL.length with hid
  have hGM := E.hGM hE.hG
  have hNF := hE.hNF
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  have hW3 : E.P.n + 3 ≤ E.W := by have := hE.hWh; grind [hostWords]
  have hRN : E.N.nRegions = E.R := E.nRegions_N
  have hrN : r < E.N.nRegions := by omega
  -- the registers of `c`
  have RR : ∀ q, FixR q → c.nreg q = c₀.nreg q := hI.regs
  have c001 : c.nreg 210001 = E.MD := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r001
  have c00 : c.nreg 216000 = E.d0 := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r00
  have c01 : c.nreg 216001 = E.γ := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r01
  have c02 : c.nreg 216002 = 1 := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r02
  have c03 : c.nreg 216003 = 0 := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r03
  have c04 : c.nreg 216004 = 4 := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r04
  have c05 : c.nreg 216005 = 2 := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r05
  have c12 : c.nreg 216012 = E.H := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r12
  have c14 : c.nreg 216014 = c₀.nmem (E.H + 4) :=
    (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r14
  have c16 : c.nreg 216016 = c₀.nmem (E.H + 7) :=
    (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r16
  have c17 : c.nreg 216017 = E.A := (RR _ (Or.inl ⟨by norm_num, by norm_num⟩)).trans hE.r17
  -- sizes and bounds
  have hir : i ≤ r := by
    have := congrArg List.length hI.hfst
    rw [List.length_map] at this
    rw [hid, this]; exact Restore.highList_length_le _ _ _
  have hKpos : 0 < E.L.length := by
    have h' : Restore.degOf E.N r ≤ E.L.length :=
      degOf_le (M := E.M) (Q := E.Q) (E := E.E) (r := r) (by simp_all [REnv.R] )
    omega
  have hBK : E.BK = E.B₀ + 3 * E.R := rfl
  have hA0B : E.A₀ ≤ E.B₀ := hE.hA₀
  have hc0A : E.BK + 2 * E.R ≤ c₀.nreg ALLOC := hE.alloc
  have hcA : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.alloc
  
  have hroom : c.nreg ALLOC + E.Bf + 2 ≤ E.W := by
    have h1 := hI.room
    have h2 := hE.room
    have : E.Bf + 2 ≤ (E.Bf + 2) * (E.R - c.nreg 216030) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hBKi : E.BK + 2 * i + 2 ≤ c.nreg ALLOC := by omega
  have hB3i : E.B₀ + 3 * i + 3 ≤ E.BK := by omega
  -- the memory
  have hNW₀ := hE.hNW
  have hareas := Gran.nf_areas hNW₀
  have hNAt₀ := hNW₀.nfAt
  have agree : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a := fun a ha =>
    (hI.low a (by omega)).trans (hE.hlow a ha)
  -- 1. the arguments
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, a3, a4, a5, a6, f₁⟩ := argS_exec (P := E.P) c hI.wb
  have w₁ := e₁.wb_right
  have g₁ : ∀ q, ¬ (81000 ≤ q ∧ q ≤ 81006) → c₁.nreg q = c.nreg q := fun q hq =>
    f₁.1 q (by grind)
  have m₁ : c₁.nmem = c.nmem := f₁.2.2.1
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (by omega_nf)
  have agree₁ : ∀ a, a < E.A₀ → c₁.nmem a = E.m₀ a := by grind
  obtain ⟨hMD₁, hwf₁⟩ := Gran.desc_agree' hE.hwf hE.hMD agree₁
  have hNW₁ : NFWithin c₁.nmem E.H (c₁.nreg ALLOC) E.N := by
    rw [m₁, A₁]; exact (hNW₀.transport hI.low).mono (by omega)
  have hctx : c₁.nreg 81004 = E.ctx := by rw [a4, hI.rctx]
  have hMD' : c₁.nreg 81000 = E.MD := by omega
  have hH' : c₁.nreg 81001 = E.H := by rw [a1, c12]
  have hγ' : c₁.nreg 81003 = E.γ := by rw [a3, c01]
  have hd' : c₁.nreg 81005 = E.d0 := by rw [a5, c00]
  have h4' : c₁.nreg 81006 = 4 := by rw [a6, c04]
  have hone : c₁.nmem E.MD = 1 := desc_one hMD₁
  -- 2. the splitting step
  have hroomF : c₁.nreg ALLOC + E.κf (c₁.nreg 81005) * E.F (c₁.nreg 81003) *
      E.G (c₁.nreg 81003) * (E.Hc (c₁.nreg 81003) + Nat.clog 2 (c₁.nreg 81003) + 1) ≤ E.W := by
    rw [hd', hγ', A₁]
    have : Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ ≤ E.Bf := by omega_nf
    unfold Restore.costF at this
    omega
  have hXh : E.X.holds E.P c₁.nmem E.ctx (c₁.nreg ALLOC) :=
    E.X.mono _ _ _ _ _ (by omega)
      (E.X.local_ _ _ _ _ _ (fun a ha => (agree₁ a ha).symm) hE.hX)
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨-, -, Ppost⟩, F₂⟩ := hE.hF E.P E.W c₁ w₁
    ⟨hE.hG, hE.hWh, by grind, by rw [hγ', hctx]; exact hE.hcap _ agree₁,
      by rw [hMD']; exact hwf₁.mono (by omega),
      fun h0 => by grind,
      fun h0 => by grind,
      E.M, E.N, by grind, hGM, rfl, by grind, hNF,
      by rw [hd']; exact hE.hdeg, by rw [hγ']; exact hE.hsg, by omega⟩ hroomF
  beta_reduce at hk₂
  rw [hd', hγ'] at hk₂
  have w₂ := e₂.wb_right
  obtain ⟨hsnd, hcpl⟩ := Ppost E.M E.N E.reg (by rw [hMD']; exact hMD₁)
    (by rw [hH']; exact hNW₁.nfAt) hNF hE.hregs
  have hDH : DistinctHeights (Qof E.P) := (goodShear_epsOf hE.hG.2).2.1
  have hdegr : E.M.deg (E.N.F E.M E.Q) (E.reg r) = Restore.degOf E.N r :=
    Gran.deg_region hNF hE.hregs.1 hE.hregs.2.2.2 hrN
  have hflag : c₂.nreg 81007 = 1 := hcpl (by rw [h4']; exact fullDegLe_interior (E.hQ hE.hG) hDH)
    (by rw [h4', a2, hdegr]; exact hhigh)
  obtain ⟨s1, s2, s3, s4⟩ := hsnd hflag
  rw [a2] at s4
  set t : ℕ × ℕ × ℕ := (c₂.nreg 81008, c₂.nreg 81009, c₂.nreg 81010) with htd
  have hfound : Restore.FoundOK E.M E.Q E.N E.reg r t := ⟨s1, s2, s3, s4⟩
  have K2 : ∀ q, 210000 ≤ q → q < 220000 → c₂.nreg q = c.nreg q := fun q h1 h2 =>
    (find_keeps F₂ (Or.inl ⟨h1, h2⟩)).trans (g₁ q (by omega))
  have K2c : c₂.nreg 230001 = c.nreg 230001 := (find_keeps F₂ (Or.inr rfl)).trans (g₁ _ (by omega))
  have mem₂ : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
    rw [F₂.2.2.1 a (by omega), m₁]
  -- 3. the test
  have htest : c₂.nreg 216003 < c₂.nreg 81007 := by
    rw [K2 _ (by norm_num) (by norm_num), c03, hflag]; norm_num
  -- 4. appending the triple
  set RB := c₀.nmem (E.H + 5) with hRB
  have hp : c₂.nreg 216031 = RB + 2 + 5 * r := by rw [K2 _ (by norm_num) (by norm_num), hI.ptr]
  have hRBr : RB + 5 * r + 4 < E.B₀ := hareas.2.2.1 r hrN
  have hnA : 0 < (E.N.region r).arcs.length := by
    have hne : (E.N.F E.M E.Q).Nonempty := by
      refine ⟨(E.N.chord 0).toSet E.M E.Q, E.N.chord 0, ?_, rfl⟩
      unfold NF.chord
      have h0 : 0 < E.N.chords.length := by simp [BuildNF.buildNF]; exact hKpos
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some]
      exact List.getElem_mem h0
    exact (Restore.region_arc (walkAx_of_goodModel hGM) hNF hE.hregs hne hrN).1
  have hlp := arcList_lt hNW₀ hrN (t := 0) hnA
  rw [← hRB] at hlp
  have hm2 : c₂.nmem (RB + 2 + 5 * r - 1) = c₀.nmem (RB + 5 * r + 1) := by
    rw [show RB + 2 + 5 * r - 1 = RB + 5 * r + 1 by omega, mem₂ _ (by omega),
      hI.low _ (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, d21, d20, d42, d43, d41, d400, d40, f₃⟩ := appT_exec (P := E.P)
    c₂ w₂ (d := E.B₀ + 3 * i) (n := i) (p := RB + 2 + 5 * r) (LB := c₀.nmem (E.H + 7))
    (by rw [K2 _ (by norm_num) (by norm_num), hI.dst])
    (by rw [K2 _ (by norm_num) (by norm_num), hI.cnt])
    (by rw [K2 _ (by norm_num) (by norm_num), c02]) (by rw [K2 _ (by norm_num) (by norm_num), c05])
    hp (by rw [K2 _ (by norm_num) (by norm_num), c16]) (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have w₃ := e₃.wb_right
  rw [show RB + 2 + 5 * r - 2 = RB + 5 * r by omega, mem₂ _ (by omega), hI.low _ (by omega)] at d42
  rw [hm2] at d43
  rw [K2 _ (by norm_num) (by norm_num), c001] at d400
  have g₃ : ∀ q, BappT q = false → c₃.nreg q = c₂.nreg q := f₃.1
  -- the memory of `c₃` below `B₀`
  have low₃ : ∀ a, a < E.B₀ → c₃.nmem a = c₀.nmem a := fun a ha => by
    rw [m₃, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega), mem₂ a (by omega), hI.low a ha]
  have agree₃ : ∀ a, a < E.B₀ → c₃.nmem a = c₀.nmem a := low₃
  -- the scan data
  have hBW : E.B₀ ≤ E.W := by omega
  have hscan : ∀ (m : ℕ → ℕ), (∀ a, a < E.B₀ → m a = c₀.nmem a) → (∀ a, m a ≤ E.W) →
      ∀ s, s < 2 → ScanGood E.P E.W E.M E.N r (endPos t s) m E.MD (m (E.H + 4))
        (m (E.H + 7) + m (m (E.H + 5) + 5 * r + 1)) := by
    intro m hm hmW s hs
    obtain ⟨xe, x1, xp, -⟩ := endPos_props (P := E.P) hGM hfound hs
    have hmA : ∀ a, a < E.A₀ → m a = E.m₀ a := fun a ha => (hm a (by omega)).trans (hE.hlow a ha)
    obtain ⟨hMDm, hwfm⟩ := Gran.desc_agree' hE.hwf hE.hMD hmA
    exact scanGood_of hGM hE.hG hE.hWh hE.hok hE.hperm hE.hsort hKpos hE.hregs
      (hNW₀.transport hm) hBW (hwfm.mono (by omega)) hMDm (by unfold REnv.R at hr; omega) xe x1 xp
  have hex : ∀ s, s < 2 → ∃ j ∈ (E.N.region r).arcs, matchB E.N.arcs.length j
      (tA E.M (Qof E.P) E.N (endPos t s) j) (tB E.M (Qof E.P) E.N (endPos t s) j) = true :=
    fun s hs => hex_of hGM hE.hok hE.hperm hE.hsort hKpos hE.hregs hrN hfound hs
  have hNA : (E.N.region r).arcs.length = c₀.nmem (RB + 5 * r) :=
    ((hNAt₀.2.2.2.2.2.2.2.1 r hrN).1).symm
  -- 5. the first scan
  have S1 := hscan c₃.nmem agree₃ w₃.2 0 (by norm_num)
  have hH7 : E.H + 7 < E.B₀ := hareas.1
  rw [agree₃ (E.H + 4) (by omega), agree₃ (E.H + 7) (by omega), agree₃ (E.H + 5) (by omega),
    ← hRB, agree₃ (RB + 5 * r + 1) (by omega)] at S1
  have e40 : c₃.nreg 216040 = (endPos t 0).edge := by rw [d40]; rfl
  have e41 : c₃.nreg 216041 = (endPos t 0).hgt := by rw [d41]; rfl
  have r3 : ∀ q, BappT q = false → 210000 ≤ q → q < 220000 → c₃.nreg q = c.nreg q :=
    fun q hq h1 h2 => (g₃ q hq).trans (K2 q h1 h2)
  obtain ⟨c₄, k₄, e₄, hk₄, fd₀, f₄⟩ := scanS_exec S1 c₃ w₃ rfl e40 e41
    (by omega) (by rw [d43])
    (by rw [r3 _ (by decide) (by norm_num) (by norm_num), c14, ← agree₃ _ (by omega)])
    (by rw [r3 _ (by decide) (by norm_num) (by norm_num), c17]; rfl)
    (by rw [r3 _ (by decide) (by norm_num) (by norm_num), c02])
    (by rw [r3 _ (by decide) (by norm_num) (by norm_num), c03])
    (by rw [d400]) (hex 0 (by norm_num))
  have w₄ := e₄.wb_right
  have g₄ : ∀ q, Bscan q = false → c₄.nreg q = c₃.nreg q := f₄.1
  -- 6. the first bucket
  have d22 : c₄.nreg 216022 = E.BK + 2 * i := by
    rw [g₄ _ (by decide), r3 _ (by decide) (by norm_num) (by norm_num), hI.dstB]
  obtain ⟨c₅, k₅, e₅, hk₅, m₅, d22', f₅⟩ := stB_exec (P := E.P) c₄ w₄ d22
    (by rw [g₄ _ (by decide), r3 _ (by decide) (by norm_num) (by norm_num), c02])
    (by omega)
  have w₅ := e₅.wb_right
  -- 7. the right end
  have ex₆ := Exec.copyN (P := E.P) w₅ 216040 81010
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 216040 (c₅.nreg 81010) } with hc₆
  have w₆ := ex₆.wb_right
  have f₆ : FrameB (fun r => decide (r = 216040)) c₅ c₆ := exec_frameB ex₆ (by decide)
  have g56 : ∀ q, q ≠ 216040 → c₆.nreg q = c₅.nreg q := fun q hq => by
    rw [hc₆]; simp [hq]
  have g5 : ∀ q, q ≠ 216022 → c₅.nreg q = c₄.nreg q := fun q hq => f₅.1 q (by simpa using hq)
  -- 8. the second scan
  have agree₆ : ∀ a, a < E.B₀ → c₆.nmem a = c₀.nmem a := fun a ha => by
    show c₅.nmem a = _
    rw [m₅, Machine.upd_other _ _ _ (by unfold REnv.BK at *; omega), f₄.2.2.1, agree₃ a ha]
  have S2 := hscan c₆.nmem agree₆ w₆.2 1 (by norm_num)
  rw [agree₆ (E.H + 4) (by omega), agree₆ (E.H + 7) (by omega), agree₆ (E.H + 5) (by omega),
    ← hRB, agree₆ (RB + 5 * r + 1) (by omega)] at S2
  have r6 : ∀ q, Bscan q = false → BappT q = false → q ≠ 216022 → q ≠ 216040 → 210000 ≤ q →
      q < 220000 → c₆.nreg q = c.nreg q := fun q h1 h2 h3 h4 h5 h6 => by
    rw [g56 q h4, g5 q h3, g₄ q h1, r3 q h2 h5 h6]
  have e40' : c₆.nreg 216040 = (endPos t 1).edge := by
    rw [hc₆]; simp only [Machine.upd_same]
    rw [g5 _ (by norm_num), g₄ _ (by decide), g₃ _ (by decide)]
    rfl
  have e41' : c₆.nreg 216041 = (endPos t 1).hgt := by
    rw [g56 _ (by norm_num), g5 _ (by norm_num), g₄ _ (by decide), d41]
    rfl
  have hnAd : (E.N.region r).arcs.length ≤ E.d0 + 1 := by
    have h1 := Restore.arcs_le_deg hGM hNF hE.hregs hrN
    have h2 := hE.hdeg (E.reg r) (hE.hregs.1.1 r hrN)
    omega
  obtain ⟨c₇, k₇, e₇, hk₇, fd₁, f₇⟩ := scanS_exec S2 c₆ w₆ rfl e40' e41'
    (by rw [g56 _ (by norm_num), g5 _ (by norm_num), g₄ _ (by decide), d42, hNA])
    (by rw [g56 _ (by norm_num), g5 _ (by norm_num), g₄ _ (by decide), d43])
    (by rw [r6 _ (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      c14, ← agree₆ (E.H + 4) (by omega)])
    (by rw [r6 _ (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      c17]; rfl)
    (by rw [r6 _ (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      c02])
    (by rw [r6 _ (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      c03])
    (by rw [g56 _ (by norm_num), g5 _ (by norm_num), g₄ _ (by decide), d400]) (hex 1 (by norm_num))
  have w₇ := e₇.wb_right
  -- 9. the second bucket
  obtain ⟨c₈, k₈, e₈, hk₈, m₈, d22'', f₈⟩ := stB_exec (P := E.P) c₇ w₇
    (d := E.BK + 2 * i + 1) (by rw [f₇.1 _ (by decide), g56 _ (by norm_num), d22'])
    (by rw [f₇.1 _ (by decide), r6 _ (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), c02]) (by omega)
  -- the execution
  have eApp : Exec E.P E.W appS c₂ c₈ (k₃ + (k₄ + (k₅ + (1 + (k₇ + k₈))))) :=
    .seq e₃ (.seq e₄ (.seq e₅ (.seq ex₆ (.seq e₇ e₈))))
  have eCall : Exec E.P E.W (callS E.sF) c c₈
      (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (1 + (k₇ + k₈)))) + 1))) :=
    .seq e₁ (.seq e₂ (.ifLtN_true htest eApp))
  -- the memory of `c₈`
  have m78 : c₈.nmem = upd (upd c₃.nmem (E.BK + 2 * i) (c₄.nreg 216053)) (E.BK + 2 * i + 1)
      (c₇.nreg 216053) := by
    rw [m₈, f₇.2.2.1]
    show upd c₅.nmem _ _ = _
    rw [m₅, f₄.2.2.1]
  have mlow : ∀ a, a < E.B₀ → c₈.nmem a = c.nmem a := fun a ha => by
    rw [m78, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), low₃ a ha,
      hI.low a ha]
  -- the frame
  have Fapp : FrameM Bapp c₂ c₈ :=
    (f₃.mono bapp_of_appT).trans (((FrameB.toM f₄).mono bapp_of_scan).trans
      ((f₅.mono bapp_of_22).trans (((FrameB.toM f₆).mono bapp_of_40).trans
        (((FrameB.toM f₇).mono bapp_of_scan).trans (f₈.mono bapp_of_22)))))
  have RF₁ : Restore.RF DrvR.drvBands E.B₀ c c₁ k₁ := rf_of_frameB inDrv_arg f₁
  have RF₂ : Restore.RF DrvR.drvBands E.B₀ c₁ c₂ k₂ :=
    (Restore.RF.of_frame F₂ (by rw [A₁]; omega)).mono find_bands le_rfl
  have RF₃ : Restore.RF DrvR.drvBands E.B₀ c₂ c₈ (k₃ + (k₄ + (k₅ + (1 + (k₇ + k₈)))) + 1) :=
    rf_of_frameM inDrv_app Fapp (fun a ha => by
      rw [mlow a ha, mem₂ a (by omega)])
  -- registers of `c₈`
  have G : ∀ q, Bapp q = false → c₈.nreg q = c₂.nreg q := Fapp.1
  have G3 : ∀ q, Bscan q = false → q ≠ 216022 → q ≠ 216040 → c₈.nreg q = c₃.nreg q :=
    fun q h1 h2 h3 => by
      rw [f₈.1 q (by simpa using h2), f₇.1 q h1, g56 q h3, g5 q h2, g₄ q h1]
  have fixq : ∀ q, FixR q → Bapp q = false := fun q hq => by
    unfold FixR at hq
    simp only [Bapp, BappT, Bscan, BuildRam.Bhalf, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  refine ⟨c₈, _, t, eCall, ?_, RF₁.trans (RF₂.trans RF₃), e₈.wb_right, hfound, ?_, ?_, ?_, ?_, ?_,
    mlow, fun q hq => ?_, ?_, ?_, ?_⟩
  · -- cost
    have hs1 : (scanK + 2) * (E.N.region r).arcs.length ≤ (scanK + 2) * (E.d0 + 1) :=
      Nat.mul_le_mul_left _ hnAd
    have hBf : E.Bf = Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ +
      2 * ((scanK + 2) * (E.d0 + 1)) + 60 := rfl
    unfold Restore.costF at hBf
    omega
  · -- buckets
    refine BktOK.snoc hI.hbk (fun q hq => ?_) ?_ ?_
    · show c₈.nmem (E.BK + q) = c.nmem (E.BK + q)
      rw [m78, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega), m₃,
        Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), mem₂ _ (by omega)]
    · show ScanFound E.M E.Q E.N r (endPos t 0) (c₈.nmem (E.BK + 2 * i))
      rw [m78, Machine.upd_other _ _ _ (by omega), Machine.upd_same]
      exact fd₀
    · show ScanFound E.M E.Q E.N r (endPos t 1) (c₈.nmem (E.BK + 2 * i + 1))
      rw [m78, Machine.upd_same]
      exact fd₁
  · rw [G3 _ (by decide) (by norm_num) (by norm_num), d20]
  · rw [G3 _ (by decide) (by norm_num) (by norm_num), d21]; ring
  · omega
  · -- the list
    rw [List.map_append]
    have hlen : (newL.map Prod.snd).length = i := by rw [List.length_map]
    have hm8 : ∀ a, a < E.BK → c₈.nmem a = c₃.nmem a := fun a ha => by
      rw [m78, Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
    refine Gran.ChordListAt.snoc hI.list (fun a h1 h2 => ?_) ?_ ?_ ?_
    · rw [hlen] at h2
      rw [hm8 a (by omega), m₃, Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        mem₂ a (by omega)]
    · rw [hlen, hm8 _ (by omega), m₃, Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), Machine.upd_same]
    · rw [hlen, hm8 _ (by omega), m₃, Machine.upd_other _ _ _ (by omega), Machine.upd_same]
    · rw [hlen, hm8 _ (by omega), m₃, Machine.upd_same]
  · rw [G q (fixq q hq), K2 q (by unfold FixR at hq; omega) (by unfold FixR at hq; omega)]
  · rw [G _ (by decide), K2 _ (by norm_num) (by norm_num)]
  · rw [G _ (by decide), K2 _ (by norm_num) (by norm_num)]
  · rw [G _ (by decide), K2c]

end

end DrvD

end Chazelle.Core
