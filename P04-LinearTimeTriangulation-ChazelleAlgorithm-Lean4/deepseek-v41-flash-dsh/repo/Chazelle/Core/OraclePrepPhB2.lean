module

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepHdr

/-!
# Lemma 3.6 (WP-H), preprocessing part 32: phase B composed

`phB := starStage; zipStage; dedupStage; setB`: from the state after phase A, the chord arrays of
the book `⟨A + 3, starList (rgi N) A, D⟩` (`D` the deduplicated zipper pairs), with `μ = A + 3` in
`60034`, the number of edges in `60037` and the number of inner chords in `60008`
(`phB_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- `μ = A + 3` and `E = μ + |I| + |O|`. -/
def setB : Stmt :=
  block [.addN 60034 120030 120048, .addN 60034 60034 120011, .addN 60037 60034 60003]

/-- **Phase B.** -/
def phB : Stmt := .seq starStage (.seq zipStage (.seq dedupStage setB))

/-- The bands of phase B. -/
def bBands : Finset ℕ := {bSign, bSort, bLocate, bDecomp, bOPrep, bOQuery}

theorem BZS_const {r : ℕ} (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BZS r = false := by
  simp only [BZS, BZB, BPR, BLS, BL, NFLoc.Bdir, NFLoc.Bloc, Bcmp, Bk, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega

theorem BSP_const {r : ℕ} (h1 : 120010 ≤ r) (h2 : r ≤ 120049) : BSP r = false := by
  simp only [BSP, BSA, BKI, BLZ, BTS, BL, NFLoc.Bdir, NFLoc.Bloc, Bcmp, Bk, BEm, BG, Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega

theorem sortCost_mono (κ : ℕ) {a b : ℕ} (h : a ≤ b) : SortR.sortCost κ a ≤ SortR.sortCost κ b := by
  unfold SortR.sortCost
  have := Nat.clog_mono_right 2 h
  gcongr

set_option maxHeartbeats 8000000 in
theorem phB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hHW : hostWords P.n ≤ W) {H : Host} {C : Chain} {N : NF} {m₀ : ℕ → ℕ} {D NB A₀ : ℕ}
    (hCQ : C.P = Qof P) (hsl : C.s < C.P.n)
    (hD : ChainDescAt m₀ D (Qof P) H C) (hwf : ChainWF P A₀ m₀ D)
    (hNFw : NFWithin m₀ NB A₀ N) (hN : IsNF (chainModel C) (Qof P) N)
    (hagree : ∀ a, a < A₀ → c.nmem a = m₀ a)
    (PL : PLoaded P D NB C.s C.m C.topIdx (m₀ (D + 4)) N.arcs.length N.chords.length
      (m₀ (NB + 3)) (m₀ (NB + 4)) (m₀ (NB + 5)) (m₀ (NB + 6)) (m₀ (NB + 7)) c)
    (h205 : c.nreg 110205 = 3) (hpk : PosK P.n C.s C.m (C.sideS C.sideBeta) (OracleQ.rT C) c)
    (hMD0 : c.nmem (c.nreg 120040) = 0)
    (hmdc : ∀ i, i < 5 → c.nmem (c.nreg 120040 + 1 + i) = m₀ (D + i))
    (hA₀MD : A₀ ≤ c.nreg 120040) (hTB : c.nreg 120041 = c.nreg 120040 + 6)
    (htab : ∀ j, j < c.nreg 120042 → c.nmem (c.nreg 120041 + j) = 2 ^ j)
    (hAlt : N.arcs.length < 2 ^ c.nreg 120042) {A₁ : ℕ} (hAl : c.nreg 9999 = A₁)
    (hTBA : c.nreg 120041 + c.nreg 120042 ≤ A₁)
    (hroom : A₁ + N.regions.length + 20 * N.arcs.length + 60 +
      SortR.sortCost 20 (2 * N.arcs.length + 5) ≤ W) :
    ∃ c' k, Exec P W phB c c' k ∧
      k ≤ 2 * N.arcs.length * (5500 * (c.nreg 120042 + 1) + 410) +
        3 * (5500 * (c.nreg 120042 + 1) + 262) + 150 * N.arcs.length + 600 +
        SortR.sortCost 20 (2 * N.arcs.length + 5) ∧
      GF bBands A₁ c c' ∧ (∀ r, 120010 ≤ r → r ≤ 120049 → c'.nreg r = c.nreg r) ∧
      A₁ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₁ + N.regions.length + 12 * N.arcs.length + 30 +
        SortR.sortCost 20 (2 * N.arcs.length + 5) ∧
      ∃ CH1 CH2 : ℕ, ∃ Dl : List (ℕ × ℕ),
        A₁ ≤ CH1 ∧ c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧
        c'.nreg 60008 = (starList (OracleQ.rgi N) N.arcs.length).length ∧
        c'.nreg 60034 = N.arcs.length + 3 ∧
        c'.nreg 60037 = N.arcs.length + 3 + (starList (OracleQ.rgi N) N.arcs.length ++ Dl).length ∧
        PairsAt c'.nmem CH1 CH2 (starList (OracleQ.rgi N) N.arcs.length ++ Dl) ∧
        CH1 + (starList (OracleQ.rgi N) N.arcs.length ++ Dl).length ≤ CH2 ∧
        CH2 + (starList (OracleQ.rgi N) N.arcs.length ++ Dl).length ≤ c'.nreg ALLOC ∧
        Dl.Nodup ∧ (∀ x, x ∈ Dl ↔ x ∈ OracleQ.zipRaw C (Qof P) N) ∧
        Dl.length ≤ 2 * N.arcs.length + 5 := by
  have hAL : ALLOC = 9999 := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hsimp : C.P.Simple := by rw [hCQ]; exact (shearInvariance (epsOf P) P).1 hG.1
  have hA0 := arcs_pos hsimp hN
  obtain ⟨hNB7, hABb, hSBb⟩ := NFLoc.nfWithin_bounds hNFw hN hA0
  have hNFc : NFAt c.nmem NB N := hNFw c.nmem hagree
  have hmn : C.m < P.n := by have := C.m_lt; rw [hCQ, hQn] at this; exact this
  have hm1 := C.one_le
  have hW8 : 8 * P.n + 32 ≤ W := by unfold hostWords at hHW; omega
  set MD := c.nreg 120040 with hMDdef
  set L := c.nreg 120042 with hLdef
  -- 1. the star chords
  have e4 : c.nmem (NB + 4) = m₀ (NB + 4) := hagree _ (by omega)
  have e6 : c.nmem (NB + 6) = m₀ (NB + 6) := hagree _ (by omega)
  have hM := rgMem_of hNFc hN
  rw [e4, e6] at hM
  obtain ⟨-, -, -, hAo⟩ := NFLoc.isNF_arcs hN
  have hρR : ∀ p, p < N.arcs.length →
      (fun j => (N.arc j).reg) ((fun p => N.seq.getD p 0) p) < N.regions.length := fun p hp => by
    obtain ⟨reg, -, hA, -⟩ := NFLoc.isNF_arcs hN
    exact (hA.1 _ (NFLoc.seq_lt hN hp)).1
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a9₁, b72, b73, b74, pairs₁⟩ := starStage_exec (P := P) hw hM PL.rNB
    PL.two hNFc.2.2.1 PL.rAB PL.rSB PL.rA PL.one hAl (by omega) (by omega) (by omega) hρR
    (by unfold chCap; omega)
  have hstar : starList (fun q => (fun j => (N.arc j).reg) ((fun p => N.seq.getD p 0) q))
      N.arcs.length = starList (OracleQ.rgi N) N.arcs.length := rfl
  rw [hstar] at b74 pairs₁
  have K₁ : ∀ r, (BFR r || BIS r) = false → c₁.nreg r = c.nreg r := F₁.1
  have k12₁ : ∀ r, 120010 ≤ r → r ≤ 120049 → c₁.nreg r = c.nreg r := fun r a b => K₁ r (by
    simp only [BFR, BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have PL₁ := PL.congr fun r hr => k12₁ r (by unfold PLReg at hr; omega)
    (by unfold PLReg at hr; omega)
  -- 2. the zipper
  have mem₁ : ∀ a, a < A₁ → c₁.nmem a = c.nmem a := F₁.2.2.1
  set V : QV := { qvOf c₁ with μ := N.arcs.length + 3 } with hV
  have hVMD : V.MD = MD := k12₁ _ (by norm_num) (by norm_num)
  have hVTB : V.TB = MD + 6 := by
    show c₁.nreg 120041 = _; rw [k12₁ _ (by norm_num) (by norm_num), hTB]
  have hVL : V.L = L := k12₁ _ (by norm_num) (by norm_num)
  have hVA : V.A = N.arcs.length := PL₁.rA
  have hZ : ZEnv P W A₁ C N V c₁ :=
    { good := hG
      hW := hW8
      CQ := hCQ
      simple := hsimp
      s_lt := by rw [hCQ, hQn] at hsl; exact hsl
      isNF := hN
      loc := zloc_of (m := c₁.nmem) (MD := MD) (TB := MD + 6) (L := L) hHW hsimp hD hwf hNFw hN
        (fun a ha => by rw [mem₁ a (by omega), hagree a ha])
        (by rw [mem₁ _ (by omega)]; exact hMD0)
        (fun i hi => by rw [mem₁ _ (by omega)]; exact hmdc i hi) hA₀MD le_rfl
        (fun j hj => by rw [mem₁ _ (by omega), ← hTB]; exact htab j hj) hAlt
        (by rw [← hTB]; exact hTBA) (by omega) hVMD PL₁.rNB hVTB hVL hVA PL₁.rAB PL₁.rSB (by simp [hV])
      pk := hpk.congr fun r hr => K₁ r (by
        simp only [BFR, BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
      rMD := rfl
      rNB := rfl
      rTB := rfl
      rL := rfl
      rA := rfl
      rAB := rfl
      rSB := rfl
      r3 := by rw [K₁ _ (by decide)]; exact h205 }
  set A₃ := A₁ + N.regions.length + 2 * chCap N.arcs.length with hA₃
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, a9₂, z93, z94, z95, pairsZ, -⟩ := zipStage_exec (P := P)
    e₁.wb_right hZ a9₁ (by omega) (by rw [hVA]; unfold zCap chCap at *; omega)
  rw [hVA] at a9₂ z94 pairsZ hk₂
  rw [hVL] at hk₂
  have K₂ : ∀ r, (BZS r || BSP r) = false → c₂.nreg r = c₁.nreg r := F₂.1
  have k12₂ : ∀ r, 120010 ≤ r → r ≤ 120049 → c₂.nreg r = c₁.nreg r := fun r a b => K₂ r (by
    rw [BZS_const a b, BSP_const a b]; rfl)
  have hnraw : (OracleQ.zipRaw C (Qof P) N).length ≤ 2 * N.arcs.length + 5 := by
    unfold OracleQ.zipRaw
    have := emitted_length_le (OracleQ.zipSk C (Qof P) N) N.arcs.length
    have := emitted_length_le (OracleQ.zipEk C (Qof P) N) N.arcs.length
    have : (OracleQ.zipSp C (Qof P) N).length ≤ 5 := by
      unfold OracleQ.zipSp OracleQ.zipSpO
      exact (List.length_filterMap_le _ _).trans (by simp)
    simp only [List.length_append]; omega
  have hnI : (starList (OracleQ.rgi N) N.arcs.length).length ≤ N.arcs.length := starList_length _ _
  -- 3. the deduplication
  set n := (OracleQ.zipRaw C (Qof P) N).length with hn
  set nI := (starList (OracleQ.rgi N) N.arcs.length).length with hnIdef
  set CH1 := A₁ + N.regions.length with hCH1
  set CH2 := A₁ + N.regions.length + chCap N.arcs.length with hCH2
  have hsc := sortCost_mono 20 hnraw
  have hchc : chCap N.arcs.length = 3 * N.arcs.length + 5 := rfl
  have hzc : zCap N.arcs.length = 2 * N.arcs.length + 5 := rfl
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mem₃, rm₃, o₃, al3a, al3b, v1, v2, v8, Dl, cnt, hDl, pairsD,
      hnd, hmem⟩ := dedupStage_exec (P := P) e₂.wb_right (CH1 := CH1) (CH2 := CH2) (nI := nI)
    (by rw [K₂ _ (by decide)]; exact b72) (by rw [K₂ _ (by decide)]; exact b73)
    (by rw [K₂ _ (by decide)]; exact b74) z93 z94 z95
    (by rw [k12₂ _ (by norm_num) (by norm_num)]; exact PL₁.one)
    (by rw [k12₂ _ (by norm_num) (by norm_num)]; exact PL₁.zero) a9₂
    (by omega) (by omega) (by omega)
    (by omega) (by omega)
    (by omega)
  have k12₃ : ∀ r, 120010 ≤ r → r ≤ 120049 → c₃.nreg r = c.nreg r := fun r a b => by
    rw [r₃ r (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]; omega) (by rw [hAL]; omega),
      k12₂ r a b, k12₁ r a b]
  -- 4. the numbers of the book
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, w34, w37⟩ : ∃ c₄ k₄, Exec P W setB c₃ c₄ k₄ ∧ k₄ = 3 ∧
      FrameB (fun r => decide (r = 60034 ∨ r = 60037)) c₃ c₄ ∧
      c₄.nreg 60034 = N.arcs.length + 3 ∧ c₄.nreg 60037 = N.arcs.length + 3 + (nI + Dl.length) := by
    have hwr : wr (fun r => decide (r = 60034 ∨ r = 60037)) setB = true := by decide
    suffices H : ∃ c₄ k₄, Exec P W setB c₃ c₄ k₄ ∧ k₄ = 3 ∧ c₄.nreg 60034 = N.arcs.length + 3 ∧
        c₄.nreg 60037 = N.arcs.length + 3 + (nI + Dl.length) by
      obtain ⟨c₄, k₄, ex, hk, a, b⟩ := H
      exact ⟨c₄, k₄, ex, hk, exec_frameB ex hwr, a, b⟩
    have w₃ := e₃.wb_right
    have g30 : c₃.nreg 120030 = N.arcs.length := by rw [k12₃ _ (by norm_num) (by norm_num), PL.rA]
    have g48 : c₃.nreg 120048 = 2 := by rw [k12₃ _ (by norm_num) (by norm_num), PL.two]
    have g11 : c₃.nreg 120011 = 1 := by rw [k12₃ _ (by norm_num) (by norm_num), PL.one]
    unfold setB
    exec_block
    · rw [g30, g48]; omega
    · config_simp; rw [g30, g48, g11]; omega
    · config_simp; rw [g30, g48, g11, cnt]; omega
    · exact ⟨rfl, by config_simp; rw [g30, g48, g11], by config_simp; rw [g30, g48, g11, cnt]⟩
  have ex : Exec P W phB c c₄ _ := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have hA₄ : A₃ + 2 * zCap N.arcs.length = A₃ + 4 * N.arcs.length + 10 := by rw [hzc]; ring
  have k12₄ : ∀ r, 120010 ≤ r → r ≤ 120049 → c₄.nreg r = c.nreg r := fun r a b => by
    have h4 : (decide (r = 60034 ∨ r = 60037)) = false := by
      simp only [decide_eq_false_iff_not]; omega
    rw [F₄.1 r h4, k12₃ r a b]
  refine ⟨c₄, _, ex, ?_, ?_, k12₄, ?_, ?_, CH1, CH2, Dl, by omega, by rw [F₄.1 _ (by decide), v1],
    by rw [F₄.1 _ (by decide), v2], by rw [F₄.1 _ (by decide), v8], w34,
    by rw [w37, List.length_append], ?_, ?_, ?_, hnd, fun x => ?_, by omega⟩
  · have := hk₃; omega
  · -- the frame
    have hband : ∀ r, (110000 ≤ r ∧ r < 130000) → bandOf r ∈ bBands := by
      intro r h; simp only [bBands, Finset.mem_insert, Finset.mem_singleton, bOPrep, bOQuery,
        bandOf]; omega
    have G₁ : GF bBands A₁ c c₁ := PF.gf F₁ (fun r hr => by
        simp only [BFR, BIS, Bool.or_eq_true, decide_eq_true_eq] at hr
        by_cases h9 : r = 9999
        · exact Or.inr h9
        · left; exact hband r (by omega))
      (fun r => exec_rframeS e₁ (B := fun _ => false) (by decide) r rfl) le_rfl
    have hrr₂ : ∀ r, Bk r = false → c₂.rreg r = c₁.rreg r := exec_rframeS e₂ (by decide)
    have G₂ : GF bBands A₁ c₁ c₂ :=
      ⟨fun r hr hra => F₂.1 r (by
          by_contra h'; simp only [Bool.not_eq_false] at h'
          simp only [BZS, BZB, BPR, BLS, BL, NFLoc.Bdir, NFLoc.Bloc, Bcmp, Bk, BSP, BSA, BKI, BLZ, BTS, BEm, BG,
            Bool.or_eq_true, decide_eq_true_eq] at h'
          apply hr
          simp only [bBands, Finset.mem_insert, Finset.mem_singleton, bSign, bLocate, bOPrep,
            bOQuery, bSort, bDecomp, bandOf]
          unfold ALLOC at hra
          omega),
        fun r hr => hrr₂ r (by
          simp only [Bk, decide_eq_false_iff_not]; intro h
          exact hr (by simp only [bBands, Finset.mem_insert, Finset.mem_singleton, bSign, bandOf]
                       omega)),
        fun a ha => F₂.2.2.1 a (by omega), fun a ha => F₂.2.2.2.1 a (by omega), F₂.2.2.2.2⟩
    have G₃ : GF bBands A₁ c₂ c₃ :=
      ⟨fun r hr hra => r₃ r (fun h => hr (by
          simp only [dBands, Finset.mem_insert, Finset.mem_singleton] at h
          simp only [bBands, Finset.mem_insert, Finset.mem_singleton]; tauto)) hra,
        fun r hr => rr₃ r (fun h => hr (by
          simp only [dBands, Finset.mem_insert, Finset.mem_singleton] at h
          simp only [bBands, Finset.mem_insert, Finset.mem_singleton]; tauto)),
        fun a ha => mem₃ a (Or.inl (by omega)), fun a ha => rm₃ a (by omega), o₃⟩
    have hb6 : ∀ r, bandOf r ∉ bBands → (decide (r = 60034 ∨ r = 60037)) = false := by
      intro r hr
      have : bandOf r ≠ 6 := fun h => hr (by simp [bBands, bDecomp, h])
      unfold bandOf at this
      simp only [decide_eq_false_iff_not]; omega
    have G₄ : GF bBands A₁ c₃ c₄ :=
      ⟨fun r hr _ => F₄.1 r (hb6 r hr), fun r hr => F₄.2.1 r (hb6 r hr),
        fun a _ => by rw [F₄.2.2.1], fun a _ => by rw [F₄.2.2.2.1], F₄.2.2.2.2⟩
    exact G₁.trans (G₂.trans (G₃.trans G₄))
  · rw [hAL] at al3a; rw [hAL, F₄.1 _ (by decide)]; omega
  · rw [hAL] at al3b; rw [hAL, F₄.1 _ (by decide)]; omega
  · refine PairsAt.append (fun t ht => ?_) ?_
    · rw [F₄.2.2.1, mem₃ _ (Or.inl (by omega)), mem₃ _ (Or.inr (Or.inl ⟨by omega,
        by omega⟩)), F₂.2.2.1 _ (by omega), F₂.2.2.1 _ (by omega)]
      exact pairs₁ t ht
    · rw [F₄.2.2.1]; exact pairsD
  · rw [List.length_append]; omega
  · rw [hAL] at al3a; rw [List.length_append, hAL, F₄.1 _ (by decide)]; omega
  · rw [hmem x]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨p1, p2⟩ := pairsZ i hi
      rw [z93, z94] at *
      rw [p1, p2]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    · intro hx
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
      refine ⟨i, hi, ?_⟩
      obtain ⟨p1, p2⟩ := pairsZ i hi
      rw [p1, p2, NFLoc.getD_of_lt _ hi, e]

end

end OracleR

end Chazelle.Core
