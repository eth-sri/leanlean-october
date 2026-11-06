module

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepCh
public import Chazelle.Core.ShearInv

/-!
# Lemma 3.6 (WP-H), preprocessing part 28: phase A (constants, descriptor, tables)

`phA := pLoad; setA; mdS; tbS; posTS; posInit`: the constants of the query in band `12`
(`PLoaded`), a neutral origin and direction (`120023 … 120025`), the model descriptor (`MD`), the
table of powers (`TB`, `L`), the inverse of the arc-sequence table (`POS`) and the constants of the
walk positions (`PosK`).  Main result: `phA_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- `wrROK` that also accepts natural stores. -/
def wrRSOK (B : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | i => wrROK B i

/-- Every instruction of the statement satisfies `wrRSOK B`. -/
def wrRS (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrRSOK B i
  | .seq s t => wrRS B s && wrRS B t
  | .ifLtN _ _ t e => wrRS B t && wrRS B e
  | .ifLtR _ _ t e => wrRS B t && wrRS B e
  | .whileLtN _ _ b => wrRS B b
  | .whileLtR _ _ b => wrRS B b

/-- **Real-register frame** with natural stores allowed. -/
theorem exec_rframeS {P : Polygon} {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrRS B s = true) : ∀ r, B r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact fun _ _ => rfl
  | @instr ins c c' _ he _ _ =>
    ϴ' wrRS at hs
    cases ins <;> ϴ' wrRSOK, wrROK, Bool.false_eq_true at hs <;>
      ϴ' Instr.effect, Option.some.injEq at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (simp only [upd]; split_ifs with hh
         · subst hh; simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    ϴ' wrRS, Bool.and_eq_true at hs
    exact fun r hr => (ih₂ hs.2 r hr).trans (ih₁ hs.1 r hr)
  | ifLtN_true _ _ ih =>
    ϴ' wrRS, Bool.and_eq_true at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    ϴ' wrRS, Bool.and_eq_true at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    ϴ' wrRS, Bool.and_eq_true at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    ϴ' wrRS, Bool.and_eq_true at hs; exact ih hs.2
  | whileLtN_false _ _ => exact fun _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ =>
    exact fun r hr => (ih₂ hs r hr).trans (ih₁ (by simpa [wrRS] using hs) r hr)
  | whileLtR_false _ _ => exact fun _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ =>
    exact fun r hr => (ih₂ hs r hr).trans (ih₁ (by simpa [wrRS] using hs) r hr)

/-- The registers of `PLoaded`. -/
def PLReg (r : ℕ) : Prop :=
  (120010 ≤ r ∧ r ≤ 120022) ∨ r = 120028 ∨ r = 120029 ∨ r = 120030 ∨ r = 120039 ∨
    (120043 ≤ r ∧ r ≤ 120048)

theorem PLoaded.congr {P : Polygon} {D NB s mm ti bb A K CB AB RB SB LB : ℕ} {c c' : Config}
    (h : PLoaded P D NB s mm ti bb A K CB AB RB SB LB c)
    (hr : ∀ r, PLReg r → c'.nreg r = c.nreg r) : PLoaded P D NB s mm ti bb A K CB AB RB SB LB c' := by
  have g : ∀ r, PLReg r → ∀ v, c.nreg r = v → c'.nreg r = v := fun r h v hv => (hr r h).trans hv
  exact ⟨g _ (by unfold PLReg; omega) _ h.n, g _ (by unfold PLReg; omega) _ h.one,
    g _ (by unfold PLReg; omega) _ h.zero, g _ (by unfold PLReg; omega) _ h.two,
    g _ (by unfold PLReg; omega) _ h.six, g _ (by unfold PLReg; omega) _ h.rD,
    g _ (by unfold PLReg; omega) _ h.rNB, g _ (by unfold PLReg; omega) _ h.rs,
    g _ (by unfold PLReg; omega) _ h.rm, g _ (by unfold PLReg; omega) _ h.rti,
    g _ (by unfold PLReg; omega) _ h.rbb, g _ (by unfold PLReg; omega) _ h.twoM,
    g _ (by unfold PLReg; omega) _ h.nW, g _ (by unfold PLReg; omega) _ h.tEnd,
    g _ (by unfold PLReg; omega) _ h.sS, g _ (by unfold PLReg; omega) _ h.tv,
    g _ (by unfold PLReg; omega) _ h.rA, g _ (by unfold PLReg; omega) _ h.rK,
    g _ (by unfold PLReg; omega) _ h.rCB, g _ (by unfold PLReg; omega) _ h.rAB,
    g _ (by unfold PLReg; omega) _ h.rRB, g _ (by unfold PLReg; omega) _ h.rSB,
    g _ (by unfold PLReg; omega) _ h.rLB⟩

/-- A neutral origin and direction, and the granularity saved in `120049`. -/
def setA : Stmt :=
  block [.constN 120025 2, .constN 120023 0, .constN 120024 0, .copyN 120049 110002,
    .copyN 120026 9999]

/-- The constant `3` of the zipper; the chord table into `120038`. -/
def setZ : Stmt := block [.constN 110205 3, .copyN 120038 60120]

/-- **Phase A.** -/
def phA : Stmt :=
  .seq pLoad (.seq setA (.seq chSortS (.seq setZ (.seq mdS (.seq tbS (.seq posTS posInit))))))

/-- The side of the top from the descriptor. -/
theorem sS_of_desc {m : ℕ → ℕ} {D : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hD : ChainDescAt m D Q H C) :
    (if m (D + 4) = 1 then C.topIdx else 2 * C.m - C.topIdx) = C.sideS C.sideBeta := by
  obtain ⟨-, -, -, -, -, hd4⟩ := hD
  unfold Chain.sideS
  by_cases hb : C.sideBeta = true
  · Ξ ite_eq_left (hd4.2 hb), ite_eq_left hb
  · Ξ ite_eq_right (fun h => hb (hd4.1 h)), ite_eq_right hb

/-- The chord order only reads the chord area, the chain and the top vertex of the values. -/
theorem chLe_V_congr {P : Polygon} {C : Chain} {V V' : QV} {m : ℕ → ℕ} {i j : ℕ}
    (hCB : V.CB = V'.CB) (hm : V.m = V'.m) (hs : V.s = V'.s) (htv : V.tv = V'.tv) :
    ChLe P C V m i j ↔ ChLe P C V' m i j := by
  unfold ChLe xpX' xpSym chH chL
  Ξ hCB, hm, hs, htv

theorem arcs_pos {C : Chain} {Q : Polygon} {N : NF} (hs : C.P.Simple)
    (hN : IsNF (chainModel C) Q N) : 0 < N.arcs.length := by
  obtain ⟨⟨U, hU, a, b, hab⟩, -⟩ := arcCover (chainModel C) Q (N.F (chainModel C) Q)
    (Or.inl ⟨C, hs, rfl⟩) hN.1
  obtain ⟨j, hj, -⟩ := NFLoc.listed_of_isArc hN hU hab
  omega

/-- The bands of phase A. -/
def aBands : Finset ℕ := {bSort, bSign, bDecomp, bOPrep, bOQuery}


theorem phA_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {H : Host} {C : Chain} {N : NF} {A₀ : ℕ}
    (hD : ChainDescAt c.nmem (c.nreg 110000) (Qof P) H C) (hCQ : C.P = Qof P)
    (hsl : C.s < C.P.n) (hNFw : NFWithin c.nmem (c.nreg 110001) A₀ N)
    (hN : IsNF (chainModel C) (Qof P) N) (hAl : c.nreg 9999 = A₀)
    (hDA : c.nreg 110000 + 5 ≤ A₀)
    (hroom : A₀ + 3 * (N.arcs.length + N.chords.length) +
      SortR.sortCost 500 N.chords.length + 20 ≤ W) :
    ∃ cA k, Exec P W phA c cA k ∧
      k ≤ 8 * Nat.clog 2 (N.arcs.length + N.chords.length + 1) + 8 * N.arcs.length +
        7 * N.chords.length + SortR.sortCost 500 N.chords.length + 230 ∧
      FrameN aBands c cA ∧
      A₀ + N.chords.length ≤ cA.nreg 120038 ∧ cA.nreg 120038 + N.chords.length ≤ cA.nreg 120040 ∧
      cA.nreg 120040 ≤ A₀ + N.chords.length + SortR.sortCost 500 N.chords.length ∧
      cA.nreg 9999 = cA.nreg 120040 + 6 + Nat.clog 2 (N.arcs.length + N.chords.length + 1) +
        N.arcs.length ∧
      PLoaded P (c.nreg 110000) (c.nreg 110001) C.s C.m C.topIdx (c.nmem (c.nreg 110000 + 4))
        N.arcs.length N.chords.length (c.nmem (c.nreg 110001 + 3)) (c.nmem (c.nreg 110001 + 4))
        (c.nmem (c.nreg 110001 + 5)) (c.nmem (c.nreg 110001 + 6)) (c.nmem (c.nreg 110001 + 7)) cA ∧
      cA.nreg 120025 = 2 ∧ cA.nreg 120023 = 0 ∧ cA.nreg 120024 = 0 ∧
      cA.nreg 120049 = c.nreg 110002 ∧ cA.nreg 110205 = 3 ∧ cA.nreg 120026 = A₀ ∧
      cA.nmem (cA.nreg 120040) = 0 ∧
      (∀ i, i < 5 → cA.nmem (cA.nreg 120040 + 1 + i) = c.nmem (c.nreg 110000 + i)) ∧
      cA.nreg 120041 = cA.nreg 120040 + 6 ∧
      cA.nreg 120042 = Nat.clog 2 (N.arcs.length + N.chords.length + 1) ∧
      (∀ j, j < Nat.clog 2 (N.arcs.length + N.chords.length + 1) →
        cA.nmem (cA.nreg 120041 + j) = 2 ^ j) ∧
      N.arcs.length < 2 ^ Nat.clog 2 (N.arcs.length + N.chords.length + 1) ∧
      N.chords.length < 2 ^ Nat.clog 2 (N.arcs.length + N.chords.length + 1) ∧
      cA.nreg 120031 = cA.nreg 120041 + Nat.clog 2 (N.arcs.length + N.chords.length + 1) ∧
      (∀ j, j < N.arcs.length → cA.nmem (cA.nreg 120031 + j) < N.arcs.length ∧
        N.seq.getD (cA.nmem (cA.nreg 120031 + j)) 0 = j) ∧
      PosK P.n C.s C.m (C.sideS C.sideBeta) (OracleQ.rT C) cA ∧
      (∀ q, q < N.chords.length → cA.nmem (cA.nreg 120038 + q) < N.chords.length) ∧
      (∀ q q', q < N.chords.length → q' < N.chords.length →
        cA.nmem (cA.nreg 120038 + q) = cA.nmem (cA.nreg 120038 + q') → q = q') ∧
      (∀ q q', q ≤ q' → q' < N.chords.length →
        ChLe P C (qvOf cA) c.nmem (cA.nmem (cA.nreg 120038 + q)) (cA.nmem (cA.nreg 120038 + q'))) := by
  have hAL : ALLOC = 9999 := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hsimp : C.P.Simple := by rw [hCQ]; exact (shearInvariance (epsOf P) P).1 hG.1
  have hNF := hNFw.nfAt
  have hA0 := arcs_pos hsimp hN
  obtain ⟨hNB7, hABb, hSBb⟩ := NFLoc.nfWithin_bounds hNFw hN hA0
  have hLle : Nat.clog 2 (N.arcs.length + N.chords.length + 1) ≤
      N.arcs.length + N.chords.length + 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]; exact (Nat.lt_two_pow_self).le
  have hmn : C.m < P.n := by have := C.m_lt; rw [hCQ, hQn] at this; exact this
  have hm1 := C.one_le
  have hsc := SortR.sortCost_ge 500 N.chords.length
  -- 1. the constants
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, PL₁⟩ := pLoad_exec (P := P) c hw hD hCQ hsl hNF (by omega)
    (by omega) hW
  -- 2. the neutral registers
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, s25, s23, s24, s49, s26⟩ : ∃ c₂ k₂, Exec P W setA c₁ c₂ k₂ ∧
      k₂ = 5 ∧ FrameB (fun r => decide (r = 120025 ∨ r = 120023 ∨ r = 120024 ∨ r = 120049 ∨
        r = 120026)) c₁ c₂ ∧
      c₂.nreg 120025 = 2 ∧ c₂.nreg 120023 = 0 ∧ c₂.nreg 120024 = 0 ∧
      c₂.nreg 120049 = c.nreg 110002 ∧ c₂.nreg 120026 = A₀ := by
    have hwr : wr (fun r => decide (r = 120025 ∨ r = 120023 ∨ r = 120024 ∨ r = 120049 ∨
      r = 120026)) setA = true := by decide
    suffices H : ∃ c₂ k₂, Exec P W setA c₁ c₂ k₂ ∧ k₂ = 5 ∧
        c₂.nreg 120025 = 2 ∧ c₂.nreg 120023 = 0 ∧ c₂.nreg 120024 = 0 ∧
        c₂.nreg 120049 = c.nreg 110002 ∧ c₂.nreg 120026 = A₀ by
      obtain ⟨c₂, k₂, ex, hk, a, b, d, e, f⟩ := H
      exact ⟨c₂, k₂, ex, hk, exec_frameB ex hwr, a, b, d, e, f⟩
    have w₁ := e₁.wb_right
    have hW3 : 3 ≤ W := by omega
    unfold setA
    exec_block
    all_goals (try omega)
    exact ⟨rfl, by config_simp, by config_simp, by config_simp,
      by config_simp; exact F₁.1 _ (by decide),
      by config_simp; rw [F₁.1 _ (by decide), hAl]⟩
  have PL₂ := PL₁.congr fun r hr => F₂.1 r (by
    unfold PLReg at hr; simp only [decide_eq_false_iff_not]; omega)
  have a9₂ : c₂.nreg 9999 = A₀ := by rw [F₂.1 _ (by decide), F₁.1 _ (by decide), hAl]
  have hm₂ : c₂.nmem = c.nmem := F₂.2.2.1.trans F₁.2.2.1
  -- 3. the chord table
  have hq₂ : QConst P (qvOf c₂) c₂ := qconst_qvOf PL₂.n PL₂.one PL₂.zero PL₂.two PL₂.six
    (by rw [PL₂.twoM, PL₂.rm]) (by rw [PL₂.nW, PL₂.rm]) (by rw [PL₂.tEnd, PL₂.rm]) s25
  have hv₂ : QVOK P C (qvOf c₂) :=
    ⟨hCQ, PL₂.rs, PL₂.rm, by show c₂.nreg 120021 = _; rw [PL₂.sS]; exact sS_of_desc hD,
      by show c₂.nreg 120023 < P.n; rw [s23]; omega, by show c₂.nreg 120024 ≤ 1; rw [s24]; omega,
      by show c₂.nreg 120015 < P.n; rw [PL₂.rs]; rw [hCQ, hQn] at hsl; exact hsl⟩
  have hK₂ : (qvOf c₂).K = N.chords.length := PL₂.rK
  have hCB₂ : (qvOf c₂).CB = c.nmem (c.nreg 110001 + 3) := PL₂.rCB
  have hrec : ∀ i, i < (qvOf c₂).K → (qvOf c₂).CB + 5 * i + 2 ≤ A₀ := fun i hi => by
    rw [hK₂] at hi
    have h1 : Robust A₀ c.nmem fun m' => m' (m' (c.nreg 110001 + 3) + (5 * i + 4)) =
        (N.chord i).dn := fun m' hm' => by
      have := ((hNFw m' hm').2.2.2.2.2.1 i hi).2.2.2.2
      simpa only [Nat.add_assoc] using this
    have := (NFLoc.robust_addr2 h1).2
    rw [hCB₂]; omega
  have hh : ∀ i, i < (qvOf c₂).K → c₂.nmem ((qvOf c₂).CB + 5 * i) < P.n := fun i hi => by
    rw [hK₂] at hi
    rw [hm₂, hCB₂, (hNF.2.2.2.2.2.1 i hi).1]
    obtain ⟨-, -, -, -, -, -, -, -, -, hhh, -⟩ := hN
    have := hhh i hi; rwa [hQn] at this
  have htv : (qvOf c₂).tv < P.n := by
    show c₂.nreg 120022 < P.n; rw [PL₂.tv]; exact Nat.mod_lt _ (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, al3a, al3b, R6₃, R12₃, ch1, ch2, chlt, chinj, chsort⟩ :=
    chSort_exec (P := P) hG hW e₂.wb_right hv₂ hq₂ a9₂ hrec hh htv (by omega)
      (by rw [hK₂]; omega)
  rw [hK₂] at hk₃ al3a al3b ch1 ch2 chlt chinj chsort
  rw [hAL] at al3a al3b ch2
  set A₁ := c₃.nreg 9999 with hA₁
  have PL₃ := PL₂.congr fun r hr => R12₃ r (by unfold PLReg at hr; omega)
    (by unfold PLReg at hr; omega)
  -- 4. the zipper constant and the chord table
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, z205, z38⟩ : ∃ c₄ k₄, Exec P W setZ c₃ c₄ k₄ ∧ k₄ = 2 ∧
      FrameB (fun r => decide (r = 110205 ∨ r = 120038)) c₃ c₄ ∧ c₄.nreg 110205 = 3 ∧
      c₄.nreg 120038 = c₃.nreg 60120 := by
    have hwr : wr (fun r => decide (r = 110205 ∨ r = 120038)) setZ = true := by decide
    suffices H : ∃ c₄ k₄, Exec P W setZ c₃ c₄ k₄ ∧ k₄ = 2 ∧ c₄.nreg 110205 = 3 ∧
        c₄.nreg 120038 = c₃.nreg 60120 by
      obtain ⟨c₄, k₄, ex, hk, a, b⟩ := H
      exact ⟨c₄, k₄, ex, hk, exec_frameB ex hwr, a, b⟩
    have w₃ := e₃.wb_right
    unfold setZ
    exec_block
    · omega
    · exact ⟨rfl, by config_simp, by config_simp⟩
  have PL₄ := PL₃.congr fun r hr => F₄.1 r (by
    unfold PLReg at hr; simp only [decide_eq_false_iff_not]; omega)
  have a9₄ : c₄.nreg 9999 = A₁ := by rw [F₄.1 _ (by decide)]
  -- 5. the model descriptor
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, a9₅, md₅, m0₅, mi₅⟩ := mdS_exec (P := P) e₄.wb_right PL₄.rD
    PL₄.one a9₄ (by omega) (by omega)
  have PL₅ := PL₄.congr fun r hr => F₅.1 r (by
    unfold PLReg at hr; simp only [BMD, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 6. the table of powers
  obtain ⟨c₆, k₆, e₆, hk₆, F₆, a9₆, tb₆, l₆, tab₆, Alt, Klt⟩ := tbS_exec (P := P) e₅.wb_right
    PL₅.rA PL₅.rK PL₅.one a9₅ (by omega)
  have PL₆ := PL₅.congr fun r hr => F₆.1 r (by
    unfold PLReg at hr; simp only [BTB, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 7. the inverse table
  have mem₆ : ∀ a, a < A₀ → c₆.nmem a = c.nmem a := fun a ha => by
    rw [F₆.2.2.1 _ (by omega), F₅.2.2.1 _ (by omega), F₄.2.2.1,
      F₃.2.2.1 a (by rw [hAL, a9₂]; exact ha), hm₂]
  have hseq : ∀ p, p < N.arcs.length →
      c₆.nmem (c.nmem (c.nreg 110001 + 6) + p) = N.seq.getD p 0 := fun p hp => by
    rw [mem₆ _ (by omega)]
    exact hNF.2.2.2.2.2.2.2.2.1 p (by rw [NFLoc.seq_length hN]; exact hp)
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, a9₇, pos₇, pf₇⟩ := posTS_exec (P := P) e₆.wb_right PL₆.rSB PL₆.rA
    PL₆.one a9₆ hseq (by omega) (by omega) (fun p hp => NFLoc.seq_lt hN hp)
    (fun p q hp hq e => by
      have hnd := OracleQ.seq_nodup hN
      have hl := NFLoc.seq_length hN
      rw [NFLoc.getD_of_lt 0 (by omega), NFLoc.getD_of_lt 0 (by omega)] at e
      exact (List.Nodup.getElem_inj_iff hnd).1 e)
    (fun j hj => NFLoc.seq_surj hN hj)
  have PL₇ := PL₆.congr fun r hr => F₇.1 r (by
    unfold PLReg at hr; simp only [BPT, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 8. the position constants
  have hSs : c₇.nreg 120021 = C.sideS C.sideBeta := by rw [PL₇.sS]; exact sS_of_desc hD
  obtain ⟨c₈, k₈, e₈, hk₈, F₈, q0, q1, q2, q3, q4⟩ := posInit_exec (P := P) e₇.wb_right PL₇.rm
    PL₇.twoM hSs (C.sideS_lt _) hm1 (by omega)
  have PL₈ := PL₇.congr fun r hr => F₈.1 r (by
    unfold PLReg at hr; simp only [BPI, decide_eq_false_iff_not]; omega)
  have ex : Exec P W phA c c₈ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  -- the later stages keep the registers outside their sets and the memory below `A₁`
  have K58 : ∀ r, BPI r = false → BPT r = false → BTB r = false → BMD r = false →
      c₈.nreg r = c₄.nreg r := fun r a b d e => by
    rw [F₈.1 r a, F₇.1 r b, F₆.1 r d, F₅.1 r e]
  have M48 : ∀ a, a < A₁ → c₈.nmem a = c₄.nmem a := fun a ha => by
    rw [F₈.2.2.1, F₇.2.2.1 a (by omega), F₆.2.2.1 a (by omega), F₅.2.2.1 a ha]
  have hMD : c₈.nreg 120040 = A₁ := by
    rw [F₈.1 _ (by decide), F₇.1 _ (by decide), F₆.1 _ (by decide), md₅]
  have hCH : c₈.nreg 120038 = c₃.nreg 60120 := by
    rw [K58 _ (by decide) (by decide) (by decide) (by decide), z38]
  have hV : ∀ q q', ChLe P C (qvOf c₂) c₂.nmem q q' ↔ ChLe P C (qvOf c₈) c.nmem q q' := by
    intro q q'
    rw [hm₂]
    exact chLe_V_congr (by show c₂.nreg 120043 = c₈.nreg 120043; rw [PL₂.rCB, PL₈.rCB])
      (by show c₂.nreg 120016 = c₈.nreg 120016; rw [PL₂.rm, PL₈.rm])
      (by show c₂.nreg 120015 = c₈.nreg 120015; rw [PL₂.rs, PL₈.rs])
      (by show c₂.nreg 120022 = c₈.nreg 120022; rw [PL₂.tv, PL₈.tv])
  refine ⟨c₈, _, ex, by omega, ?_, by rw [hCH]; exact ch1, by rw [hCH, hMD]; exact ch2,
    by rw [hMD]; exact al3b, ?_, PL₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Alt, Klt, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- the frame
    have hband : ∀ r, (110000 ≤ r ∧ r < 130000) → bandOf r ∈ aBands := by
      intro r h; simp only [aBands, Finset.mem_insert, Finset.mem_singleton, bOPrep, bOQuery,
        bandOf]; omega
    have hrr₁ : ∀ r, c₂.rreg r = c.rreg r := fun r =>
      exec_rframeS (.seq e₁ e₂) (B := fun _ => false) (by decide) r rfl
    have FA : FrameN aBands c c₂ := PF.frameN (B := fun r => BPL r ||
        decide (r = 120025 ∨ r = 120023 ∨ r = 120024 ∨ r = 120049 ∨ r = 120026))
      ⟨fun r hr => by
        simp only [Bool.or_eq_false_iff] at hr; rw [F₂.1 r hr.2, F₁.1 r hr.1],
        fun r _ => hrr₁ r, fun a _ => by rw [hm₂], fun a _ => by rw [F₂.2.2.2.1, F₁.2.2.2.1],
        by rw [F₂.2.2.2.2, F₁.2.2.2.2]⟩
      (fun r hr => by
        simp only [BPL, Bool.or_eq_true, decide_eq_true_eq] at hr
        left; exact hband r (by omega)) (hrr₁ _)
    have FB : FrameN aBands c₂ c₃ := FrameN.mono F₃ (by decide)
    have hrr₂ : ∀ r, c₈.rreg r = c₃.rreg r := fun r =>
      exec_rframeS (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))) (B := fun _ => false) (by decide) r rfl
    have FC : FrameN aBands c₃ c₈ := PF.frameN (B := fun r => decide (r = 110205 ∨ r = 120038) || BMD r ||
        BTB r || BPT r || BPI r)
      ⟨fun r hr => by
        simp only [Bool.or_eq_false_iff] at hr
        rw [K58 r hr.2 hr.1.2 hr.1.1.2 hr.1.1.1.2, F₄.1 r hr.1.1.1.1],
        fun r _ => hrr₂ r, fun a ha => by rw [hAL] at ha; rw [M48 a ha, F₄.2.2.1],
        fun a ha => by
          rw [hAL] at ha
          rw [F₈.2.2.2.1, F₇.2.2.2.1 a (by omega), F₆.2.2.2.1 a (by omega), F₅.2.2.2.1 a ha,
            F₄.2.2.2.1],
        by rw [F₈.2.2.2.2, F₇.2.2.2.2, F₆.2.2.2.2, F₅.2.2.2.2, F₄.2.2.2.2]⟩
      (fun r hr => by
        simp only [BMD, BTB, BPT, BPI, Bool.or_eq_true, decide_eq_true_eq] at hr
        by_cases h9 : r = 9999
        · exact Or.inr h9
        · left; exact hband r (by omega)) (hrr₂ _)
    have hA₂ : c.nreg ALLOC ≤ c₂.nreg ALLOC := by rw [hAL, a9₂, hAl]
    exact (FA.trans FB hA₂).trans FC (by rw [hAL, hAl]; show A₀ ≤ A₁; omega)
  · rw [F₈.1 _ (by decide), a9₇, hMD]
  · rw [K58 _ (by decide) (by decide) (by decide) (by decide), F₄.1 _ (by decide),
      R12₃ _ (by omega) (by omega), s25]
  · rw [K58 _ (by decide) (by decide) (by decide) (by decide), F₄.1 _ (by decide),
      R12₃ _ (by omega) (by omega), s23]
  · rw [K58 _ (by decide) (by decide) (by decide) (by decide), F₄.1 _ (by decide),
      R12₃ _ (by omega) (by omega), s24]
  · rw [K58 _ (by decide) (by decide) (by decide) (by decide), F₄.1 _ (by decide),
      R12₃ _ (by omega) (by omega), s49]
  · rw [K58 _ (by decide) (by decide) (by decide) (by decide)]; exact z205
  · rw [K58 _ (by decide) (by decide) (by decide) (by decide), F₄.1 _ (by decide),
      R12₃ _ (by omega) (by omega), s26]
  · rw [hMD, F₈.2.2.1, F₇.2.2.1 _ (by omega), F₆.2.2.1 _ (by omega), m0₅]
  · intro i hi
    rw [hMD, F₈.2.2.1, F₇.2.2.1 _ (by omega), F₆.2.2.1 _ (by omega), mi₅ i hi, F₄.2.2.1,
      F₃.2.2.1 _ (by rw [hAL, a9₂]; omega), hm₂]
  · rw [F₈.1 _ (by decide), F₇.1 _ (by decide), tb₆, hMD]
  · rw [F₈.1 _ (by decide), F₇.1 _ (by decide), l₆]
  · intro j hj
    rw [F₈.1 _ (by decide), F₇.1 _ (by decide), tb₆, F₈.2.2.1, F₇.2.2.1 _ (by omega)]
    exact tab₆ j hj
  · rw [F₈.1 _ (by decide), pos₇, F₈.1 _ (by decide), F₇.1 _ (by decide), tb₆]
  · intro j hj
    rw [F₈.1 _ (by decide), pos₇, F₈.2.2.1]; exact pf₇ j hj
  · exact ⟨PL₈.n, PL₈.one, PL₈.zero, PL₈.rs, PL₈.rm, PL₈.twoM, by rw [F₈.1 _ (by decide), hSs],
      PL₈.six, PL₈.tEnd, q0, q1, q2, q3, q4⟩
  · intro q hq
    rw [hCH, M48 _ (by omega), F₄.2.2.1]; exact chlt q hq
  · intro q q' hq hq' e
    rw [hCH, M48 _ (by omega), M48 _ (by omega), F₄.2.2.1] at e
    exact chinj q q' hq hq' e
  · intro q q' hqq hq'
    rw [hCH, M48 _ (by omega), M48 _ (by omega), F₄.2.2.1]
    exact (hV _ _).1 (chsort q q' hqq hq')
end

end OracleR

end Chazelle.Core
