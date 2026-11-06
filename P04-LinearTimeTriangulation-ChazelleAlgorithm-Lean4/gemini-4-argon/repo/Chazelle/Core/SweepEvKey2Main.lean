module

public import Chazelle.Core.SweepEvKey2Fin

/-!
# The sweep (WP-D), stage 3: the next key (task K)

`keyProg`: the selection of the least candidate (`kqSel`); if there is one, the key and its flags
(`kqPre`), the skipping of the stops at the key (`skipS (skipS skip)`), the new label list
(`finLab`) and the log record (`writeLog`); otherwise `dF = 1`.

**`keyTask : KeyTask`** (cost `56000`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- The steps after the selection, when there is a candidate. -/
def keyMain : Stmt := .seq kqPre (.seq (skipS (skipS .skip)) (.seq finLab writeLog))

/-- **The next key.** -/
def keyProg : Stmt := .seq kqSel (.ifLtN K0 kqF keyMain (block [.constN dF 1]))

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-! ## Register sets -/

theorem selR_KR {r : ℕ} (h : SelR r) : KR r := by
  simp only [SelR, OffR, kqF, kqE, kqH, kqO, kqSE, kqSH, kqX, sw] at h
  simp only [KR, kE, kH, kN, kL, sP, dF, lC, sw]; omega

theorem preR_KR {r : ℕ} (h : PreR r) : KR r := by
  simp only [PreR, LblR, kE, kH, dF, kqB, kqA, kqO, kqN, kqL, sw] at h
  simp only [KR, kE, kH, kN, kL, sP, dF, lC, sw]; omega

theorem skR_KR {r : ℕ} (h : SkR r) : KR r := by
  simp only [SkR, KStR, LblR, sP, kqSE, kqSH, kqO, kqA, kqX, kqV, kqY, kqN, kqL, sw] at h
  simp only [KR, kE, kH, kN, kL, sP, dF, lC, sw]; omega

theorem lbl_KR {r : ℕ} (h : LblR kN kL r) : KR r := by
  simp only [LblR, kN, kL, sw] at h
  simp only [KR, kE, kH, kN, kL, sP, dF, lC, sw]; omega

theorem lbl_not {r : ℕ} (h : LblR kN kL r) :
    ¬ SelR r ∧ ¬ PreR r ∧ ¬ SkR r ∧ r ≠ kqX ∧ r ≠ kqY ∧ r ≠ lC ∧ 240000 ≤ r ∧ r < 250000 := by
  simp only [LblR, kN, kL, sw] at h
  simp only [SelR, OffR, PreR, SkR, KStR, LblR, kqF, kqE, kqH, kqO, kqSE, kqSH, kqX, kqV, kqY,
    kE, kH, dF, kqB, kqA, kqN, kqL, sP, lC, sw]
  omega

/-! ## The selection -/

theorem sel_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hH : CandHyp P J c) (hroom : c.nreg ALLOC + 22100 ≤ W) :
    IRS P W c₀ kqSel c 22061 (fun d => SelInv P J c d True True) := by
  unfold kqSel
  refine IRS.seq (K₁ := 8) (K₂ := 22053) (selB_irs (J := J) hI E.hK (by omega)) ?_
  rintro d hId - hA hS
  refine IRS.seq (K₁ := 11029) (K₂ := 11024) (selS_irs E.hK hH (E.ctxW' hId) (E.gw' hId)
    (kqGW_lt J) hId hS (by omega)) ?_
  rintro d' hId' - hA' hS'
  exact selW_irs E.hK hH (E.ctxW' hId') (E.gw' hId') (kqGW_lt J) hId' hS' (by omega)

/-! ## The next key -/

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 100000 in
/-- **The next key.** -/
theorem key_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH))
    (hw : c.nreg wX = 0 → PosW P J (c.nreg wE) (c.nreg wH))
    (hst : ∀ i, i < c.nreg sC → PosW P J (stopE c i) (stopH c i))
    (hsort : ∀ i i', i ≤ i' → i' < c.nreg sC →
      offK P J (stopE c i) (stopH c i) ≤ offK P J (stopE c i') (stopH c i'))
    (htwo : ∀ i, i + 2 < c.nreg sC →
      offK P J (stopE c i) (stopH c i) < offK P J (stopE c (i + 2)) (stopH c (i + 2)))
    (hsPC : c.nreg sP ≤ c.nreg sC) (hkN : c.nreg kN ≤ 4) (hbN : c.nreg bN ≤ 4)
    (hsB : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC) (haB : c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hlB : c₀.nreg ALLOC ≤ c.nreg lB) (hlC : c.nreg lB + 7 * (c.nreg lC + 1) ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 56000 ≤ W) :
    IRS P W c₀ keyProg c 56000 (KeyOut P J c) := by
  have hH : CandHyp P J c := ⟨hb, hw, hst, hsB⟩
  unfold keyProg
  refine (IRS.seq (K₁ := 22061) (K₂ := 33461) (sel_irs E hI hH (by omega)) ?_).mono (by norm_num)
    (fun _ h => h)
  rintro d₁ hI₁ hA₁ hA₁' ⟨frS, hF, hFiff, hFmin⟩
  have hK₁ := E.hK.fix hI₁
  have kS : ∀ r, ¬ SelR r → 240000 ≤ r ∧ r < 250000 → d₁.nreg r = c.nreg r :=
    fun r h1 h2 => frS.kkeep h1 h2
  have nS : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
      r = lB ∨ r = lC ∨ r = kN ∨ r = dF) → ¬ SelR r ∧ 240000 ≤ r ∧ r < 250000 := by
    intro r hr
    simp only [bF, bE, bH, bN, sP, sC, sB, aB, lB, lC, kN, dF, sw] at hr
    simp only [SelR, OffR, kqF, kqE, kqH, kqO, kqSE, kqSH, kqX, sw]
    omega
  have e1 : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
      r = lB ∨ r = lC ∨ r = kN ∨ r = dF) → d₁.nreg r = c.nreg r :=
    fun r hr => kS r (nS r hr).1 (nS r hr).2
  by_cases hc : d₁.nreg K0 < d₁.nreg kqF
  · -- a candidate exists
    have hF1 : d₁.nreg kqF = 1 := by rw [hK₁.1] at hc; omega
    have hcand := hFiff.1 hF1
    obtain ⟨hCK, hm1, hm2, hm3⟩ := hFmin hF1
    have hpk := candK_posW hH hCK
    refine IRS.mono (K := 33459 + 2) (IRS.ifT hc ?_) (by norm_num) (fun _ h => h)
    unfold keyMain
    refine IRS.seq (K₁ := 11030) (K₂ := 22429) (pre_irs E hI₁ hpk
      (by rwa [e1 bF (by simp), e1 bE (by simp), e1 bH (by simp)])
      (by rwa [e1 bF (by simp), e1 bE (by simp), e1 bH (by simp)]) (by omega)) ?_
    rintro d₀ hI₀ hA₀ hA₀' ⟨frP, eKE, eKH, eDF, eKA, hB1, hBiff, hBlab, hBlab0⟩
    have nP : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
        r = lB ∨ r = lC ∨ r = kN) → ¬ PreR r := by
      intro r hr
      simp only [bF, bE, bH, bN, sP, sC, sB, aB, lB, lC, kN, sw] at hr
      simp only [PreR, LblR, kE, kH, dF, kqB, kqA, kqO, kqN, kqL, sw]
      omega
    have e0 : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
        r = lB ∨ r = lC ∨ r = kN) → d₀.nreg r = c.nreg r := fun r hr =>
      (frP.kkeep (nP r hr) (nS r (by rcases hr with h|h|h|h|h|h|h|h|h|h|h <;> simp [h])).2).trans
        (e1 r (by rcases hr with h|h|h|h|h|h|h|h|h|h|h <;> simp [h]))
    have hN0 : d₀.nreg kqN ≤ 4 := by
      by_cases h : d₀.nreg kqB = 1
      · rwa [(hBlab h).1, e1 bN (by simp)]
      · rw [(hBlab0 h).2]; omega
    have hS : SkCtx P J c d₀ :=
      { hsP := e0 sP (by simp), hsC := e0 sC (by simp), hsB := e0 sB (by simp),
        haB := e0 aB (by simp), hA := frS.2.1.trans frP.2.1,
        hm := fun x hx => (frP.2.2 x (lt_of_lt_of_le hx frS.2.1)).trans (frS.2.2 x hx),
        hpk := by rwa [eKE, eKH],
        hmin := fun h => by rw [eKE, eKH]; exact hm2 trivial h,
        hps := hst, hsort := hsort, htwo := htwo, hsBA := hsB, haBA := haB }
    refine IRS.seq (K₁ := 22400) (K₂ := 29) (skip2_irs E hS hI₀ (skInv_zero hS hsPC hN0 eKA)
      (by omega)) ?_
    rintro d₅ hI₅ hA₅ hA₅' ⟨j, ⟨frK, hsP5, hjC, hj2, hoff, hN5, hlb5, hA5, hAiff5⟩, hnext⟩
    have nK : ∀ r, (r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = lB ∨ r = lC ∨ r = kN) →
        ¬ SkR r ∧ 240000 ≤ r ∧ r < 250000 := by
      intro r hr
      simp only [kE, kH, dF, kqB, lB, lC, kN, sw] at hr
      simp only [SkR, KStR, LblR, sP, kqSE, kqSH, kqO, kqA, kqX, kqV, kqY, kqN, kqL, sw]
      omega
    have e5 : ∀ r, (r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = lB ∨ r = lC ∨ r = kN) →
        d₅.nreg r = d₀.nreg r := fun r hr => frK.kkeep (nK r hr).1 (nK r hr).2
    have hB5 : d₅.nreg kqB ≤ 1 := by rwa [e5 kqB (by simp)]
    refine IRS.seq (K₁ := 9) (K₂ := 20) (fin_irs hI₅ E.hK hB5 hA5) ?_
    rintro d₆ hI₆ hA₆ hA₆' ⟨f1, f2, f3, f4⟩
    have e6 : ∀ r, ¬ LblR kN kL r → d₆.nreg r = d₅.nreg r := f1
    have eLB6 : d₆.nreg lB = c.nreg lB := by
      rw [e6 lB (by simp only [LblR, lB, kN, kL, sw]; omega), e5 lB (by simp), e0 lB (by simp)]
    have eLC6 : d₆.nreg lC = c.nreg lC := by
      rw [e6 lC (by simp only [LblR, lC, kN, kL, sw]; omega), e5 lC (by simp), e0 lC (by simp)]
    have hc'A : c.nreg ALLOC ≤ d₆.nreg ALLOC := by
      rw [e6 ALLOC (by simp only [LblR, ALLOC, kN, kL, sw]; omega)]
      exact frS.2.1.trans (frP.2.1.trans frK.2.1)
    refine (writeLog_irs hI₆ E.hK (by rwa [eLB6]) (by rw [eLB6, eLC6]; omega)).mono
      le_rfl ?_
    rintro c' ⟨w1, w2, w3, w4, w5, w6, w7⟩
    rw [eLB6, eLC6] at w3 w4 w5 w6 w7
    -- registers of `c'`
    have g6 : ∀ r, r ≠ kqX → r ≠ kqY → r ≠ lC → ¬ LblR kN kL r → c'.nreg r = d₅.nreg r :=
      fun r h1 h2 h3 h4 => (w2 r h1 h2 h3).trans (e6 r h4)
    have nW : ∀ r, (r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = sP) →
        r ≠ kqX ∧ r ≠ kqY ∧ r ≠ lC ∧ ¬ LblR kN kL r := by
      intro r hr
      simp only [kE, kH, dF, kqB, sP, sw] at hr
      simp only [LblR, kqX, kqY, lC, kN, kL, sw]
      omega
    have g : ∀ r, (r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = sP) → c'.nreg r = d₅.nreg r :=
      fun r hr => g6 r (nW r hr).1 (nW r hr).2.1 (nW r hr).2.2.1 (nW r hr).2.2.2
    have cKE : c'.nreg kE = d₀.nreg kE := (g kE (by simp)).trans (e5 kE (by simp))
    have cKH : c'.nreg kH = d₀.nreg kH := (g kH (by simp)).trans (e5 kH (by simp))
    have cDF : c'.nreg dF = 0 := ((g dF (by simp)).trans (e5 dF (by simp))).trans eDF
    have cSP : c'.nreg sP = c.nreg sP + j := (g sP (by simp)).trans hsP5
    have cKB : d₅.nreg kqB = d₀.nreg kqB := e5 kqB (by simp)
    have ok : offK P J (c'.nreg kE) (c'.nreg kH) = offK P J (d₁.nreg kqE) (d₁.nreg kqH) := by
      rw [cKE, cKH, eKE, eKH]
    have lblC : ∀ (d d' : Config) (X : ℕ → Prop), EFr X d d' → (∀ r, LblR bN bL r → ¬ X r) →
        lblOf d' bN bL = lblOf d bN bL := fun d d' X h hX => kqLblOf_eq fun q hq =>
      h.kkeep (hX q hq) (by simp only [LblR, bN, bL, sw] at hq ⊢; omega)
    -- the label condition
    have hCb : (d₅.nreg kqB = 1) ↔ (c.nreg bF = 1 ∧
        offK P J (c.nreg bE) (c.nreg bH) = offK P J (c'.nreg kE) (c'.nreg kH)) := by
      rw [cKB, hBiff, ok, e1 bF (by simp), e1 bE (by simp), e1 bH (by simp)]
    have hCa : (d₅.nreg kqA = 1) ↔ ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
        c.nmem (c.nreg aB + 5 * i) = 1 := by rwa [cSP]
    have lab0 : lblOf d₀ kqN kqL = if c.nreg bF = 1 ∧
        offK P J (c.nreg bE) (c.nreg bH) = offK P J (c'.nreg kE) (c'.nreg kH)
        then lblOf c bN bL else [] := by
      split_ifs with h
      · rw [(hBlab (cKB ▸ hCb.2 h)).2, lblC c d₁ SelR frS (fun r hr => by
          simp only [LblR, bN, bL, sw] at hr
          simp only [SelR, OffR, kqF, kqE, kqH, kqO, kqSE, kqSH, kqX, sw]; omega)]
      · exact (hBlab0 (fun h' => h (hCb.1 (cKB ▸ h')))).1
    have nKR : ∀ r, ¬ KR r → r ≠ kqX ∧ r ≠ kqY ∧ r ≠ lC ∧ ¬ LblR kN kL r ∧ ¬ SkR r ∧
        ¬ PreR r ∧ ¬ SelR r := by
      intro r hr
      refine ⟨fun h => hr ?_, fun h => hr ?_, fun h => hr ?_, fun h => hr (lbl_KR h),
        fun h => hr (skR_KR h), fun h => hr (preR_KR h), fun h => hr (selR_KR h)⟩ <;>
        subst h <;> simp only [KR, kqX, kqY, lC, kE, kH, kN, kL, sP, dF, sw] <;> norm_num
    refine ⟨fun r hb hr hra => ?_, ?_, fun h => by
      rcases hcand with h1 | ⟨-, h1⟩ | ⟨-, h1⟩
      · exact absurd h1 h.1
      · exact absurd h1 h.2.1
      · exact absurd h1 h.2.2, fun _ => ?_⟩
    · obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := nKR r hr
      rw [g6 r n1 n2 n3 n4, frK.1 r hb n5 hra, frP.1 r hb n6 hra, frS.1 r hb n7 hra]
    · rwa [w2 ALLOC (by kqr) (by kqr) (by kqr)]
    -- the candidate case
    have hlbK : ∀ r, LblR kN kL r → d₅.nreg r = c.nreg r := fun r hr => by
      obtain ⟨n1, n2, n3, -, -, -, n7, n8⟩ := lbl_not hr
      rw [frK.kkeep n3 ⟨n7, n8⟩, frP.kkeep n2 ⟨n7, n8⟩, frS.kkeep n1 ⟨n7, n8⟩]
    have hlbC : ∀ r, LblR kN kL r → c'.nreg r = d₆.nreg r := fun r hr => by
      obtain ⟨-, -, -, n4, n5, n6, -⟩ := lbl_not hr
      exact w2 r n4 n5 n6
    have hmemC : ∀ x, x < c.nreg ALLOC → d₆.nmem x = c.nmem x := fun x hx => by
      rw [f2, frK.2.2 x (lt_of_lt_of_le hx (frS.2.1.trans frP.2.1)),
        frP.2.2 x (lt_of_lt_of_le hx frS.2.1), frS.2.2 x hx]
    have hkN' : c'.nreg kN ≤ 4 := by
      rw [hlbC kN (Or.inl rfl)]
      by_cases hC : d₅.nreg kqB = 1 ∨ d₅.nreg kqA = 1
      · rwa [(f3 hC).2]
      · rwa [f4 hC kN, hlbK kN (Or.inl rfl)]
    refine ⟨cDF, by rwa [cKE, cKH, eKE, eKH], fun h => by rw [ok]; exact hm1 h,
      fun h => by rw [ok]; exact hm2 trivial h, fun h => by rw [ok]; exact hm3 trivial h,
      by rw [cSP]; omega, by rwa [cSP], fun i h1 h2 => ?_, fun h => ?_, hkN',
      fun hC => ?_, fun hC => ?_, by rw [w1, eLC6], ?_, ?_, ?_, ?_, ?_⟩
    · rw [cSP] at h2; rw [hoff i h1 h2, cKE, cKH]
    · rw [g sP (by simp)] at h ⊢; rw [cKE, cKH]; exact hnext h
    · have hC' : d₅.nreg kqB = 1 ∨ d₅.nreg kqA = 1 := by
        rcases hC with h | h
        · exact Or.inl (hCb.2 h)
        · exact Or.inr (hCa.2 h)
      rw [kqLblOf_eq hlbC, (f3 hC').1, hlb5, lab0, cSP, Nat.add_sub_cancel_left]
    · have hC' : ¬ (d₅.nreg kqB = 1 ∨ d₅.nreg kqA = 1) := by
        rintro (h | h)
        · exact hC (Or.inl (hCb.1 h))
        · exact hC (Or.inr (hCa.1 h))
      refine ⟨?_, ?_⟩
      · rw [kqLblOf_eq hlbC, kqLblOf_eq (fun r _ => f4 hC' r), kqLblOf_eq hlbK]
      · rw [hlbC kN (Or.inl rfl), f4 hC' kN, hlbK kN (Or.inl rfl)]
    · rw [w3, w2 kE (by kqr) (by kqr) (by kqr)]
    · rw [w4, w2 kH (by kqr) (by kqr) (by kqr)]
    · rw [w5, w2 kN (by kqr) (by kqr) (by kqr)]
    · intro i hi
      rw [w6 i hi, w2 (kL + i) (by unfold kL kqX sw; omega) (by unfold kL kqY sw; omega)
        (by unfold kL lC sw; omega)]
    · intro x hx hx'
      rw [w7 x hx', hmemC x hx]
  · -- no candidate
    have hF0 : d₁.nreg kqF ≠ 1 := by rw [hK₁.1] at hc; omega
    refine IRS.mono (K := 1 + 2) (IRS.ifF hc (IRS.block [.constN dF 1] hI₁
      ⟨⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩, trivial⟩)) (by norm_num) ?_
    rintro c' hc'
    have v1 : c'.nreg dF = 1 := by rw [hc']; simp [regB, regI]
    have v2 : ∀ r, r ≠ dF → c'.nreg r = d₁.nreg r := fun r hr => by
      rw [hc']; simp [regB, regI, upd, hr]
    have vm : c'.nmem = d₁.nmem := by rw [hc']
    refine ⟨fun r hb hr hra => ?_, by rw [v2 ALLOC (by kqr)]; exact frS.2.1,
      fun _ => ⟨v1, by rw [v2 lC (by kqr)]; exact e1 lC (by simp),
        fun x hx => by rw [vm]; exact frS.2.2 x hx⟩, fun h => absurd (hFiff.2 (by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨trivial, h⟩)
        · exact Or.inr (Or.inr ⟨trivial, h⟩))) hF0⟩
    rw [v2 r (fun h => hr (by subst h; simp [KR]))]
    exact frS.1 r hb (fun h => hr (selR_KR h)) hra

/-- **Task K: the next key.** -/
theorem keyTask : KeyTask :=
  ⟨keyProg, 56000, fun _ _ _ _ _ _ _ _ _ _ _ _ E hI _ hb hw hst hsort htwo hsPC hkN hbN hsB haB hlB hlC
    hroom => key_irs E hI hb hw hst hsort htwo hsPC hkN hbN hsB haB hlB hlC hroom⟩

end

end SweepEv

end Chazelle.Core
