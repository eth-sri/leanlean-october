module

public import Chazelle.Core.SweepEvLab
public import Chazelle.Core.SweepEvSpec
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-!
# The sweep (WP-D), stage 3: the offer of a candidate to the minimum (RAM)

`offerC`: the candidate position `(cME, eA + 2)` of the walk of `C` is compared (offsets from
`gW`) with the current key `(kE, kH)`; if it is beyond the key it is offered to the best
candidate `(bF; bE, bH)` with the labels `oUp, oDn` (label list `bN, bL`): a smaller candidate
replaces it, an equal one adds its labels.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

def kE : ℕ := sw 2400
def kH : ℕ := sw 2401
def bF : ℕ := sw 2410
def bE : ℕ := sw 2411
def bH : ℕ := sw 2412
def bN : ℕ := sw 2413
def bL : ℕ := sw 2414
def cO : ℕ := sw 2280
def cO2 : ℕ := sw 2282
def cGW : ℕ := sw 659

/-- The offset (from `gW`) of a position of the walk of `C`. -/
noncomputable def offK (P : Polygon) (J : Merge.Junction) (e h : ℕ) : ℝ :=
  off (chainModel J.whole).W.n (gW J : ℝ) ((chainModel J.whole).key (Qof P) ⟨e, h⟩)

/-- Take the candidate. -/
def takeL : List Instr :=
  [.constN bF 1, .copyN bE cME, .copyN bH (eA + 2), .constN bN 2, .copyN bL oUp, .copyN (bL + 1) oDn]

/-- Compare with the best candidate. -/
def offCmp' : Stmt :=
  .seq (callOff (sw 2) cME (eA + 2) bE bH cGW cO2)
    (.ifLtN K0 cO2 (block takeL) (.ifLtN K0 (cO2 + 1) .skip
      (.seq (addLab bN bL oUp) (addLab bN bL oDn))))

/-- **The offer of a candidate.** -/
def offerC : Stmt :=
  .seq (callOff (sw 2) cME (eA + 2) kE kH cGW cO)
    (.ifLtN K0 (cO + 1) (.ifLtN K0 bF offCmp' (block takeL)) .skip)

/-- The registers of the best candidate. -/
def BestR (q : ℕ) : Prop := q = bF ∨ q = bE ∨ q = bH ∨ LblR bN bL q

/-- The best-candidate state is unchanged. -/
def BestSame (c c' : Config) : Prop :=
  c'.nreg bF = c.nreg bF ∧ c'.nreg bE = c.nreg bE ∧ c'.nreg bH = c.nreg bH ∧
    lblOf c' bN bL = lblOf c bN bL ∧ c'.nreg bN = c.nreg bN

/-- **The outputs of the offer.** -/
def OfferOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  c'.nreg bF ≤ 1 ∧ c'.nreg bN ≤ 4 ∧
  (¬ offK P J (c.nreg kE) (c.nreg kH) < offK P J (c.nreg cME) (c.nreg (eA + 2)) → BestSame c c') ∧
  (offK P J (c.nreg kE) (c.nreg kH) < offK P J (c.nreg cME) (c.nreg (eA + 2)) →
    (c.nreg bF ≠ 1 ∨ offK P J (c.nreg cME) (c.nreg (eA + 2)) < offK P J (c.nreg bE) (c.nreg bH)) →
    c'.nreg bF = 1 ∧ c'.nreg bE = c.nreg cME ∧ c'.nreg bH = c.nreg (eA + 2) ∧
    lblOf c' bN bL = [c.nreg oUp, c.nreg oDn] ∧ c'.nreg bN = 2) ∧
  (offK P J (c.nreg kE) (c.nreg kH) < offK P J (c.nreg cME) (c.nreg (eA + 2)) → c.nreg bF = 1 →
    offK P J (c.nreg cME) (c.nreg (eA + 2)) = offK P J (c.nreg bE) (c.nreg bH) →
    c'.nreg bF = 1 ∧ c'.nreg bE = c.nreg bE ∧ c'.nreg bH = c.nreg bH ∧
    lblOf c' bN bL = addL (addL (lblOf c bN bL) (c.nreg oUp)) (c.nreg oDn)) ∧
  (offK P J (c.nreg kE) (c.nreg kH) < offK P J (c.nreg cME) (c.nreg (eA + 2)) → c.nreg bF = 1 →
    offK P J (c.nreg bE) (c.nreg bH) < offK P J (c.nreg cME) (c.nreg (eA + 2)) → BestSame c c') ∧
  EFr (fun q => BestR q ∨ (cO ≤ q ∧ q ≤ cO2 + 1)) c c'

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem takeL_val (m f : ℕ → ℕ) :
    regB m takeL f bF = 1 ∧ regB m takeL f bE = f cME ∧ regB m takeL f bH = f (eA + 2) ∧
    regB m takeL f bN = 2 ∧ regB m takeL f bL = f oUp ∧ regB m takeL f (bL + 1) = f oDn ∧
    (∀ q, ¬ BestR q → regB m takeL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => regB_other _ _ _ (fun i hi => ?_)⟩
  · sis only [takeL, regB, regI, upd, bF, bE, bH, bN, bL, cME, eA, oUp, oDn, sw]
  · sis only [takeL, regB, regI, upd, bF, bE, bH, bN, bL, cME, eA, oUp, oDn, sw]
  · sis only [takeL, regB, regI, upd, bF, bE, bH, bN, bL, cME, eA, oUp, oDn, sw]
  · sis only [takeL, regB, regI, upd, bF, bE, bH, bN, bL, cME, eA, oUp, oDn, sw]
  · sis only [takeL, regB, regI, upd, bF, bE, bH, bN, bL, cME, eA, oUp, oDn, sw]
  · sis only [takeL, regB, regI, upd, bF, bE, bH, bN, bL, cME, eA, oUp, oDn, sw]
  · simp only [takeL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> intro h <;> apply hq
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

theorem lblOf_take {c c' : Config} (h1 : c'.nreg bN = 2) (h2 : c'.nreg bL = c.nreg oUp)
    (h3 : c'.nreg (bL + 1) = c.nreg oDn) : lblOf c' bN bL = [c.nreg oUp, c.nreg oDn] := by
  unfold lblOf; rw [h1]; simp [List.range_succ, h2, h3]

theorem lblOf_congr {c c' : Config} (h : ∀ q, LblR bN bL q → c'.nreg q = c.nreg q) :
    lblOf c' bN bL = lblOf c bN bL := by
  unfold lblOf
  rw [h bN (Or.inl rfl)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact h _ (Or.inr ⟨by omega, by omega⟩)

theorem bestR_reg {q : ℕ} (h : BestR q ∨ (cO ≤ q ∧ q ≤ cO2 + 1)) : sw 2280 ≤ q ∧ q ≤ sw 2417 := by
  unfold BestR LblR bF bE bH bN bL cO cO2 sw at h
  ufo sw

/-- **The offer of a candidate.** -/
theorem offerC_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hctx : ChainCtx P W c (sw 2) J.whole) (hgw : c.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n)
    (hc : PosW P J (c.nreg cME) (c.nreg (eA + 2))) (hk : PosW P J (c.nreg kE) (c.nreg kH))
    (hb : c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH)) (hbF : c.nreg bF ≤ 1)
    (hbN : c.nreg bN ≤ 4) (hroom : c.nreg ALLOC + 22200 ≤ W) :
    IRS P W c₀ offerC c 22200 (OfferOut P J c) := by
  have hK := hK₀.fix hI
  obtain ⟨k0, k1, -, -, -, -, -⟩ := hK
  have hW4 : 4 ≤ W := by have := hctx.2.2.2.2.2; omega
  set oc := offK P J (c.nreg cME) (c.nreg (eA + 2)) with hoc
  set ok := offK P J (c.nreg kE) (c.nreg kH) with hok
  set ob := offK P J (c.nreg bE) (c.nreg bH) with hob
  have hgw' : ((c.nreg cGW : ℕ) : ℝ) = (gW J : ℝ) := by rw [hgw]
  -- 1. candidate against the key
  refine IRS.seq (K₁ := 11008) (K₂ := 11192) (callOff_irs (dsc := sw 2) (ex := cME) (hx := eA + 2)
    (ey := kE) (hy := kH) (g := cGW) (o := cO) hI hctx
    ⟨by norm_num [sw], by norm_num [sw], by ufn cME sw, by ufn cME sw,
      by ufn eA sw, by ufn eA sw, by ufn kE sw,
      by ufn kE sw, by ufn kH sw, by ufn kH sw,
      by ufn cGW sw, by ufn cGW sw⟩
    ⟨by ufn cO sw, by ufn cO sw⟩ hc.1 hk.1 (by rwx [hgw])
    hc.2.1 hk.2.1 hc.2.2 hk.2.2 (by omega)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨b1, b2, k₁, ha₁, hm₁⟩
  rw [hgw'] at b1 b2
  change BitIs c₁ cO (oc < ok) at b1
  change BitIs c₁ (cO + 1) (ok < oc) at b2
  have kk₁ : ∀ r, ¬ (cO ≤ r ∧ r ≤ cO2 + 1) → bandOf r ∉ oracleBands → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 => k₁ r h2 (fun h => h1 ⟨by omega, by
        ufo cO cO2 sw at *⟩) (fun h => h1 ⟨by omega, by ufo cO cO2 sw at *⟩) h3
  have ksw₁ : ∀ r, 240000 ≤ r → r < 250000 → ¬ (cO ≤ r ∧ r ≤ cO2 + 1) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => kk₁ r h3 (not_oracle_sw h1 h2) (by ufo ALLOC)
  have k01  := (hK₀.fix hI₁).1
  have fr1 : EFr (fun q => BestR q ∨ (cO ≤ q ∧ q ≤ cO2 + 1)) c c₁ :=
    ⟨fun r hr hX hra => kk₁ r (fun h => hX (Or.inr h)) hr hra, ha₁, hm₁⟩
  have same1 : ∀ r, BestR r → c₁.nreg r = c.nreg r := fun r hr => ksw₁ r
    (by have := bestR_reg (Or.inl hr); ufo sw at this)
    (by have := bestR_reg (Or.inl hr); ufo sw at this)
    (by ufo BestR LblR bF bE bH bN bL cO cO2 sw at *)
  have bs1 : BestSame c c₁ := ⟨same1 _ (Or.inl rfl), same1 _ (Or.inr (Or.inl rfl)),
    same1 _ (Or.inr (Or.inr (Or.inl rfl))), lblOf_congr (fun q hq => same1 q (Or.inr (Or.inr (Or.inr hq)))),
    same1 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  -- the take block from a configuration `c₂` agreeing with `c` outside the scratch
  have takeIRS : ∀ c₂ : Config, IInv W c₀ c₂ → EFr (fun q => BestR q ∨ (cO ≤ q ∧ q ≤ cO2 + 1)) c c₂ →
      (∀ r, r = cME ∨ r = eA + 2 ∨ r = oUp ∨ r = oDn → c₂.nreg r = c.nreg r) →
      ok < oc → (c.nreg bF ≠ 1 ∨ oc < ob) →
      IRS P W c₀ (block takeL) c₂ 6 (OfferOut P J c) := by
    intro c₂ hI₂ fr2 hr2 hlt0 hcase
    have hok : okB W c₂.nmem takeL c₂.nreg := by
      simp only [takeL, okB, okI]
      exact ⟨⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩, iscr_sw' (by norm_num) (by norm_num),
        iscr_sw' (by norm_num) (by norm_num), ⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩,
        iscr_sw' (by norm_num) (by norm_num), iscr_sw (by ufn bL sw)
          (by ufn bL sw), trivial⟩
    refine (IRS.block takeL hI₂ hok).mono le_rfl ?_
    rintro c' hc'
    obtain ⟨t1, t2, t3, t4, t5, t6, tO⟩ := takeL_val c₂.nmem c₂.nreg
    have e1 : c'.nreg bF = 1 := by rwx [hc']
    have e2 : c'.nreg bE = c.nreg cME := by rw [hc']; exact t2.trans (hr2 _ (Or.inl rfl))
    have e3 : c'.nreg bH = c.nreg (eA + 2) := by rw [hc']; exact t3.trans (hr2 _ (Or.inr (Or.inl rfl)))
    have e4 : c'.nreg bN = 2 := by rwx [hc']
    have e5 : c'.nreg bL = c.nreg oUp := by rw [hc']; exact t5.trans (hr2 _ (Or.inr (Or.inr (Or.inl rfl))))
    have e6 : c'.nreg (bL + 1) = c.nreg oDn := by
      rw [hc']; exact t6.trans (hr2 _ (Or.inr (Or.inr (Or.inr rfl))))
    have hlb := lblOf_take e4 e5 e6
    refine ⟨by omega, by omega, fun h => absurd hlt0 h, fun _ _ => ⟨e1, e2, e3, hlb, e4⟩,
      fun h hb1 heq => ?_, fun h hb1 hlt => ?_, fr2.trans ⟨fun r hr hX hra => by
        rw [hc']; exact tO r (fun h => hX (Or.inl h)),
        by rw [hc']; exact (tO ALLOC (by ufo BestR LblR bF bE bH bN bL ALLOC sw)).ge,
        fun a _ => by rw [hc']⟩⟩
    · rcases hcase with h' | h'
      · exact absurd hb1 h'
      · exact absurd heq (ne_of_lt h')
    · rcases hcase with h' | h'
      · exact absurd hb1 h'
      · exact absurd hlt (not_lt.2 h'.le)
  have keepc₁ : ∀ r, r = cME ∨ r = eA + 2 ∨ r = oUp ∨ r = oDn → c₁.nreg r = c.nreg r := by
    rintro r (rfl | rfl | rfl | rfl)
    · exact ksw₁ _ (by ufn cME sw) (by ufn cME sw) (by ufo cME cO cO2 sw)
    · exact ksw₁ _ (by ufn eA sw) (by ufn eA sw) (by ufo eA cO cO2 sw)
    · exact ksw₁ _ (by ufn oUp sw) (by ufn oUp sw) (by ufo oUp cO cO2 sw)
    · exact ksw₁ _ (by ufn oDn sw) (by ufn oDn sw) (by ufo oDn cO cO2 sw)
  by_cases h2 : c₁.nreg K0 < c₁.nreg (cO + 1)
  · rw [k01] at h2
    have hlt : ok < oc := b2.2.1 (by have := b2.1; omega)
    refine IRS.mono (K := 11190 + 2) (IRS.ifT (by rwx [k01]) ?_) (by norm_num) (fun _ => id)
    have bF1  := bs1.1
    by_cases h3 : c₁.nreg K0 < c₁.nreg bF
    · rw [k01, bF1] at h3
      have hbF1 : c.nreg bF = 1 := by omega
      refine IRS.mono (K := 11188 + 2) (IRS.ifT (by rwx [k01, bF1]) ?_) le_rfl (fun _ => id)
      have hbP := hb hbF1
      have eBE  := bs1.2.1
      have eBH  := bs1.2.2.1
      have hctx₁  := hctx.transport
        (ksw₁ _ (by norm_num [sw]) (by norm_num [sw]) (by ufo cO sw)) hm₁ ha₁
      have egw : c₁.nreg cGW = gW J := (ksw₁ _ (by ufn cGW sw)
        (by ufn cGW sw) (by ufo cGW cO cO2 sw)).trans hgw
      have eME := keepc₁ _ (Or.inl rfl)
      have eE2 := keepc₁ _ (Or.inr (Or.inl rfl))
      refine IRS.seq (K₁ := 11008) (K₂ := 180) (callOff_irs (dsc := sw 2) (ex := cME) (hx := eA + 2)
        (ey := bE) (hy := bH) (g := cGW) (o := cO2) hI₁ hctx₁
        ⟨by norm_num [sw], by norm_num [sw], by ufn cME sw, by ufn cME sw,
          by ufn eA sw, by ufn eA sw, by ufn bE sw,
          by ufn bE sw, by ufn bH sw, by ufn bH sw,
          by ufn cGW sw, by ufn cGW sw⟩
        ⟨by ufn cO2 sw, by ufn cO2 sw⟩ (by rw [eME]; exact hc.1)
        (by rw [eBE]; exact hbP.1) (by rwx [egw]) (by rw [eME, eE2]; exact hc.2.1)
        (by rw [eBE, eBH]; exact hbP.2.1) (by rw [eME, eE2]; exact hc.2.2)
        (by rw [eBE, eBH]; exact hbP.2.2) (by omega)) ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨d1, d2, k₂, ha₂, hm₂⟩
      rw [egw, eME, eE2, eBE, eBH] at d1 d2
      change BitIs c₂ cO2 (oc < ob) at d1
      change BitIs c₂ (cO2 + 1) (ob < oc) at d2
      have kk₂ : ∀ r, 240000 ≤ r → r < 250000 → r ≠ cO2 → r ≠ cO2 + 1 → c₂.nreg r = c₁.nreg r :=
        fun r h1 h2 h3 h4 => k₂ r (not_oracle_sw h1 h2) h3 h4 (by ufo ALLOC)
      have fr2  := fr1.trans
        ⟨fun r hr hX hra => k₂ r hr (fun h => hX (Or.inr ⟨by ruo [h] cO cO2 sw,
          by rwo [h]⟩)) (fun h => hX (Or.inr ⟨by ruo [h] cO cO2 sw, by rw [h]⟩))
          hra, ha₂, hm₂⟩
      have keepc₂ : ∀ r, r = cME ∨ r = eA + 2 ∨ r = oUp ∨ r = oDn → c₂.nreg r = c.nreg r := by
        intro r hr
        rw [← keepc₁ r hr]
        rcases hr with rfl | rfl | rfl | rfl
        · exact kk₂ _ (by ufn cME sw) (by ufn cME sw) (by ufo cME cO2 sw)
            (by ufo cME cO2 sw)
        · exact kk₂ _ (by ufn eA sw) (by ufn eA sw) (by ufo eA cO2 sw)
            (by ufo eA cO2 sw)
        · exact kk₂ _ (by ufn oUp sw) (by ufn oUp sw) (by ufo oUp cO2 sw)
            (by ufo oUp cO2 sw)
        · exact kk₂ _ (by ufn oDn sw) (by ufn oDn sw) (by ufo oDn cO2 sw)
            (by ufo oDn cO2 sw)
      have same2 : ∀ r, BestR r → c₂.nreg r = c.nreg r := fun r hr => by
        rw [← same1 r hr]
        have := bestR_reg (Or.inl hr)
        exact kk₂ r (by ufo sw at this) (by ufo sw at this)
          (by ufo BestR LblR bF bE bH bN bL cO2 sw at *)
          (by ufo BestR LblR bF bE bH bN bL cO2 sw at *)
      have bs2 : BestSame c c₂ := ⟨same2 _ (Or.inl rfl), same2 _ (Or.inr (Or.inl rfl)),
        same2 _ (Or.inr (Or.inr (Or.inl rfl))),
        lblOf_congr (fun q hq => same2 q (Or.inr (Or.inr (Or.inr hq)))),
        same2 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
      have k02  := (hK₀.fix hI₂).1
      by_cases h4 : c₂.nreg K0 < c₂.nreg cO2
      · rw [k02] at h4
        have hlt2 : oc < ob := d1.2.1 (by have := d1.1; omega)
        exact (IRS.ifT (by rwx [k02]) (takeIRS c₂ hI₂ fr2 keepc₂ hlt (Or.inr hlt2))).mono
          (by norm_num) (fun _ => id)
      · rw [k02] at h4
        have hnlt2 : ¬ oc < ob := fun h => by have := d1.2.2 h; omega
        refine IRS.mono (K := 176 + 2) (IRS.ifF (by rwx [k02]) ?_) (by norm_num) (fun _ => id)
        by_cases h5 : c₂.nreg K0 < c₂.nreg (cO2 + 1)
        · rw [k02] at h5
          have hlt3 : ob < oc := d2.2.1 (by have := d2.1; omega)
          refine IRS.mono (K := 0 + 2) (IRS.ifT (by rwx [k02]) (IRS.skip hI₂ rfl)) (by norm_num) ?_
          rintro c' rfl
          exact ⟨by rwx [bs2.1], by rwx [bs2.2.2.2.2], fun h => absurd hlt h,
            fun _ h => by rcases h with h | h; exact absurd hbF1 h; exact absurd hlt3 (not_lt.2 h.le),
            fun _ _ heq => absurd heq (ne_of_gt hlt3), fun _ _ _ => bs2, fr2⟩
        · rw [k02] at h5
          have heq : oc = ob := by
            have : ¬ ob < oc := fun h => by have := d2.2.2 h; omega
            linarith [not_lt.1 this, not_lt.1 hnlt2]
          refine IRS.mono (K := 60 + 2) (IRS.ifF (by rwx [k02]) ?_) (by norm_num) (fun _ => id)
          have hsN : IScr bN := iscr_sw' (by norm_num) (by norm_num)
          have hsL : ∀ i, i < 4 → IScr (bL + i) := fun i hi =>
            iscr_sw (by ufo bL sw) (by ufo bL sw)
          have hNL : ∀ i, i < 4 → bN ≠ bL + i := fun i hi => by ufo bN bL sw
          have hKN : ∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ¬ LblR bN bL k := by
            rintro k (rfl | rfl | rfl | rfl) <;> simp only [LblR, bN, bL, K1, K2, K3, K4, sw] <;> omega
          have hN2 : c₂.nreg bN ≤ 4 := by rwx [bs2.2.2.2.2]
          refine IRS.seq (K₁ := 30) (K₂ := 30) (addLab_irs (r := oUp) hI₂ (hK₀.fix hI₂) hsN hsL hNL
            (by ufo oUp bN sw) (fun i hi => by ufo oUp bL sw) hKN hN2 hW4) ?_
          rintro c₃ hI₃ hA₃ hA₃' ⟨g1, g2, g3, g4⟩
          refine (addLab_irs (r := oDn) hI₃ (hK₀.fix hI₃) hsN hsL hNL
            (by ufo oDn bN sw) (fun i hi => by ufo oDn bL sw) hKN g1 hW4).mono
            le_rfl ?_
          rintro c' ⟨f1, f2, f3, f4⟩
          have nLF : ¬ LblR bN bL bF := by ufo LblR bN bL bF sw
          have nLE : ¬ LblR bN bL bE := by ufo LblR bN bL bE sw
          have nLH : ¬ LblR bN bL bH := by ufo LblR bN bL bH sw
          have eUp : c₂.nreg oUp = c.nreg oUp := keepc₂ _ (Or.inr (Or.inr (Or.inl rfl)))
          have eDn : c₃.nreg oDn = c.nreg oDn := by
            rw [g3 _ (by ufo LblR bN bL oDn sw)]; exact keepc₂ _ (Or.inr (Or.inr (Or.inr rfl)))
          have e1 : c'.nreg bF = c.nreg bF := by rw [f3 _ nLF, g3 _ nLF]; exact bs2.1
          refine ⟨by rwx [e1], f1, fun h => absurd hlt h,
            fun _ h => by rcases h with h | h; exact absurd hbF1 h; exact absurd h hnlt2,
            fun _ _ _ => ⟨by rw [e1, hbF1], by rw [f3 _ nLE, g3 _ nLE]; exact bs2.2.1,
              by rw [f3 _ nLH, g3 _ nLH]; exact bs2.2.2.1, by rw [f2, g2, eDn, eUp, bs2.2.2.2.1]⟩,
            fun _ _ h => absurd heq (ne_of_gt h), fr2.trans (EFr.trans
              ⟨fun r hr hX hra => g3 r (fun h => hX (Or.inl (Or.inr (Or.inr (Or.inr h))))), hA₃, ?_⟩
              ⟨fun r hr hX hra => f3 r (fun h => hX (Or.inl (Or.inr (Or.inr (Or.inr h))))), ?_, ?_⟩)⟩
          · intro a _; rw [g4]
          · exact (f3 ALLOC (by ufo LblR bN bL ALLOC sw)).ge
          · intro a _; rw [f4]
    · rw [k01, bF1] at h3
      refine IRS.mono (K := 6 + 2) (IRS.ifF (by rwx [k01, bF1])
        (takeIRS c₁ hI₁ fr1 keepc₁ hlt (Or.inl (by omega)))) (by norm_num) (fun _ => id)
  · rw [k01] at h2
    have hnlt : ¬ ok < oc := fun h => by have := b2.2.2 h; omega
    refine IRS.mono (K := 0 + 2) (IRS.ifF (by rwx [k01]) (IRS.skip hI₁ rfl)) (by norm_num) ?_
    rintro c' rfl
    exact ⟨by rwx [bs1.1], by rwx [bs1.2.2.2.2], fun _ => bs1,
      fun h => absurd h hnlt, fun h => absurd h hnlt, fun h => absurd h hnlt, fr1⟩

end

end SweepEv

end Chazelle.Core
