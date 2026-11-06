module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvKey2

/-!
# The sweep (WP-D), stage 3: the next key (task K), the selection of the least candidate

`kqSel`: the running minimum `(kqF; kqE, kqH)` of the three candidates — the best candidate
`(bE, bH)` (if `bF = 1`), the stop `sP` (if `sP < sC`) and the window end `(wE, wH)` (if
`wX = 0`).  `sel_irs`: `SelInv … True True` (the flag says whether a candidate exists; the
minimum is a candidate of least offset).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- Register arithmetic of the next-key step. -/
macro "kqr" : tactic => `(tactic| ((try simp only [kqF, kqE, kqH, kqSE, kqSH, kqO, kqB, kqA, kqN, kqL,
  kqX, kqV, kqY, kE, kH, kN, kL, bF, bE, bH, bN, bL, sP, sC, sB, aB, dF, lB, lC, wX, wE, wH, cGW,
  K0, K1, K2, K3, K4, ALLOC, OffR, LblR, KR, sw, ne_eq, not_or]) <;> omega))

/-! ## The program -/

/-- The best candidate. -/
def kqSelB : Stmt :=
  .seq (block [.constN kqF 0]) (kqIsOne bF (block [.constN kqF 1, .copyN kqE bE, .copyN kqH bH]))

/-- The next stop. -/
def selS : Stmt := .ifLtN sP sC (.seq (block ldStopL) offerQ) .skip

/-- The window end. -/
def selW : Stmt := .ifLtN K0 wX .skip (.seq (block [.copyN kqSE wE, .copyN kqSH wH]) offerQ)

/-- **The selection of the least candidate.** -/
def kqSel : Stmt := .seq kqSelB (.seq selS selW)

/-- The registers the selection writes. -/
def SelR (r : ℕ) : Prop := OffR r ∨ r = kqSE ∨ r = kqSH ∨ r = kqX

/-- A candidate position. -/
def CandK (_P : Polygon) (_J : Merge.Junction) (c : Config) (e h : ℕ) : Prop :=
  (c.nreg bF = 1 ∧ e = c.nreg bE ∧ h = c.nreg bH) ∨
  (c.nreg sP < c.nreg sC ∧ e = stopE c (c.nreg sP) ∧ h = stopH c (c.nreg sP)) ∨
  (c.nreg wX = 0 ∧ e = c.nreg wE ∧ h = c.nreg wH)

section
variable (P : Polygon) (J : Merge.Junction)
include P J
/-- **The invariant of the selection** (stops considered iff `ps`, window end iff `pw`). -/
def SelInv (c d : Config) (ps pw : Prop) : Prop :=
  EFr SelR c d ∧ d.nreg kqF ≤ 1 ∧
  (d.nreg kqF = 1 ↔ (c.nreg bF = 1 ∨ (ps ∧ c.nreg sP < c.nreg sC) ∨ (pw ∧ c.nreg wX = 0))) ∧
  (d.nreg kqF = 1 → CandK P J c (d.nreg kqE) (d.nreg kqH) ∧
    (c.nreg bF = 1 →
      offK P J (d.nreg kqE) (d.nreg kqH) ≤ offK P J (c.nreg bE) (c.nreg bH)) ∧
    (ps → c.nreg sP < c.nreg sC → offK P J (d.nreg kqE) (d.nreg kqH) ≤
      offK P J (stopE c (c.nreg sP)) (stopH c (c.nreg sP))) ∧
    (pw → c.nreg wX = 0 →
      offK P J (d.nreg kqE) (d.nreg kqH) ≤ offK P J (c.nreg wE) (c.nreg wH)))

/-- The hypotheses on the candidates. -/
def CandHyp (c : Config) : Prop :=
  (c.nreg bF = 1 → PosW P J (c.nreg bE) (c.nreg bH)) ∧
  (c.nreg wX = 0 → PosW P J (c.nreg wE) (c.nreg wH)) ∧
  (∀ i, i < c.nreg sC → PosW P J (stopE c i) (stopH c i)) ∧
  c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC


end

variable {P : Polygon} {W : ℕ} {c₀ c d : Config} {J : Merge.Junction}

theorem candK_posW {e h : ℕ} (hH : CandHyp P J c) (hc : CandK P J c e h) : PosW P J e h := by
  rcases hc with ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩
  · ram_grind
  · ram_grind
  · ram_grind

section
variable {X : ℕ → Prop}
theorem EFr.kkeep {c d : Config} (h : EFr X c d) {r : ℕ} (hr : ¬ X r)
    (h1 : 240000 ≤ r ∧ r < 250000) : d.nreg r = c.nreg r :=
  h.1 r (not_oracle_sw h1.1 h1.2) hr (by omega_nf)

/-- The frame of a block. -/
theorem kqEfr_block (l : List Instr) (hX : ∀ i ∈ l, X (dstI i)) (hA : ¬ X ALLOC) :
    EFr X c { c with nreg := regB c.nmem l c.nreg } :=
  ⟨fun r _ hr _ => regB_other _ _ _ (fun i hi h => hr (by grind)),
    (regB_other _ _ _ (fun i hi h => hA (by grind))).ge, fun _ _ => rfl⟩

/-- The stop records below the allocator are kept. -/
theorem kqStop_keep {c d : Config} (h : EFr X c d) (hsB : ¬ X sB)
    (hH : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC) {i : ℕ} (hi : i < c.nreg sC) :
    d.nmem (d.nreg sB + 5 * i) = stopE c i ∧ d.nmem (d.nreg sB + 5 * i + 1) = stopH c i := by
  rw [h.kkeep hsB (by omega_nf)]
  ram_grind

/-! ## The steps -/


end

set_option maxHeartbeats 4000000 in
theorem selB_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hW : 1 ≤ W) :
    IRS P W c₀ kqSelB c 8 (fun d => SelInv P J c d False False) := by
  unfold kqSelB
  refine IRS.seq (K₁ := 1) (K₂ := 7) (IRS.block [.constN kqF 0] hI
    ⟨⟨iscr_sw' (by norm_num) (by norm_num), by omega⟩, trivial⟩) ?_
  rintro c₁ hI₁ - - hc₁
  have fr1 : EFr SelR c c₁ := by
    rw [hc₁]; exact kqEfr_block _ (by simp [dstI, SelR, OffR]) (by omega_nf)
  have e0 : c₁.nreg kqF = 0 := by simp_all [regB, regI] 
  have eF : c₁.nreg bF = c.nreg bF := fr1.kkeep (by omega_nf) (by kqr)
  have eE : c₁.nreg bE = c.nreg bE := fr1.kkeep (by omega_nf) (by kqr)
  have eH : c₁.nreg bH = c.nreg bH := fr1.kkeep (by omega_nf) (by kqr)
  have hK₁ : Consts c₁ := hK₀.fix hI₁
  refine kqIsOne_irs (K := 3) hI₁ hK₁ (fun h1 => ?_) (fun h1 => ?_)
  · refine (IRS.block _ hI₁ (by
      simp only [okB, okI]
      ram_grind)).mono
      le_rfl ?_
    rintro d hd
    have fr2 : EFr SelR c₁ d := by
      rw [hd]; exact kqEfr_block _ (by simp [dstI, SelR, OffR]) (by omega_nf)
    have v1 : d.nreg kqF = 1 := by simp_all [regB, regI, upd, kqF, kqE, kqH, sw] 
    have v2 : d.nreg kqE = c₁.nreg bE := by simp_all [regB, regI, upd, kqF, kqE, kqH, bE, sw] 
    have v3 : d.nreg kqH = c₁.nreg bH := by
      simp_all [regB, regI, upd, kqF, kqE, kqH, bH, sw] 
    rw [eE] at v2; rw [eH] at v3; rw [eF] at h1
    refine ⟨fr1.trans fr2, by omega, ⟨fun _ => Or.inl h1, fun _ => v1⟩, fun _ => ⟨Or.inl ⟨h1, v2, v3⟩,
      fun _ => by rw [v2, v3], fun h => h.elim, fun h => h.elim⟩⟩
  core_grind

set_option maxHeartbeats 8000000 in
theorem selS_irs (hK₀ : Consts c₀) (hH : CandHyp P J c)
    (hctx : ChainCtx P W d (sw 2) J.whole) (hgw : d.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n) (hId : IInv W c₀ d)
    (hS : SelInv P J c d False False) (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ selS d 11029 (fun d' => SelInv P J c d' True False) := by
  obtain ⟨fr, hF, hiff, hmin⟩ := hS
  have eSP : d.nreg sP = c.nreg sP := fr.kkeep (by omega_nf) (by kqr)
  have eSC : d.nreg sC = c.nreg sC := fr.kkeep (by omega_nf) (by kqr)
  
  have eSB : d.nreg sB = c.nreg sB := fr.kkeep (by omega_nf) (by kqr)
  have hKd := hK₀.fix hId
  unfold selS
  by_cases hs : d.nreg sP < d.nreg sC
  · rw [eSP, eSC] at hs
    obtain ⟨l1, l2⟩ := kqStop_keep fr (by omega_nf) hH.2.2.2 hs
    refine IRS.mono (K := 11027 + 2) (IRS.ifT (by omega) ?_) le_rfl (fun _ h => h)
    refine IRS.seq (K₁ := 7) (K₂ := 11020) (ldStop_irs hId hKd.2.1 (by
      ram_grind)) ?_
    rintro d₁ hI₁ hA₁ hA₁' ⟨s1, s2, s3, s4⟩
    rw [eSP, l1] at s1; rw [eSP, l2] at s2
    have fr1 : EFr SelR d d₁ := ⟨fun r _ hr _ => s3 r (fun h => hr (Or.inr (Or.inr (Or.inr h))))
      (fun h => hr (Or.inr (Or.inl h))) (fun h => hr (Or.inr (Or.inr (Or.inl h)))),
      (s3 ALLOC (by kqr) (by kqr) (by kqr)).ge, fun a _ => by rw [s4]⟩
    have k1 : ∀ r, r = kqF ∨ r = kqE ∨ r = kqH → d₁.nreg r = d.nreg r := fun r hr => by
      rcases hr with rfl | rfl | rfl <;> exact s3 _ (by kqr) (by kqr) (by kqr)
    have hF1 : d₁.nreg kqF ≤ 1 := by grind
    refine (offerQ_irs hI₁ (hK₀.fix hI₁) (hctx.transport (fr1.kkeep (by omega_nf) (by kqr))
      (fun a ha => fr1.2.2 a ha) fr1.2.1) (by rw [fr1.kkeep (by omega_nf) (by kqr)]; exact hgw)
      hgn hF1 (fun h => ?_) (by rw [s1, s2]; exact hH.2.2.1 _ hs) (by omega)).mono le_rfl ?_
    · grind [Chazelle.Core.SweepEv.candK_posW]
    rintro d' ⟨o1, o2, o3, o4, fr2⟩
    rw [s1, s2] at o2 o3
    rw [k1 _ (Or.inl rfl), k1 _ (Or.inr (Or.inl rfl)), k1 _ (Or.inr (Or.inr rfl))] at o2 o4
    refine ⟨fr.trans (fr1.trans (fr2.mono fun r h => Or.inl h)), by omega,
      ⟨fun _ => Or.inr (Or.inl ⟨trivial, hs⟩), fun _ => o1⟩, fun _ => ?_⟩
    rcases o2 with ⟨hF', e1, e2⟩ | ⟨e1, e2⟩
    · ram_grind
    · ram_grind
  · rw [eSP, eSC] at hs
    refine IRS.mono (K := 0 + 2) (IRS.ifF (by omega) (IRS.skip hId rfl))
      (by norm_num) ?_
    core_grind

set_option maxHeartbeats 8000000 in
theorem selW_irs (hK₀ : Consts c₀) (hH : CandHyp P J c)
    (hctx : ChainCtx P W d (sw 2) J.whole) (hgw : d.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n) (hId : IInv W c₀ d)
    (hS : SelInv P J c d True False) (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ selW d 11024 (fun d' => SelInv P J c d' True True) := by
  obtain ⟨fr, hF, hiff, hmin⟩ := hS
  have eWX : d.nreg wX = c.nreg wX := fr.kkeep (by omega_nf) (by kqr)
  have eWE : d.nreg wE = c.nreg wE := fr.kkeep (by omega_nf) (by kqr)
  have eWH : d.nreg wH = c.nreg wH := fr.kkeep (by omega_nf) (by kqr)
  have hKd := hK₀.fix hId
  unfold selW
  by_cases hs : d.nreg K0 < d.nreg wX
  · have hw : c.nreg wX ≠ 0 := by omega
    refine IRS.mono (K := 0 + 2) (IRS.ifT hs (IRS.skip hId rfl)) (by norm_num) ?_
    core_grind
  · have hw : c.nreg wX = 0 := by ram_grind
    refine IRS.mono (K := 11022 + 2) (IRS.ifF hs ?_) le_rfl (fun _ h => h)
    refine IRS.seq (K₁ := 2) (K₂ := 11020) (IRS.block [.copyN kqSE wE, .copyN kqSH wH] hId
      ⟨iscr_sw' (by norm_num) (by norm_num), iscr_sw' (by norm_num) (by norm_num), trivial⟩) ?_
    rintro d₁ hI₁ hA₁ hA₁' hd₁
    have fr1 : EFr SelR d d₁ := by
      rw [hd₁]; exact kqEfr_block _ (by simp [dstI, SelR]) (by omega_nf)
    have s1 : d₁.nreg kqSE = d.nreg wE := by rw [hd₁]; simp [regB, regI, upd, kqSE, kqSH, wE, sw]
    have s2 : d₁.nreg kqSH = d.nreg wH := by rw [hd₁]; simp [regB, regI, upd, kqSE, kqSH, wH, sw]
    rw [eWE] at s1; rw [eWH] at s2
    have k1 : ∀ r, r = kqF ∨ r = kqE ∨ r = kqH → d₁.nreg r = d.nreg r := fun r hr => by
      rw [hd₁]
      rcases hr with rfl | rfl | rfl <;> simp [regB, regI, upd, kqF, kqE, kqH, kqSE, kqSH, sw]
    have hF1 : d₁.nreg kqF ≤ 1 := by grind
    refine (offerQ_irs hI₁ (hK₀.fix hI₁) (hctx.transport (fr1.kkeep (by omega_nf) (by kqr))
      (fun a ha => fr1.2.2 a ha) fr1.2.1) (by rw [fr1.kkeep (by omega_nf) (by kqr)]; exact hgw)
      hgn hF1 (fun h => ?_) (by ram_grind) (by omega)).mono le_rfl ?_
    · grind [Chazelle.Core.SweepEv.candK_posW]
    rintro d' ⟨o1, o2, o3, o4, fr2⟩
    rw [s1, s2] at o2 o3
    rw [k1 _ (Or.inl rfl), k1 _ (Or.inr (Or.inl rfl)), k1 _ (Or.inr (Or.inr rfl))] at o2 o4
    refine ⟨fr.trans (fr1.trans (fr2.mono fun r h => Or.inl h)), by omega,
      ⟨fun _ => Or.inr (Or.inr ⟨trivial, hw⟩), fun _ => o1⟩, fun _ => ?_⟩
    rcases o2 with ⟨hF', e1, e2⟩ | ⟨e1, e2⟩
    · grind
    · ram_grind

end

end SweepEv

end Chazelle.Core
