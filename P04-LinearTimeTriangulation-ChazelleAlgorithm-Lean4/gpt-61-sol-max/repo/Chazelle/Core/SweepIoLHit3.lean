module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLHit2

/-!
# The sweep RAM (WP-D), answers: the local hit, part 3 (the chord ends)

The far ends of the exit chords of the three regions attached at `x` along the ray (`ChordAt`):
for each region, a loop over its exit chords tests the record words and offers the far end.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The far end of a chord at `x` -/

/-- **A chord record attached at `x` along the direction** has its far end on the ray. -/
theorem chord_far {C : Chain} {N : NF} (hNF : IsNF (chainModel C) (Qof P) N) {k : ℕ}
    (hk : k < N.nChords) {x : WPos} {d : ℕ} (hca : Sweep.ChordAt (N.chord k) x d) :
    ProperPos (chainModel C) (Qof P) P.n (Sweep.farPos (N.chord k) d) ∧
      (Sweep.farPos (N.chord k) d).edge < (chainModel C).W.n ∧
      ∃ τ, 0 < τ ∧ (chainModel C).pos (Qof P) (Sweep.farPos (N.chord k) d) =
        rayPt ((chainModel C).pos (Qof P) x) (dirOf d) τ := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hA := hNF.2.2.1 k hk
  have hFam := hNF.1
  obtain ⟨-, -, -, reg, -, -, -, -, -, hhlt, -⟩ := hNF
  have hh := hhlt k hk
  rw [hQn] at hh
  have hmem : (N.chord k).toSet (chainModel C) (Qof P) ∈ N.F (chainModel C) (Qof P) :=
    ⟨N.chord k, by unfold NF.chord; rw [NFLoc.getD_of_lt _ hk]; grind, rfl⟩
  obtain ⟨y, a, b, hH, -, hey, -, -⟩ := Merge.augChords_spec (hFam.2.1 hmem)
  have hab := hH.lt
  obtain ⟨hla, hrb, -⟩ := Sweep.rec_pos_ends hA hey hab
  obtain ⟨⟨hlp, hl0, hl1, -⟩, ⟨hrp, hr0, hr1, -⟩⟩ := hA
  unfold Sweep.ChordAt at hca
  unfold Sweep.farPos
  rcases hca with ⟨hd, hlx, hhx⟩ | ⟨hd, hrx, hhx⟩
  · have hx : x = (N.chord k).lpos := by
      simp_all [CRec.lpos] 
    rw [ite_eq_left hd, hx, hla, hrb, hd]
    refine ⟨⟨hr0, hr1, by grind [CRec.rpos]⟩, hrp, b - a, by linarith, ?_⟩
    simp_all [rayPt, dirOf] <;> omega_nf
  · have hx : x = (N.chord k).rpos := by
      simp_all [CRec.rpos] 
    rw [ite_eq_right hd, hx, hla, hrb]
    refine ⟨⟨hl0, hl1, by grind [CRec.lpos]⟩, hlp, b - a, by linarith, ?_⟩
    simp_all [rayPt, dirOf] <;> omega_nf

/-! ## Registers and programs of the scan -/

def sX : ℕ := sw 1130
def sY : ℕ := sw 1131
def sNc : ℕ := sw 1132
def sCl : ℕ := sw 1133
def sT : ℕ := sw 1134
def sK : ℕ := sw 1135
def sCh : ℕ := sw 1136
def sLp : ℕ := sw 1137
def sRp : ℕ := sw 1138
def sH1 : ℕ := sw 1139
def sFe : ℕ := sw 1140
def sFh : ℕ := sw 1141
def sR5 : ℕ := sw 1142
def sL7 : ℕ := sw 1143
def sC3 : ℕ := sw 1144

/-- The registers of the scan. -/
def SSet (r : ℕ) : Prop := sw 1130 ≤ r ∧ r ≤ sw 1144

/-- The bases of the normal form. -/
def scanInitL : List Instr :=
  [.addN sX lNF K5, .loadN sR5 sX, .addN sX sX K2, .loadN sL7 sX, .addN sX lNF K3, .loadN sC3 sX]

/-- The head of the scan of the region in `rr`. -/
def scanHeadL (rr : ℕ) : List Instr :=
  [.addN sX rr rr, .addN sX sX sX, .addN sX sX rr, .addN sX sR5 sX, .addN sY sX K2, .loadN sNc sY,
    .addN sY sX K3, .loadN sCl sY, .constN sT 0]

def scanHead (rr : ℕ) : Stmt :=
  .seq (block (scanHeadL rr)) (.ifLtN K0 sNc (.instr (.addN sCl sCl sL7)) .skip)

/-- Read the chord at place `sT`: its height code (plus one) and its walk edges. -/
def scanReadL : List Instr :=
  [.addN sX sCl sT, .loadN sK sX, .addN sX sK sK, .addN sX sX sX, .addN sX sX sK, .addN sX sC3 sX,
    .loadN sCh sX, .addN sY sX K1, .loadN sLp sY, .addN sY sY K1, .loadN sRp sY,
    .addN sH1 sCh K1]

/-- `s` if the registers `a`, `b` hold equal values. -/
def eqT (a b : ℕ) (s : Stmt) : Stmt := .ifLtN a b .skip (.ifLtN b a .skip s)

/-- Offer the position `(src, sH1)`. -/
def offerFar (src : ℕ) : Stmt :=
  .seq (block [.copyN sFe src, .copyN sFh sH1]) (offerF accA lCD sFe sFh lT lD lN lO)

/-- The test `ChordAt` and the offer of the far end. -/
def scanTest : Stmt :=
  .ifLtN lD K1 (eqT sRp lE (eqT sH1 lH (offerFar sLp)))
    (.ifLtN K1 lD (eqT sRp lE (eqT sH1 lH (offerFar sLp)))
      (eqT sLp lE (eqT sH1 lH (offerFar sRp))))

def scanBody : Stmt := .seq (block scanReadL) (.seq scanTest (block [.addN sT sT K1]))

def scanR (rr : ℕ) : Stmt := .seq (scanHead rr) (.whileLtN sT sNc scanBody)

/-- **The chord ends of the three regions.** -/
def lhScan : Stmt := .seq (block scanInitL) (.seq (scanR lR0) (.seq (scanR lR1) (scanR lR2)))

section
variable (m f : ℕ → ℕ) (hk1 : f K1 = 1)
include hk1
theorem scanReadL_val :
    regB m scanReadL f sLp = m (f sC3 + 5 * m (f sCl + f sT) + 1) ∧
    regB m scanReadL f sRp = m (f sC3 + 5 * m (f sCl + f sT) + 2) ∧
    regB m scanReadL f sH1 = m (f sC3 + 5 * m (f sCl + f sT)) + 1 := by
  have e1 : f 240611 = 1 := hk1
  simp only [scanReadL, regB, regI, upd, sX, sY, sCl, sT, sK, sC3, sCh, sLp, sRp, sH1, K1, sw]
  simp_all +arith

theorem scanReadL_ok (hb : f sCl + f sT ≤ W)
    (hb2 : f sC3 + 5 * m (f sCl + f sT) + 2 ≤ W) (hb3 : m (f sC3 + 5 * m (f sCl + f sT)) + 1 ≤ W) :
    okB W m scanReadL f := by
  have e1 : f 240611 = 1 := hk1
  have hb' : f 241133 + f 241134 ≤ W := hb
  have hb2' : f 241144 + 5 * m (f 241133 + f 241134) + 2 ≤ W := hb2
  have hb3' : m (f 241144 + (m (f 241133 + f 241134) + m (f 241133 + f 241134) +
      (m (f 241133 + f 241134) + m (f 241133 + f 241134)) + m (f 241133 + f 241134))) + 1 ≤ W := by
    rw [show f 241144 + (m (f 241133 + f 241134) + m (f 241133 + f 241134) +
      (m (f 241133 + f 241134) + m (f 241133 + f 241134)) + m (f 241133 + f 241134)) =
      f 241144 + 5 * m (f 241133 + f 241134) by ring]; exact hb3
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (by omega) (by omega)
  simp only [scanReadL, okB, okI, regI, upd, sX, sY, sCl, sT, sK, sC3, sCh, sLp, sRp, sH1, K1, sw]
  grind

/-! ## The accumulator during the scan -/


end

/-- The chords of a list whose far ends (attached at `x` along `d`) are offered. -/
def ChordsDone (P : Polygon) (C : Chain) (N : NF) (x : WPos) (d : ℕ) (ks : List ℕ)
    (L : Set ℝ) : Prop :=
  ∀ k ∈ ks, Sweep.ChordAt (N.chord k) x d → ∃ τ ∈ L,
    (chainModel C).pos (Qof P) (Sweep.farPos (N.chord k) d) =
      rayPt ((chainModel C).pos (Qof P) x) (dirOf d) τ


/-! ## Offering a far end -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem offerFar_irs {src : ℕ} (hsrc : src = sLp ∨ src = sRp) {C : Chain} {Mod : ℕ → Chain}
    {R₀ : ℝ} {z : Point} {L : Set ℝ} {τ : ℝ} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W) (hctx : ChainCtx P W c lCD C)
    (hacc : AccOK P accA Mod R₀ z (dirOf (c.nreg lD)) L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod (c.nreg lT) = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (he : c.nreg src < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg src, c.nreg sH1⟩)
    (hpos : (chainModel C).pos (Qof P) ⟨c.nreg src, c.nreg sH1⟩ = rayPt z (dirOf (c.nreg lD)) τ)
    (hy : |z.2| < R₀) (hroom : c.nreg ALLOC + (2 + offerFK) ≤ W) :
    IRS P W c₀ (offerFar src) c (2 + offerFK) (fun c' =>
      (∃ L', AccOK P accA Mod R₀ z (dirOf (c.nreg lD)) L' c' ∧
        (L' = L ∨ (L' = insert τ L ∧ OnCB C (rayPt z (dirOf (c.nreg lD)) τ))) ∧
        (z.2 ≤ C.top.2 → L' = insert τ L)) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → (r < accA ∨ accA + 12 < r) → r ≠ lO →
        r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  
  have hok : okB W c.nmem [.copyN sFe src, .copyN sFh sH1] c.nreg :=
    ⟨iscr_sw (by omega_nf) (by omega_nf),
      iscr_sw (by omega_nf) (by omega_nf), trivial⟩
  refine IRS.seq (K₂ := offerFK) (IRS.block _ hI hok) ?_ |>.mono (by simp) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have vFe : c₁.nreg sFe = c.nreg src := by
    simp_all [regB, regI, sFe, sFh, sw, upd_same] 
  have vFh : c₁.nreg sFh = c.nreg sH1 := by
    simp_all [regB, regI, upd_same, sFe, sH1, sw] 
  have k1 : ∀ q, q ≠ sFe → q ≠ sFh → c₁.nreg q = c.nreg q := by
    simp_all [regB, regI] 
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have kk : ∀ q, ¬ SSet q → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q (fun h => hq (by grind [SSet, sFe, sw]))
      (fun h => hq (by grind [SSet, sFh, sw]))
  have t1 := kk lT (by omega_nf)
  have d1 := kk lD (by omega_nf)
  have n1 := kk lN (by omega_nf)
  have cd1 := kk lCD (by omega_nf)
  have hA1 := kk ALLOC (by omega_nf)
  have a1 : ∀ j, j ≤ 12 → c₁.nreg (accA + j) = c.nreg (accA + j) := fun j hj =>
    kk _ (by omega_nf)
  refine (offerF_irs (L := L) (τ := τ) (Mod := Mod) hI₁ hK hG hW3
    ⟨by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf⟩
    (by rw [d1]; exact hacc.transport a1) (by omega)
    (by grind [Chazelle.Core.SweepIo.ChainCtx])
    (by grind) (by grind) (by grind)
    (by grind) (by grind) hy
    (by omega)).mono le_rfl ?_
  rintro c' ⟨⟨L', hacc', hL', hc'⟩, k2, hA2, hm2⟩
  simp only [d1, t1, hMod] at hacc' hL' hc'
  refine ⟨⟨L', hacc', hL', hc'⟩, fun r hr hs1 hs2 hra hro hro1 hrA => ?_, by omega,
    fun a ha => by grind⟩
  grind

/-! ## The test of a chord -/

/-- The cost of the test. -/
def scanTestK : ℕ := 14 + offerFK

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The double equality test and the offer.** -/
theorem eqOffer_irs {a src : ℕ} (_ha : a = sLp ∨ a = sRp) (hsrc : src = sLp ∨ src = sRp)
    {C : Chain} {N : NF} {k : ℕ} (hk : k < N.nChords) {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point}
    {L : Set ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W)
    (hctx : ChainCtx P W c lCD C) (hNF : IsNF (chainModel C) (Qof P) N)
    (hacc : AccOK P accA Mod R₀ z (dirOf (c.nreg lD)) L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod (c.nreg lT) = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (hz : z = (chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) (hy : |z.2| < R₀)
    (hiff : (c.nreg a = c.nreg lE ∧ c.nreg sH1 = c.nreg lH) ↔
      Sweep.ChordAt (N.chord k) ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD))
    (hfar : Sweep.farPos (N.chord k) (c.nreg lD) = ⟨c.nreg src, c.nreg sH1⟩)
    (hroom : c.nreg ALLOC + (10 + offerFK) ≤ W) :
    IRS P W c₀ (eqT a lE (eqT sH1 lH (offerFar src))) c (10 + offerFK) (fun c' =>
      (∃ L', AccOK P accA Mod R₀ z (dirOf (c.nreg lD)) L' c' ∧ L ⊆ L' ∧
        (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt z (dirOf (c.nreg lD)) τ))) ∧
        (z.2 ≤ C.top.2 → ChordsDone P C N ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) [k] L')) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → (r < accA ∨ accA + 12 < r) → r ≠ lO →
        r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  -- no match: nothing offered
  have hnone : ¬ Sweep.ChordAt (N.chord k) ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) → ∀ K',
      IRS P W c₀ .skip c K' (fun c' =>
        (∃ L', AccOK P accA Mod R₀ z (dirOf (c.nreg lD)) L' c' ∧ L ⊆ L' ∧
          (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt z (dirOf (c.nreg lD)) τ))) ∧
          (z.2 ≤ C.top.2 → ChordsDone P C N ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) [k] L')) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → (r < accA ∨ accA + 12 < r) → r ≠ lO →
          r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
    intro hnc K'
    refine IRS.skip hI ⟨⟨L, hacc, le_rfl, fun τ hτ => Or.inl hτ, fun _ k' hk' hca => ?_⟩,
      fun _ _ _ _ _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩
    simp_all
  unfold eqT
  by_cases h1 : c.nreg a < c.nreg lE
  · exact (IRS.ifT h1 (hnone (fun hca => by grind) (8 + offerFK))).mono
      (by omega) (fun _ h => h)
  refine IRS.mono (K := (8 + offerFK) + 2) (IRS.ifF h1 ?_) (by omega) (fun _ h => h)
  by_cases h2 : c.nreg lE < c.nreg a
  · exact (IRS.ifT h2 (hnone (fun hca => by grind) (6 + offerFK))).mono
      (by omega) (fun _ h => h)
  refine IRS.mono (K := (6 + offerFK) + 2) (IRS.ifF h2 ?_) (by omega) (fun _ h => h)
  by_cases h3 : c.nreg sH1 < c.nreg lH
  · exact (IRS.ifT h3 (hnone (fun hca => by grind) (4 + offerFK))).mono
      (by omega) (fun _ h => h)
  refine IRS.mono (K := (4 + offerFK) + 2) (IRS.ifF h3 ?_) (by omega) (fun _ h => h)
  by_cases h4 : c.nreg lH < c.nreg sH1
  · exact (IRS.ifT h4 (hnone (fun hca => by grind) (2 + offerFK))).mono
      (by omega) (fun _ h => h)
  refine IRS.mono (K := (2 + offerFK) + 2) (IRS.ifF h4 ?_) (by omega) (fun _ h => h)
  -- a match
  have hca : Sweep.ChordAt (N.chord k) ⟨c.nreg lE, c.nreg lH⟩ (c.nreg lD) := hiff.1 ⟨by omega, by omega⟩
  obtain ⟨hpp, hedge, τ, hτ, hpos⟩ := chord_far hNF hk hca
  rw [hfar] at hpp hedge hpos
  rw [← hz] at hpos
  refine (offerFar_irs hsrc (L := L) (τ := τ) hI hK hG hW3 hctx hacc htag hMod hR hn hedge hpp hpos hy
    (by omega)).mono le_rfl ?_
  rintro c' ⟨⟨L', hacc', hL', hc'⟩, k', hA', hm'⟩
  refine ⟨⟨L', hacc', ?_, fun τ' hτ' => ?_, fun hzt k'' hk'' hca' => ?_⟩, k', hA', hm'⟩
  · grind
  · grind
  grind

end

end SweepIo

end Chazelle.Core
