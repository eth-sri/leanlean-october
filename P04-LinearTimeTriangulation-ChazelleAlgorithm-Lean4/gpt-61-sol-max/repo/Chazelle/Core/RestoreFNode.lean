module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFEndF
public import Chazelle.Core.RestoreFSel
public import Chazelle.Core.RestoreNodeCand
public import Chazelle.Core.RestoreRegArc
public import Chazelle.Core.RestoreTPos

/-!
# WP-E, the search on the RAM (`FindOK`), part 20: a node of the descent

`nodeS`: at the chord node `81150 = 2k` of the piece's normal form, load the chord, run both
ends (tests and side bits), choose the witness offset, load the children and the reference arc,
and set `81150` to the child on the side of the witness (`lo` if no witness passed).
`node_fs`: soundness (for every piece) and the raw facts (`NodeRaw`) the descent's completeness
argument reads.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sidePt SideAttach sideInArc)

variable {E : FEnv} {c₀ c : Config}

/-- **A node of the descent.** -/
def nodeS (sT : Stmt) : Stmt :=
  .seq chordLoad (.seq (endFull 81160 81153 1 sT) (.seq (endFull 81170 81154 0 sT)
    (.seq wsel (.seq kidLoad (.seq refLoad
      (.ifLtN 81011 81181 sideCh (Stmt.block [.copyN 81150 81118])))))))

/-- The cost bound of a node at code `x`. -/
def ndK (E : FEnv) (x : ℕ) : ℕ := clK E x + 2 * efK E + wsK + 10 + 25 + scK + 4

/-- The registers a node writes. -/
def NodeW (q : ℕ) : Prop :=
  KeyW q ∨ VertW q ∨ (81100 ≤ q ∧ q ≤ 81129) ∨ q = 81150 ∨ (81152 ≤ q ∧ q ≤ 81199)

/-- **The facts of a kind-1 piece's stretch** that every node needs. -/
structure PCtx (E : FEnv) (c₀ : Config) (Cα : Chain) (Hα : Host) (Nα : NF)
    (g g' L Dα Bα : ℕ) : Prop where
  hS : Stretch E.M Cα g g' L
  hQ : Cα.P = Qof E.P
  hNα : IsNF (chainModel Cα) (Qof E.P) Nα
  hDec : ∃ dd, IsDecomp Nα dd
  hNW : NFWithin c₀.nmem Bα (c₀.nreg ALLOC) Nα
  hD : ChainDescAt c₀.nmem Dα (Qof E.P) Hα Cα
  hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem Dα
  hWm : 2 * Cα.m + 7 ≤ E.W

/-- The stretch registers. -/
def SRegs (c : Config) (g g' L Dα Bα : ℕ) : Prop :=
  c.nreg 81130 = g ∧ c.nreg 81131 = g' ∧ c.nreg 81132 = L ∧ c.nreg 81133 = Dα ∧
    c.nreg 81134 = Bα ∧ c.nreg 81135 = g' + L

/-- **The raw facts of a node run** from `c` to `c'` (chord `k`). -/
def NodeRaw (E : FEnv) (c₀ : Config) (Cα : Chain) (Nα : NF) (k : ℕ) (c c' : Config) : Prop :=
  ∃ c₁ c₂ c₃ c₄ : Config,
    -- the chord
    (c₁.nreg 81152 = (Nα.chord k).h ∧ c₁.nreg 81153 = (Nα.chord k).lp ∧
      c₁.nreg 81154 = (Nα.chord k).rp ∧ c₁.nreg 81155 = (Nα.chord k).h + 1 ∧
      ∀ q, 81130 ≤ q → q ≤ 81141 → c₁.nreg q = c.nreg q) ∧
    c₁.nreg 81007 = c.nreg 81007 ∧
    -- the ends
    EndRes E c₀ Cα 81160 81153 1 c₁ c₂ ∧
    (∀ q, 81011 ≤ q → q < 83000 → ¬ EndW 81160 q → c₂.nreg q = c₁.nreg q) ∧
    (c₁.nreg 81007 = 1 → c₂.nreg 81007 = 1) ∧ FWin E c₂ ∧
    EndRes E c₀ Cα 81170 81154 0 c₂ c₃ ∧
    (∀ q, 81011 ≤ q → q < 83000 → ¬ EndW 81170 q → c₃.nreg q = c₂.nreg q) ∧
    (c₂.nreg 81007 = 1 → c₃.nreg 81007 = 1) ∧
    -- the witness
    c₄.nreg 81181 ≤ 1 ∧
    (c₄.nreg 81181 = 1 → WCand E c₀ c₃ (c₄.nreg 81180) ∧
      c₄.nreg 81183 = c₃.nreg 81131 + c₄.nreg 81180 ∧ 1 ≤ c₄.nreg 81180) ∧
    ((WCand E c₀ c₃ 1 ∨
      (c₃.nreg 81160 = 1 ∧ WCand E c₀ c₃ (c₃.nreg 81153 - c₃.nreg 81131 + 1)) ∨
      (c₃.nreg 81170 = 1 ∧ WCand E c₀ c₃ (c₃.nreg 81154 - c₃.nreg 81131 + 1))) →
        c₄.nreg 81181 = 1) ∧
    c₄.nreg 81007 = c₃.nreg 81007 ∧
    -- the choice
    (c₄.nreg 81181 = 1 →
      let k' := fun (x : WPos) => (chainModel Cα).key (Qof E.P) x
      let kA := k' (Nα.chord k).lpos
      let kB := k' (Nα.chord k).rpos
      let kU := k' ⟨c₄.nreg 81183, 0⟩
      let j := (Nα.region (Nα.chord k).dn).arcs.getD 0 0
      let kS := k' (Nα.arc j).s
      ((sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) → c'.nreg 81150 = (Nα.dnode k).lo) ∧
      (¬ (sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) →
        c'.nreg 81150 = (Nα.dnode k).hi)) ∧
    c'.nreg 81007 = c₄.nreg 81007

theorem node_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs c g g' L Dα Bα)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n ⟨c.nreg 81140, c.nreg 81141⟩)
    {k : ℕ} (hx : c.nreg 81150 = 2 * k) (hk : k < Nα.nChords)
    (hroom : c.nreg ALLOC + ndK E (2 * k) ≤ E.W) :
    FRS B E.P E.W c₀ (nodeS E.sT) c (ndK E (2 * k)) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ NodeW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (c'.nreg 81150 = (Nα.dnode k).lo ∨ c'.nreg 81150 = (Nα.dnode k).hi) ∧
      NodeRaw E c₀ Cα Nα k c c') := by
  obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR
  have hS := hP.hS
  
  have hsimp : Cα.P.Simple := by rw [hP.hQ]; exact (shearInvariance (epsOf E.P) E.P).1 hE.hG.1
  have hGα : GoodModel (chainModel Cα) := Or.inl ⟨Cα, hsimp, rfl⟩
  have hMα := walkAx_of_goodModel hGα
  obtain ⟨hpA, hpB⟩ := chord_posOK hsimp hP.hNα hk
  have hat := hP.hNα.2.2.1 k hk
  obtain ⟨dd, hDec⟩ := hP.hDec
  have hdec : Nα.dec.length = Nα.nChords := hDec.1
  obtain ⟨-, -, -, regα, h1α, h2α, h3α, h4α, -, hhα, -⟩ := id hP.hNα
  have hregsα : NFRegs (chainModel Cα) (Qof E.P) Nα regα := ⟨h1α, h2α, h3α, h4α⟩
  have hneα : (Nα.F (chainModel Cα) (Qof E.P)).Nonempty := ⟨_, _, Dec.chord_mem hk, rfl⟩
  have hdn : (Nα.chord k).dn < Nα.nRegions := (h2α k hk).2.1
  obtain ⟨har, hj, -⟩ := region_arc hMα hP.hNα hregsα hneα hdn
  have hpS := (arc_posOK hsimp hP.hNα hneα hj).1
  have hhn : (Nα.chord k).h < E.P.n := by
    have := hhα k hk; rwa [show (Qof E.P).n = E.P.n from shear_n _ _] at this
  have hnW : E.P.n ≤ E.W := by have := hE.hWh; grind [hostWords]
  have hyc : ∀ z ∈ (Nα.chord k).toSet (chainModel Cα) (Qof E.P), z.2 = ((Qof E.P).vtx (Nα.chord k).h).2 :=
    fun z hz => by grind [CRec.toSet, Visibility.hseg]
  have hgL : g' + L ≤ 2 * Cα.m + 6 := hS.hgL
  have hL0 := hS.hL0
  have hLn := hS.hLn
  have h6 := hS.h6
  -- the chord
  refine (FRS.seq (K₂ := 2 * efK E + wsK + 10 + 25 + scK + 4) (chordLoad_fs hE hB hI (N := Nα)
    (by rw [r34]; exact hP.hNW) hx (by omega) (by grind)
    (by grind [ndK])) (fun c₁ hI₁ hA₁ ⟨u21, u52, u53, u54, u55, u56, f₁⟩ => ?_)).mono
    (by unfold ndK; omega) (fun _ h => h)
  rw [show 2 * k / 2 = k by omega] at u21 u52 u53 u54 u55 u56
  have F1 : ∀ q, ¬ (81120 ≤ q ∧ q ≤ 81124) → ¬ (81152 ≤ q ∧ q ≤ 81158) → c₁.nreg q = c.nreg q := f₁
  have sT : ∀ {x y : Config}, SRegs x g g' L Dα Bα →
      (∀ q, 81130 ≤ q → q ≤ 81135 → y.nreg q = x.nreg q) → SRegs y g g' L Dα Bα := by
    intro x y hs h
    grind [Chazelle.Core.Restore.SRegs]
  have s1 : SRegs c₁ g g' L Dα Bα :=
    sT ⟨r30, r31, r32, r33, r34, r35⟩ (fun q a b => F1 q (by omega) (by omega))
  have hw₁ : FWin E c₁ := hw.congr' (fun q h1 h2 => F1 q (by omega) (by omega))
  -- the candidate facts of an end
  have candE : ∀ (cx : Config) (p pv : ℕ) (tv : ℝ), SRegs cx g g' L Dα Bα → cx.nreg p = pv →
      cx.nreg 81152 = (Nα.chord k).h → cx.nreg 81155 = (Nα.chord k).h + 1 →
      SideAttach (chainModel Cα).W ((Nα.chord k).toSet (chainModel Cα) (Qof E.P)) pv
        ((chainModel Cα).param (Qof E.P) ⟨pv, (Nα.chord k).h + 1⟩) →
      PosOK Cα (Qof E.P) E.P.n ⟨pv, (Nα.chord k).h + 1⟩ →
      cx.nreg 81131 ≤ cx.nreg p → cx.nreg p < cx.nreg 81135 →
      InRange c₀ (eMof E cx p) → ∀ σb, σb ≤ 1 →
        CandOK E ⟨eMof E cx p, endCode Cα (Qof E.P) (cx.nreg p) (cx.nreg 81155)⟩
          (cx.nreg 81152) σb := by
    intro cx p pv tv ⟨x30, x31, x32, x33, x34, x35⟩ xp x52 x55 hAt hpo a b hr σb hσb
    rw [x31, xp] at a; rw [x35, xp] at b
    obtain ⟨d, rfl⟩ : ∃ d, pv = g' + d := ⟨pv - g', by omega⟩
    have hd : d < L := by omega
    unfold eMof at hr ⊢
    rw [x30, x31, xp, show g' + d - g' = d by omega] at hr ⊢
    rw [x52, x55]
    exact end_cand hE hS hd hpo hAt hyc hr hσb
  have hgn : g < E.M.W.n := hS.hg
  have hWm := hP.hWm
  have hJ₁ : c₁.nreg 81140 < E.M.W.n ∧
      ProperPos E.M (Qof E.P) E.P.n ⟨c₁.nreg 81140, c₁.nreg 81141⟩ := by
    rw [F1 81140 (by omega) (by omega), F1 81141 (by omega) (by omega)]; exact hJ
  have fl₁ : c₁.nreg 81007 = c.nreg 81007 := F1 _ (by omega) (by omega)
  -- the left end
  refine (FRS.seq (K₂ := efK E + wsK + 10 + 25 + scK + 4) (endFull_fs hE hB hBT hI₁ hw₁
    (s := 81160) (p := 81153) (σ := 1) ⟨by norm_num, by norm_num⟩ (Or.inl rfl) le_rfl
    (by rw [s1.2.2.2.1]; exact hP.hwf) (by rw [s1.2.2.2.1]; exact hP.hD) hWm
    (by rw [s1.2.1]; exact h6) (by rw [s1.1]; exact hgn) (by rw [s1.2.2.2.2.2, s1.2.1]; omega)
    (by rw [u53, u55]; exact hpA) (candE c₁ 81153 _ 0 s1 u53 u52 u55 hat.1 hpA) hJ₁
    (by unfold ndK at hroom; omega)) (fun c₂ hI₂ hA₂ ⟨hw₂, f₂, m₂, R₂⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have e2 : ∀ q, 81100 ≤ q → q ≤ 81159 → c₂.nreg q = c₁.nreg q :=
    fun q a b => f₂ q (by omega) (by omega) (by omega_nf)
  have s2 := sT s1 (fun q a b => e2 q (by omega) (by omega))
  have v52 : c₂.nreg 81152 = (Nα.chord k).h := by rw [e2 _ (by norm_num) (by norm_num), u52]
  have v53 : c₂.nreg 81153 = (Nα.chord k).lp := by rw [e2 _ (by norm_num) (by norm_num), u53]
  have v54 : c₂.nreg 81154 = (Nα.chord k).rp := by rw [e2 _ (by norm_num) (by norm_num), u54]
  have v55 : c₂.nreg 81155 = (Nα.chord k).h + 1 := by
    rw [e2 _ (by norm_num) (by norm_num), u55]
  have v56 : c₂.nreg 81156 = (Nα.chord k).dn := by rw [e2 _ (by norm_num) (by norm_num), u56]
  have v21 : c₂.nreg 81121 = k := by rw [e2 _ (by norm_num) (by norm_num), u21]
  have hJ₂ : c₂.nreg 81140 < E.M.W.n ∧
      ProperPos E.M (Qof E.P) E.P.n ⟨c₂.nreg 81140, c₂.nreg 81141⟩ := by
    rw [e2 81140 (by norm_num) (by norm_num), e2 81141 (by norm_num) (by norm_num)]; exact hJ₁
  -- the right end
  refine (FRS.seq (K₂ := wsK + 10 + 25 + scK + 4) (endFull_fs hE hB hBT hI₂ hw₂
    (s := 81170) (p := 81154) (σ := 0) ⟨by norm_num, by norm_num⟩ (Or.inr rfl) (by norm_num)
    (by rw [s2.2.2.2.1]; exact hP.hwf) (by rw [s2.2.2.2.1]; exact hP.hD) hWm
    (by rw [s2.2.1]; exact h6) (by rw [s2.1]; exact hgn) (by rw [s2.2.2.2.2.2, s2.2.1]; omega)
    (by rw [v54, v55]; exact hpB) (candE c₂ 81154 _ 0 s2 v54 v52 v55 hat.2 hpB) hJ₂
    (by unfold ndK at hroom; omega)) (fun c₃ hI₃ hA₃ ⟨hw₃, f₃, m₃, R₃⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have e3 : ∀ q, 81100 ≤ q → q ≤ 81169 → c₃.nreg q = c₂.nreg q :=
    fun q a b => f₃ q (by omega) (by omega) (by omega_nf)
  have s3 := sT s2 (fun q a b => e3 q (by omega) (by omega))
  have w53 : c₃.nreg 81153 = (Nα.chord k).lp := by rw [e3 _ (by norm_num) (by norm_num), v53]
  have w54 : c₃.nreg 81154 = (Nα.chord k).rp := by rw [e3 _ (by norm_num) (by norm_num), v54]
  have w55 : c₃.nreg 81155 = (Nα.chord k).h + 1 := by
    rw [e3 _ (by norm_num) (by norm_num), v55]
  have w56 : c₃.nreg 81156 = (Nα.chord k).dn := by rw [e3 _ (by norm_num) (by norm_num), v56]
  have w21 : c₃.nreg 81121 = k := by rw [e3 _ (by norm_num) (by norm_num), v21]
  have hpA' : c₃.nreg 81160 = 1 → g' ≤ c₃.nreg 81153 ∧ c₃.nreg 81153 - g' < L := by
    intro h1
    rw [e3 _ (by norm_num) (by norm_num)] at h1
    obtain ⟨a, b, -⟩ := R₂.1.2.mp h1
    rw [s1.2.1, u53] at a; rw [s1.2.2.2.2.2, u53] at b; omega
  have hpB' : c₃.nreg 81170 = 1 → g' ≤ c₃.nreg 81154 ∧ c₃.nreg 81154 - g' < L := by
    intro h1
    obtain ⟨a, b, -⟩ := R₃.1.2.mp h1
    rw [s2.2.1, v54] at a; rw [s2.2.2.2.2.2, v54] at b; omega
  -- the witness
  refine (FRS.seq (K₂ := 10 + 25 + scK + 4) (wsel_fs hE hB hI₃
    (R₂.2.2.2.2.2.2.congr (fun j hj => e3 _ (by omega) (by omega))) R₃.2.2.2.2.2.2
    (by rw [s3.1]; exact hgn) (by rw [s3.2.2.1]; exact hLn) (by rw [s3.2.1, s3.2.2.1]; omega)
    (by rw [s3.2.2.1]; exact hL0) (by rw [s3.2.1, s3.2.2.1]; exact hpA')
    (by rw [s3.2.1, s3.2.2.1]; exact hpB')
    (by unfold ndK at hroom; omega)) (fun c₄ hI₄ hA₄ ⟨x81, xC, xAll, f₄⟩ => ?_)).mono
    (by omega) (fun _ h => h)
  have e4 : ∀ q, 81000 ≤ q → q ≤ 81179 → c₄.nreg q = c₃.nreg q :=
    fun q a b => f₄ q (by omega) (by omega) (by omega_nf)
  have s4 := sT s3 (fun q a b => e4 q (by omega) (by omega))
  have x21 : c₄.nreg 81121 = k := by rw [e4 _ (by norm_num) (by norm_num), w21]
  -- the children
  refine (FRS.seq (K₂ := 25 + scK + 4) (kidLoad_fs hE hB hI₄ (N := Nα)
    (by rw [s4.2.2.2.2.1]; exact hP.hNW) (by omega))
    (fun c₅ hI₅ hA₅ ⟨kl, kh, f₅⟩ => ?_)).mono (by omega) (fun _ h => h)
  rw [x21] at kl kh
  have s5 := sT s4 (fun q a b => f₅ q (by omega) (by omega) (by omega))
  have y56 : c₅.nreg 81156 = (Nα.chord k).dn := by
    rw [f₅ _ (by norm_num) (by norm_num) (by norm_num), e4 _ (by norm_num) (by norm_num), w56]
  -- the reference arc
  refine (FRS.seq (K₂ := scK + 4) (refLoad_fs hE hB hI₅ (N := Nα)
    (by rw [s5.2.2.2.2.1]; exact hP.hNW) (by omega) (by rw [y56]; exact har)
    (by rw [y56]; exact hj)) (fun c₆ hI₆ hA₆ ⟨rs, rh, f₆⟩ => ?_)).mono (by omega) (fun _ h => h)
  rw [y56] at rs rh
  have e64 : ∀ q, 81120 ≤ q → q < 83000 → c₆.nreg q = c₄.nreg q := fun q a b => by
    rw [f₆ q (by omega) (by omega) (by omega) (by omega), f₅ q (by omega) (by omega) (by omega)]
  have e6 : ∀ q, 81120 ≤ q → q ≤ 81179 → c₆.nreg q = c₃.nreg q := fun q a b => by
    rw [e64 q a (by omega), e4 q (by omega) b]
  have s6 := sT s5 (fun q a b => f₆ q (by omega) (by omega) (by omega) (by omega))
  have z81 : c₆.nreg 81181 = c₄.nreg 81181 := e64 _ (by norm_num) (by norm_num)
  have z83 : c₆.nreg 81183 = c₄.nreg 81183 := e64 _ (by norm_num) (by norm_num)
  have z11 : c₆.nreg 81011 = 0 := by rw [hI₆.hin _ (by omega_nf), hE.k0]
  have z53 : c₆.nreg 81153 = (Nα.chord k).lp := by rw [e6 _ (by norm_num) (by norm_num), w53]
  have z54 : c₆.nreg 81154 = (Nα.chord k).rp := by rw [e6 _ (by norm_num) (by norm_num), w54]
  have z55 : c₆.nreg 81155 = (Nα.chord k).h + 1 := by
    rw [e6 _ (by norm_num) (by norm_num), w55]
  have z18 : c₆.nreg 81118 = (Nα.dnode k).lo := by
    rw [f₆ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), kl]
  have z19 : c₆.nreg 81119 = (Nα.dnode k).hi := by
    rw [f₆ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), kh]
  have z07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c₆.nreg q = c₃.nreg q := fun q a b => by
    rw [f₆ q (by omega) (by omega) (by omega) (by omega), f₅ q (by omega) (by omega) (by omega),
      e4 q (by omega) (by omega)]
  -- the end
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ ScW q → c'.nreg q = c₆.nreg q) →
      (c'.nreg 81150 = (Nα.dnode k).lo ∨ c'.nreg 81150 = (Nα.dnode k).hi) →
      (c₄.nreg 81181 = 1 →
        let k' := fun (x : WPos) => (chainModel Cα).key (Qof E.P) x
        let kA := k' (Nα.chord k).lpos
        let kB := k' (Nα.chord k).rpos
        let kU := k' ⟨c₄.nreg 81183, 0⟩
        let j := (Nα.region (Nα.chord k).dn).arcs.getD 0 0
        let kS := k' (Nα.arc j).s
        ((sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) →
          c'.nreg 81150 = (Nα.dnode k).lo) ∧
        (¬ (sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) →
          c'.nreg 81150 = (Nα.dnode k).hi)) →
      FWin E c' ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ NodeW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (c'.nreg 81150 = (Nα.dnode k).lo ∨ c'.nreg 81150 = (Nα.dnode k).hi) ∧
      NodeRaw E c₀ Cα Nα k c c' := by
    intro c' hf h50 hch
    have g07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c'.nreg q = c₃.nreg q := fun q a b => by
      rw [hf q (by omega) (by omega) (by unfold ScW KeyW; omega), z07 q a b]
    have fl' : c'.nreg 81007 = c₄.nreg 81007 := by
      rw [g07 _ (by norm_num) (by norm_num), e4 _ (by norm_num) (by norm_num)]
    refine ⟨hw₃.congr' g07, fun q a b hq => ?_, fun h1 => ?_, h50,
      ⟨c₁, c₂, c₃, c₄, ⟨u52, u53, u54, u55, fun q a b => F1 q (by omega) (by omega)⟩, fl₁, R₂, f₂,
        m₂, hw₂, R₃, f₃, m₃, x81, xC, xAll, e4 _ (by norm_num) (by norm_num), hch, fl'⟩⟩
    · unfold NodeW KeyW VertW at hq
      rw [hf q (by omega) (by omega) (by unfold ScW KeyW; omega),
        f₆ q (by omega) (by omega) (by omega) (by omega), f₅ q (by omega) (by omega) (by omega),
        f₄ q (by omega) (by omega) (by unfold WsW KeyW; omega),
        f₃ q a b (by unfold EndW KeyW VertW; omega), f₂ q a b (by unfold EndW KeyW VertW; omega),
        F1 q (by omega) (by omega)]
    · rw [g07 _ (by norm_num) (by norm_num)]; exact m₃ (m₂ (by omega))
  by_cases hc : c₆.nreg 81011 < c₆.nreg 81181
  · have h1 : c₄.nreg 81181 = 1 := by omega
    obtain ⟨xu, xe, -⟩ := xC h1
    have hu : c₄.nreg 81180 < L := by have := xu.1; rw [s3.2.2.1] at this; exact this
    have hpU : PosOK Cα (Qof E.P) E.P.n ⟨c₆.nreg 81183, 0⟩ := by
      rw [z83, xe, s3.2.1]
      refine ⟨by show g' + c₄.nreg 81180 < (chainModel Cα).W.n; rw [Stretch.nα]; omega,
        ⟨le_of_eq rfl, by positivity, Nat.zero_le _⟩,
        fun _ => by show 6 ≤ g' + c₄.nreg 81180; omega⟩
    refine (FRS.ifT hc (sideCh_fs hE hB hI₆ (by rw [s6.2.2.2.1]; exact hP.hwf)
      (by rw [s6.2.2.2.1]; exact hP.hD) hWm (by rw [z53, z55]; exact hpA)
      (by rw [z54, z55]; exact hpB) hpU (by rw [rs, rh]; exact hpS)
      (by unfold ndK at hroom; omega))).mono (by omega) (fun c' ⟨sa, sb, fS⟩ => ?_)
    rw [z53, z54, z55, z83, rs, rh, z18] at sa
    rw [z53, z54, z55, z83, rs, rh, z19] at sb
    refine fin c' fS ?_ (fun _ => ⟨sa, sb⟩)
    by_cases hh : sideInArc ((chainModel Cα).key (Qof E.P) (Nα.chord k).lpos)
        ((chainModel Cα).key (Qof E.P) (Nα.chord k).rpos)
        ((chainModel Cα).key (Qof E.P) ⟨c₄.nreg 81183, 0⟩) ↔
      ((chainModel Cα).key (Qof E.P) (Nα.arc ((Nα.region (Nα.chord k).dn).arcs.getD 0 0)).s =
          (chainModel Cα).key (Qof E.P) (Nα.chord k).lpos ∨
        sideInArc ((chainModel Cα).key (Qof E.P) (Nα.chord k).lpos)
          ((chainModel Cα).key (Qof E.P) (Nα.chord k).rpos)
          ((chainModel Cα).key (Qof E.P) (Nα.arc ((Nα.region (Nα.chord k).dn).arcs.getD 0 0)).s))
    · exact Or.inl (sa hh)
    · exact Or.inr (sb hh)
  · have h0 : c₄.nreg 81181 ≠ 1 := fun h => hc (by omega)
    have okc : okB E.W c₆.nmem [.copyN 81150 81118] c₆.nreg := by
      simp only [okB, okI]; exact ⟨Or.inl (Or.inl ⟨by omega, by omega⟩), trivial⟩
    refine (FRS.ifF hc (FRS.block hB _ hI₆ okc)).mono (by simp)
      (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₆.nmem [.copyN 81150 81118] c₆.nreg q := fun q => by rw [h']
    have f' : ∀ q, q ≠ 81150 → c'.nreg q = c₆.nreg q := fun q hq => by
      rw [e']; simp [regB, regI, upd, hq]
    have v' : c'.nreg 81150 = (Nα.dnode k).lo := by
      rw [e']; simp only [regB, regI, upd, ite_true]; exact z18
    exact fin c' (fun q _ _ hq => f' q (fun e => hq (by omega_nf))) (Or.inl v')
      (fun h => absurd h h0)

end

end Restore

end Chazelle.Core
