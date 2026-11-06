module

public import Chazelle.MacT
public import Chazelle.Core.RestoreFEndP
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.RestoreTPos
public import Chazelle.Core.DownPhaseDrvBTopMain
public import Chazelle.Core.GranWt
public import Chazelle.Core.RestoreFTest

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
      (.ifLtN 81011 81181 sideCh ztoxw))))))

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
  hNα : IsNF ztbdc zti Nα
  hDec : ∃ dd, IsDecomp Nα dd
  hNW : NFWithin c₀.nmem Bα ztdq Nα
  hD : ChainDescAt c₀.nmem Dα zti Hα Cα
  hwf : ChainWF E.P ztdq c₀.nmem Dα
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
      let k' := fun (x : WPos) => (chainModel Cα).key zti x
      let kA := k' (Nα.chord k).lpos
      let kB := k' (Nα.chord k).rpos
      let kU := k' ztfwe
      let j := (Nα.region (Nα.chord k).dn).arcs.getD 0 0
      let kS := k' (Nα.arc j).s
      (ztbbf → c'.nreg 81150 = (Nα.dnode k).lo) ∧
      (¬ (sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) →
        c'.nreg 81150 = (Nα.dnode k).hi)) ∧
    c'.nreg 81007 = c₄.nreg 81007
theorem node_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs c g g' L Dα Bα)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    {k : ℕ} (hx : c.nreg 81150 = 2 * k) (hk : k < Nα.nChords)
    (hroom : c.nreg ALLOC + ndK E ztckt ≤ E.W) :
    FRS B E.P E.W c₀ (nodeS E.sT) c (ndK E ztckt) (fun c' => FWin E c' ∧
      ztfjg ∧
      ztfn ∧
      ztcur ∧
      NodeRaw E c₀ Cα Nα k c c') := by
  zuqv
  zuglu
  zufvq
  zuln
  zubkd

  zuicf
  have hdec := hDec.1
  obtain ⟨-, -, -, regα, h1α, h2α, h3α, h4α, -, hhα, -⟩ := id hP.hNα
  have hregsα : NFRegs _ _ Nα regα := ⟨h1α, h2α, h3α, h4α⟩
  have hneα : (Nα.F ztbdc zti).Nonempty := ⟨_, _, Dec.chord_mem hk, rfl⟩
  have hdn := (h2α k hk).2.1
  obtain ⟨har, hj, -⟩ := region_arc hMα hP.hNα hregsα hneα hdn
  have hpS := (arc_posOK hsimp hP.hNα hneα hj).1
  have hhn : (Nα.chord k).h < E.P.n := by
    have := hhα k hk; rwa [show (Qof E.P).n = E.P.n from shear_n _ _] at this
  have hnW : E.P.n ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  have hyc : ∀ z ∈ (Nα.chord k).toSet ztbdc zti, z.2 = ((Qof E.P).vtx (Nα.chord k).h).2 :=
    fun z hz => by unfold CRec.toSet Visibility.hseg at hz; simp_all
  zuiyc
  have hL0 := hS.hL0
  have hLn := hS.hLn
  have h6 := hS.h6
  -- the chord
  refine (FRS.seq (K₂ := 2 * efK E + wsK + 10 + 25 + scK + 4) (chordLoad_fs hE hB hI (N := Nα)
    ztgfz hx by_omega by_grind
    ztdhb) (fun c₁ hI₁ hA₁ ⟨u21, u52, u53, u54, u55, u56, f₁⟩ => ?_)).mono
    (by unfold ndK; omega) ztb
  rw [show 2 * k / 2 = k by omega] at u21 u52 u53 u54 u55 u56
  have F1 := f₁
  have sT : ∀ {x y : Config}, SRegs x g g' L Dα Bα →
      (∀ q, 81130 ≤ q → q ≤ 81135 → y.nreg q = x.nreg q) → SRegs y g g' L Dα Bα := by
    intro x y hs h
    obtain ⟨x0, x1, x2, x3, x4, x5⟩ := hs
    exact ⟨by_grind, by_grind,
      by grind, by_grind,
      by grind, by_grind⟩
  have s1 : SRegs c₁ g g' L Dα Bα :=
    sT ⟨r30, r31, r32, r33, r34, r35⟩ by_grind
  zuizp
  -- the candidate facts of an end
  have candE : ∀ (cx : Config) (p pv : ℕ) (tv : ℝ), SRegs cx g g' L Dα Bα → cx.nreg p = pv →
      cx.nreg 81152 = (Nα.chord k).h → cx.nreg 81155 = (Nα.chord k).h + 1 →
      SideAttach (chainModel Cα).W ((Nα.chord k).toSet ztbdc zti) pv
        ((chainModel Cα).param zti ztlwk) →
      PosOK Cα zti E.P.n ztlwk →
      cx.nreg 81131 ≤ cx.nreg p → cx.nreg p < cx.nreg 81135 →
      InRange c₀ (eMof E cx p) → ∀ σb, σb ≤ 1 →
        CandOK E ⟨eMof E cx p, endCode Cα zti (cx.nreg p) (cx.nreg 81155)⟩
          (cx.nreg 81152) σb := by
    intro cx p pv tv ⟨x30, x31, x32, x33, x34, x35⟩ xp x52 x55 hAt hpo a b hr σb hσb
    rw [x31, xp] at a; rw [x35, xp] at b
    obtain ⟨d, rfl⟩ : ∃ d, pv = g' + d := ⟨pv - g', by_omega⟩
    have hd : d < L := by_omega
    unfold eMof at hr ⊢
    rw [x30, x31, xp, show g' + d - g' = d by omega] at hr ⊢
    rw [x52, x55]
    exact end_cand hE hS hd hpo hAt hyc hr hσb
  have hgn := hS.hg
  have hWm := hP.hWm
  have hJ₁ : c₁.nreg 81140 < E.M.W.n ∧
      ProperPos E.M zti E.P.n ztrbs := by
    rw [F1 81140 by_omega by_omega, F1 81141 by_omega by_omega]; exact hJ
  have fl₁ : ztmve := F1 _ by_omega by_omega
  -- the left end
  refine (FRS.seq (K₂ := efK E + wsK + 10 + 25 + scK + 4) (endFull_fs hE hB hBT hI₁ hw₁
    (s := 81160) (p := 81153) (σ := 1) ztfm ztp le_rfl
    (by zupap; exact hP.hwf) (by zupap; exact hP.hD) hWm
    (by rw [s1.2.1]; exact h6) (by rw [s1.1]; omega) (by rw [s1.2.2.2.2.2, s1.2.1]; omega)
    (by rw [u53, u55]; tauto) (candE c₁ 81153 _ 0 s1 u53 u52 u55 hat.1 hpA) hJ₁
    ztdhb) (fun c₂ hI₂ hA₂ ⟨hw₂, f₂, m₂, R₂⟩ => ?_)).mono
    by_omega ztb
  have e2 : zthpb :=
    fun q a b => f₂ q by_omega by_omega ztcml
  have s2 := sT s1 (fun q a b => e2 q by_omega by_omega)
  have v52 : c₂.nreg 81152 = (Nα.chord k).h := by rw [e2 _ by_norm_num by_norm_num, u52]
  have v53 : ztoqu := by rw [e2 _ by_norm_num by_norm_num, u53]
  have v54 : ztoqv := by rw [e2 _ by_norm_num by_norm_num, u54]
  have v55 : ztlya := by
    rw [e2 _ by_norm_num by_norm_num, u55]
  have v56 : c₂.nreg 81156 = (Nα.chord k).dn := by rw [e2 _ by_norm_num by_norm_num, u56]
  have v21 : c₂.nreg 81121 = k := by rw [e2 _ by_norm_num by_norm_num, u21]
  have hJ₂ : c₂.nreg 81140 < E.M.W.n ∧
      ProperPos E.M zti E.P.n ztrbw := by
    rw [e2 81140 by_norm_num by_norm_num, e2 81141 by_norm_num by_norm_num]; omega
  -- the right end
  refine (FRS.seq (K₂ := wsK + 10 + 25 + scK + 4) (endFull_fs hE hB hBT hI₂ hw₂
    (s := 81170) (p := 81154) (σ := 0) ztfm ztbt by_norm_num
    (by zupaq; exact hP.hwf) (by zupaq; exact hP.hD) hWm
    (by rw [s2.2.1]; exact h6) (by rw [s2.1]; omega) (by rw [s2.2.2.2.2.2, s2.2.1]; omega)
    (by rw [v54, v55]; tauto) (candE c₂ 81154 _ 0 s2 v54 v52 v55 hat.2 hpB) hJ₂
    ztdhb) (fun c₃ hI₃ hA₃ ⟨hw₃, f₃, m₃, R₃⟩ => ?_)).mono
    by_omega ztb
  have e3 : zthpc :=
    fun q a b => f₃ q by_omega by_omega ztcml
  have s3 := sT s2 (fun q a b => e3 q by_omega by_omega)
  have w53 : ztoqy := by rw [e3 _ by_norm_num by_norm_num, v53]
  have w54 : ztoqz := by rw [e3 _ by_norm_num by_norm_num, v54]
  have w55 : c₃.nreg 81155 = (Nα.chord k).h + 1 := by
    rw [e3 _ by_norm_num by_norm_num, v55]
  have w56 : c₃.nreg 81156 = (Nα.chord k).dn := by rw [e3 _ by_norm_num by_norm_num, v56]
  have w21 : c₃.nreg 81121 = k := by rw [e3 _ by_norm_num by_norm_num, v21]
  have hpA' : c₃.nreg 81160 = 1 → g' ≤ c₃.nreg 81153 ∧ c₃.nreg 81153 - g' < L := by
    zudqd
    rw [e3 _ by_norm_num by_norm_num] at h1
    obtain ⟨a, b, -⟩ := R₂.1.2.mp h1
    rw [s1.2.1, u53] at a; rw [s1.2.2.2.2.2, u53] at b; omega
  have hpB' : c₃.nreg 81170 = 1 → g' ≤ c₃.nreg 81154 ∧ c₃.nreg 81154 - g' < L := by
    zudqd
    obtain ⟨a, b, -⟩ := R₃.1.2.mp h1
    rw [s2.2.1, v54] at a; rw [s2.2.2.2.2.2, v54] at b; omega
  -- the witness
  refine (FRS.seq (K₂ := 10 + 25 + scK + 4) (wsel_fs hE hB hI₃
    (R₂.2.2.2.2.2.2.congr (fun j hj => e3 _ by_omega by_omega)) R₃.2.2.2.2.2.2
    (by rw [s3.1]; omega) ztnul ztfpr
    ztnul ztfpr
    ztfpr
    ztdhb) (fun c₄ hI₄ hA₄ ⟨x81, xC, xAll, f₄⟩ => ?_)).mono
    by_omega ztb
  have e4 : ∀ q, 81000 ≤ q → q ≤ 81179 → c₄.nreg q = c₃.nreg q :=
    fun q a b => f₄ q by_omega by_omega ztbkm
  have s4 := sT s3 (fun q a b => e4 q by_omega by_omega)
  have x21 : c₄.nreg 81121 = k := by rw [e4 _ by_norm_num by_norm_num, w21]
  -- the children
  refine (FRS.seq (K₂ := 25 + scK + 4) (kidLoad_fs hE hB hI₄ (N := Nα)
    (by rw [s4.2.2.2.2.1]; exact hP.hNW) by_omega)
    (fun c₅ hI₅ hA₅ ⟨kl, kh, f₅⟩ => ?_)).mono by_omega (fun _ h => h)
  rw [x21] at kl kh
  have s5 := sT s4 (fun q a b => f₅ q by_omega by_omega by_omega)
  have y56 : c₅.nreg 81156 = (Nα.chord k).dn := by
    rw [f₅ _ by_norm_num by_norm_num by_norm_num, e4 _ by_norm_num by_norm_num, w56]
  -- the reference arc
  refine (FRS.seq (K₂ := scK + 4) (refLoad_fs hE hB hI₅ (N := Nα)
    (by rw [s5.2.2.2.2.1]; exact hP.hNW) by_omega (by rw [y56]; omega)
    (by rw [y56]; exact hj)) (fun c₆ hI₆ hA₆ ⟨rs, rh, f₆⟩ => ?_)).mono by_omega (fun _ h => h)
  rw [y56] at rs rh
  have e64 : ∀ q, 81120 ≤ q → q < 83000 → c₆.nreg q = c₄.nreg q := fun q a b => by
    rw [f₆ q by_omega by_omega by_omega by_omega, f₅ q by_omega by_omega by_omega]
  have e6 : ∀ q, 81120 ≤ q → q ≤ 81179 → c₆.nreg q = c₃.nreg q := fun q a b => by
    rw [e64 q a by_omega, e4 q by_omega b]
  have s6 := sT s5 (fun q a b => f₆ q by_omega by_omega by_omega by_omega)
  have z81 : c₆.nreg 81181 = c₄.nreg 81181 := e64 _ by_norm_num by_norm_num
  have z83 : c₆.nreg 81183 = c₄.nreg 81183 := e64 _ by_norm_num by_norm_num
  have z11 : c₆.nreg 81011 = 0 := by rw [hI₆.hin _ ztbc, hE.k0]
  have z53 : c₆.nreg 81153 = (Nα.chord k).lp := by rw [e6 _ by_norm_num by_norm_num, w53]
  have z54 : c₆.nreg 81154 = (Nα.chord k).rp := by rw [e6 _ by_norm_num by_norm_num, w54]
  have z55 : c₆.nreg 81155 = (Nα.chord k).h + 1 := by
    rw [e6 _ by_norm_num by_norm_num, w55]
  have z18 : c₆.nreg 81118 = (Nα.dnode k).lo := by
    rw [f₆ _ by_norm_num by_norm_num by_norm_num by_norm_num, kl]
  have z19 : c₆.nreg 81119 = (Nα.dnode k).hi := by
    rw [f₆ _ by_norm_num by_norm_num by_norm_num by_norm_num, kh]
  have z07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c₆.nreg q = c₃.nreg q := fun q a b => by
    rw [f₆ q by_omega by_omega by_omega by_omega, f₅ q by_omega by_omega by_omega,
      e4 q by_omega by_omega]
  -- the end
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ ScW q → c'.nreg q = c₆.nreg q) →
      ztcur →
      (c₄.nreg 81181 = 1 →
        let k' := fun (x : WPos) => (chainModel Cα).key zti x
        let kA := k' (Nα.chord k).lpos
        let kB := k' (Nα.chord k).rpos
        let kU := k' ztfwe
        let j := (Nα.region (Nα.chord k).dn).arcs.getD 0 0
        let kS := k' (Nα.arc j).s
        (ztbbf →
          c'.nreg 81150 = (Nα.dnode k).lo) ∧
        (¬ (sideInArc kA kB kU ↔ (kS = kA ∨ sideInArc kA kB kS)) →
          c'.nreg 81150 = (Nα.dnode k).hi)) →
      FWin E c' ∧ ztfjg ∧
      ztfn ∧
      ztcur ∧
      NodeRaw E c₀ Cα Nα k c c' := by
    intro c' hf h50 hch
    have g07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c'.nreg q = c₃.nreg q := fun q a b => by
      rw [hf q by_omega by_omega ztozg, z07 q a b]
    have fl' : c'.nreg 81007 = c₄.nreg 81007 := by
      rw [g07 _ by_norm_num by_norm_num, e4 _ by_norm_num by_norm_num]
    refine ⟨hw₃.congr' g07, fun q a b hq => ?_, fun h1 => ?_, h50,
      ⟨c₁, c₂, c₃, c₄, ⟨u52, u53, u54, u55, fun q a b => F1 q by_omega by_omega⟩, fl₁, R₂, f₂,
        m₂, hw₂, R₃, f₃, m₃, x81, xC, xAll, e4 _ by_norm_num by_norm_num, hch, fl'⟩⟩
    · unfold NodeW KeyW VertW at hq
      rw [hf q by_omega by_omega ztozg,
        f₆ q by_omega by_omega by_omega by_omega, f₅ q by_omega by_omega by_omega,
        f₄ q by_omega by_omega ztbkm,
        f₃ q a b ztcml, f₂ q a b ztcml,
        F1 q by_omega by_omega]
    · rw [g07 _ by_norm_num by_norm_num]; exact m₃ (m₂ by_omega)
  by_cases hc : c₆.nreg 81011 < c₆.nreg 81181
  · have h1 : c₄.nreg 81181 = 1 := by_omega
    obtain ⟨xu, xe, -⟩ := xC h1
    have hu : ztusy := by have := xu.1; rw [s3.2.2.1] at this; omega
    have hpU : PosOK Cα zti E.P.n ⟨c₆.nreg 81183, 0⟩ := by
      rw [z83, xe, s3.2.1]
      refine ⟨by show g' + c₄.nreg 81180 < (chainModel Cα).W.n; zunks; omega,
        ⟨le_of_eq rfl, by_simp, Nat.zero_le _⟩,
        fun _ => by show 6 ≤ g' + c₄.nreg 81180; omega⟩
    refine (FRS.ifT hc (sideCh_fs hE hB hI₆ (by zupar; exact hP.hwf)
      (by zupar; exact hP.hD) hWm (by rw [z53, z55]; tauto)
      (by rw [z54, z55]; tauto) hpU (by rw [rs, rh]; omega)
      ztdhb)).mono by_omega (fun c' ⟨sa, sb, fS⟩ => ?_)
    rw [z53, z54, z55, z83, rs, rh, z18] at sa
    rw [z53, z54, z55, z83, rs, rh, z19] at sb
    refine fin c' fS ?_ (fun _ => ⟨sa, sb⟩)
    by_cases hh : sideInArc ztwmh
        ztwmi
        ztymx ↔
      ((chainModel Cα).key zti (Nα.arc ztcrs).s =
          (chainModel Cα).key zti (Nα.chord k).lpos ∨
        sideInArc ztwmh
          ztwmi
          ztxtu)
    · exact Or.inl (sa hh)
    · exact Or.inr (sb hh)
  · have h0 : c₄.nreg 81181 ≠ 1 := fun h => hc by_omega
    have okc : okB E.W c₆.nmem [.copyN 81150 81118] c₆.nreg := by
      zurp
    refine (FRS.ifF hc (FRS.block hB _ hI₆ okc)).mono by_simp
      zthi
    have e' : ∀ q, c'.nreg q = regB c₆.nmem [.copyN 81150 81118] c₆.nreg q := fun q => by zvmxl
    have f' : ∀ q, q ≠ 81150 → c'.nreg q = c₆.nreg q := fun q hq => by
      zubls
    have v' : c'.nreg 81150 = (Nα.dnode k).lo := by
      zukqq
    exact fin c' (fun q _ _ hq => f' q (fun e => hq (by unfold ScW; omega))) (Or.inl v')
      by_omega
end
end Restore
end Chazelle.Core
section
set_option hygiene false
local macro "zqbel" : tactic => `(tactic| (have hX0 : (0 : ℝ) < dX := by exact_mod_cast hD.hX0
                                           have hXL : (dX : ℝ) < L := by exact_mod_cast hD.hXL))
local macro "zqbem" : tactic => `(tactic| exact ⟨α, h0, h1, h3, fun _ _ => h4⟩)
local macro "zqben" : tactic => `(tactic| obtain ⟨-, -, -, bit7, -⟩ := stA a b)
local macro "zqbeo" : tactic => `(tactic| obtain ⟨-, -, -, bit7, -⟩ := stB a b)
set_option hygiene true

/-!
# WP-E, the search: the decision at a node of the descent

`DescGood`: the facts of a stretch of a kind-1 piece that the descent's completeness reads (the
region and its arcs `A_i ∋` stretch, `A_j`, the good vertex `X` at offset `dX` with its good
chord, the target region `T` of the piece's normal form faced just after `X`).
`end_info`: what a node end test that did not succeed tells (in offsets).
`node_dec`: after a node run that did not succeed, the chosen child is above `T`.
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp)
open WalkEmbed (off off_nonneg off_lt off_key off_key')

/-- A vertex of the side walk of a chain inside the open box is a point of the chain. -/
theorem walk_vtx_box (C : Chain) (β : Bool) {e : ℕ} (he : e < (C.sideWalk β).n)
    (hb : |((C.sideWalk β).vtx e).2| < C.radius) : (C.sideWalk β).vtx e ∈ C.set := by
  rw [Chain.sideWalk_n] at he
  zuiza
  by_cases h6 : 6 ≤ e
  · zugqb
    zukou
    exact C.vertex_mem_set ztdfj
  · exfalso
    replace hb : True ∧ |((C.sideWalk β).vtx e).2| < C.radius := by_simp_all
    interval_cases e
    · rw [C.sideWalk_vtx_zero] at hb
      have := hb.2; simp only [Chain.slitTop] at this; grind
    · rw [C.sideWalk_vtx_one] at hb
      grind
    · rw [C.sideWalk_vtx_two] at hb
      grind
    · rw [C.sideWalk_vtx_three] at hb
      grind
    · rw [C.sideWalk_vtx_four] at hb
      grind
    · rw [C.sideWalk_vtx_five] at hb
      have := hb.2; simp only [Chain.slitTop] at this; grind
variable {E : FEnv} {c₀ : Config} {Cα : Chain} {g g' L : ℕ}

/-- **A far point inside the box is in the vertex range** (or not a vertex). -/
theorem far_range (hE : FGood E c₀) {far : WPos} (hfe : far.edge < E.M.W.n)
    (hb : ∀ C : Chain, E.M = chainModel C → |(E.M.pos zti far).2| < C.radius) :
    0 < far.hgt ∨ c₀.nreg 81021 ≤ far.edge := by
  rcases Nat.eq_zero_or_pos far.hgt with h0 | h0
  · right
    refine (hE.hvc _ hfe (fun C hC => ?_)).1
    have e : far = ztugo := by zuosa
    have hb' := hb C hC
    zvmwe at hb'
    have hv : ∀ M' : Model, M'.pos zti ztugo = M'.W.vtx far.edge := fun M' => by
      rw [pos_eq_sidePt]; show sidePt M'.W far.edge 0 = _
      zufdr
    zvmyq at hb' ⊢
    revert hb' hfe
    rw [hC]
    intro hfe hb'
    exact walk_vtx_box C _ hfe hb'
  omega

/-- The host parameter and point of a node chord end's candidate. -/
theorem end_param (hS : Stretch E.M Cα g g' L) {d h : ℕ} (hd : d < L)
    (hpe : PosOK Cα zti E.P.n ztbfm) :
    E.M.param zti ztwmo =
      (chainModel Cα).param zti ztbfm ∧
    E.M.pos zti ztwmo =
      (chainModel Cα).pos zti ztbfm := by
  set t := (chainModel Cα).param _ ztbfm with ht
  obtain ⟨-, ⟨ht0, -, -⟩, -⟩ := hpe
  zuecw

  · simp_all
  · have h0 : ztbhh := by
      zuilh
    have e : (chainModel Cα).param zti ztrcl =
        (chainModel Cα).param zti ztbfm := by
      simp_all
    exact ztmqd

/-- The code of an end is `0` iff its parameter is `0`. -/
theorem endCode_zero {p h : ℕ} :
    endCode Cα zti p ztgn = 0 ↔ ¬ 0 < (chainModel Cα).param zti ztdw := by
  unfold endCode
  zulss
  · zuili
  · zuili
theorem nat_add_frac {a b : ℕ} {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (ht0' : 0 ≤ t')
    (ht1' : t' < 1) (h : (a : ℝ) + t = b + t') : a = b ∧ t = t' := by
  have h1 : (a : ℝ) < b + 1 := by_linarith
  have h2 : (b : ℝ) < a + 1 := by_linarith
  have h1' : a < b + 1 := by exact_mod_cast h1
  have h2' : b < a + 1 := by exact_mod_cast h2
  grind

/-- **The facts of a stretch of a kind-1 piece** that the completeness of the descent reads:
the region `reg E.r` with the arc `A_i = (ai, bi)` containing the open stretch and the target arc
`A_j = (aj, bj)`, the good vertex `X` at the offset `dX` with its good chord, and the region `T`
of the piece's normal form faced just after `X`. -/
structure DescGood (E : FEnv) (c₀ : Config) (Cα : Chain) (Nα : NF) (g g' L : ℕ)
    (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ) : Prop where
  hregs : NFRegs E.M zti E.N reg
  hch : (E.N.region E.r).chords ≠ []
  hAi : E.M.IsArc ztwky ztbuw ai bi
  hAj : E.M.IsArc ztwky ztbuw aj bj
  hij : ai ≠ aj
  hAin : ∀ d, d < L → ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < (d : ℝ) + t →
    sideInArc ai bi (((ztbe % E.M.W.n : ℕ) : ℝ) + t)
  hcnt : ∀ d, d < L → InRange c₀ ztxlk
  hsetD : ∀ x ∈ Cα.set, x ∉ E.M.D
  hinB : ∀ C : Chain, E.M = chainModel C → Cα.set ⊆ C.set
  hX0 : 0 < dX
  hXL : dX < L
  hgX : ∃ σb, σb ≤ 1 ∧ GoodAt E reg ztxlm σb
  hXc : ∃ (ex : Set Point) (px' : ℕ) (tx' : ℝ), ex ∈ E.M.Adm ∧
    SideAttach E.M.W ex ztxlm 0 ∧ SideAttach E.M.W ex px' tx' ∧
    sidePt E.M.W ztxlm 0 ≠ sidePt E.M.W px' tx' ∧
    ClosedArc ai bi ztwx ∧ ClosedArc aj bj ztdvt ∧
    CountOK E.M ztwky ztbuw ztwx
      ztdvt
  hregsα : NFRegs ztbdc zti Nα regα
  hRT : ∃ D, Dec.RecTree Nα D
  hT : T < Nα.nRegions
  hfT : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (chainModel Cα).Faces zttks ε (regα T)

/-- **What a node end test that did not succeed tells**, in offsets of the stretch (`dE`: the
offset of the end in `Cα`'s walk). -/
theorem end_info (hE : FGood E c₀) (hS : Stretch E.M Cα g g' L) (hGα : GoodModel ztbdc)
    {Nα : NF} {reg : ℕ → Set Point} {ai bi aj bj : ℝ} {dX : ℕ} {regα : ℕ → Set Point} {T : ℕ}
    (hD : DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T)
    {cs c' : Config} {s p σ : ℕ} (hR : EndRes E c₀ Cα s p σ cs c')
    (h30 : cs.nreg 81130 = g) (h31 : cs.nreg 81131 = g') (h35 : cs.nreg 81135 = g' + L)
    {pE h : ℕ} (hp : cs.nreg p = pE) (h55 : cs.nreg 81155 = h + 1)
    (hpe : PosOK Cα zti E.P.n ztrdx)
    {tE : ℝ} (htE : tE = (chainModel Cα).param zti ztrdx)
    {c : Set Point} (hcA : c ∈ (chainModel Cα).Adm)
    (hAE : SideAttach (chainModel Cα).W c pE tE)
    {pO : ℕ} {tO : ℝ} (hAO : SideAttach (chainModel Cα).W c pO tO)
    {L₀ : ℝ} (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment ztcwk
      ztznr)
    (hoO : rayPt ztcwk ztjtz L₀ = sidePt (chainModel Cα).W pO tO)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztcwk
      ztznr s ∈ Cα.dom)
    (hJ : aj = E.M.key zti ztrbo)
    (hJr : 0 < cs.nreg 81141 ∨ c₀.nreg 81021 ≤ cs.nreg 81140)
    (hf0 : cs.nreg 81007 = 0) (hf1 : c'.nreg 81007 ≠ 1) :
    (c'.nreg s = 1 ↔ (0 < off (chainModel Cα).W.n g' ztcaq ∧
      off (chainModel Cα).W.n g' ztcaq < L)) ∧
    off (chainModel Cα).W.n g' ztcaq ≠ dX ∧
    (0 < off (chainModel Cα).W.n g' ztcaq → off (chainModel Cα).W.n g' ztcaq < L →
      g' ≤ pE ∧ c'.nreg ztfz = 1 ∧ c'.nreg ztbk = (g + ztoef) % E.M.W.n ∧
      SweepPrim.BitIs c' ztyd (0 < tE) ∧
      ∃ α : ℝ, 0 ≤ α ∧ (0 < α → α < L → α = off (chainModel Cα).W.n g' ztkcd) ∧
        (off (chainModel Cα).W.n g' ztkcd ≠ dX →
          GEnd L ztyju α (c'.nreg ztsk = 1) dX ∧
          ∀ u, u < L → (sideInArc (E.M.key zti ⟨c'.nreg ztbk, c'.nreg ztfp⟩)
            ztxdq
            ((ztesw % E.M.W.n : ℕ) : ℝ) ↔
            sideInArc ztyju α u))) := by
  zucmh
  zuclv
  zuhel
  have hσ' := dirOf_pm σ
  have hpe' := hpe
  obtain ⟨hpn, ⟨ht0, ht1, -⟩, -⟩ := hpe'
  replace hpn : pE < (chainModel Cα).W.n := hpn
  rw [← htE] at ht0 ht1
  obtain ⟨Rb, Rp, R3, R4, R5, R6, -⟩ := hR
  rw [h31, hp, h35, h55, key_pz, ← htE] at Rb
  have hin : c'.nreg s = 1 ↔ (0 < off (chainModel Cα).W.n g' ztcaq ∧
      off (chainModel Cα).W.n g' ztcaq < L) := by
    rw [Rb.2]; exact inE_iff hS hpn ht0 ht1
  -- the end in the stretch
  have hst : 0 < off (chainModel Cα).W.n g' ztcaq → off (chainModel Cα).W.n g' ztcaq < L →
      ∃ d, pE = g' + d ∧ d < L ∧ (tE = 0 → 1 ≤ d) ∧ off (chainModel Cα).W.n g' ztcaq = d + tE ∧
        c'.nreg s = 1 ∧ eMof E cs p = ztbe % E.M.W.n := by
    intro a b
    obtain ⟨i1, i2, i3⟩ := (inE_iff hS hpn ht0 ht1).2 ztbqy
    refine ⟨pE - g', by_omega, by_omega, fun h0 => by_grind, ?_,
      by grind, by unfold eMof; grind⟩
    have e := endα_off hS (d := pE - g') by_omega ht0 ht1
    rw [show g' + ztoef = pE by omega] at e
    zulez
  -- the end is not the good vertex
  have hcode : ∀ d, pE = g' + d → tE = 0 → endCode Cα zti (cs.nreg p) (cs.nreg 81155) = 0 :=
    fun d hd h0 => by
      rw [hp, h55]; exact endCode_zero.2 by_grind
  have hne : off (chainModel Cα).W.n g' ztcaq ≠ dX := by
    zuetb
    zqbel
    obtain ⟨d, rfl, hd, -, ho, hs1, heM⟩ := hst by_grind by_grind
    rw [ho] at hx
    obtain ⟨rfl, h0⟩ := nat_add_frac (a := d) (b := dX) ht0 ht1 le_rfl one_pos by_grind
    obtain ⟨σb, hσb, hg⟩ := hD.hgX
    exact hf1 (R3 hs1 ztktm reg hD.hregs hD.hch by_grind σb hσb
      by_grind)
  refine ⟨hin, hne, fun a b => ?_⟩
  obtain ⟨d, rfl, hd, htd, ho, hs1, heM⟩ := hst a b
  have hdn : d < E.M.W.n := by have := hS.hLn; omega
  have hdt : (0 : ℝ) < d + tE := by
    grind
  obtain ⟨ct, ct', hTO, i60, i61, i63, e3, e4, ev, efl⟩ := R4 hs1 ztktm hf0
  rw [heM] at i60
  rw [hp, h55] at i61
  have hpar := end_param hS hd hpe
  rw [← htE] at hpar
  have hx : (⟨ct.nreg 81060, ct.nreg 81061⟩ : WPos) =
      ⟨ztbe % E.M.W.n, endCode Cα zti zthr ztgn⟩ := by_grind
  obtain ⟨-, -, hcl⟩ := hTO
  obtain ⟨-, hex, hcomp⟩ := hcl reg hD.hregs
  rw [hx, i63] at hex hcomp
  have hz : E.M.pos zti ztwmo =
      sidePt E.M.W ztxlk tE := by
    show sidePt E.M.W ztxlk _ = _
    zumnx
  have hkx : E.M.key zti ztwmo =
      ((ztbe % E.M.W.n : ℕ) : ℝ) + tE := by
    show _ + _ = _
    zumnx
  rw [hz, hpar.1] at hex hcomp
  have hza : sidePt E.M.W ztxlk tE = sidePt (chainModel Cα).W zthr tE := by
    rw [hS.hA.sidePt_eq hd tE, hS.mod' hd.le]
  rw [← hza] at hceq hoO hkopen
  have haC : sidePt E.M.W _ tE ∈ Cα.set := hS.memM hd ht0 ht1
  have hAM : SideAttach E.M.W c _ tE :=
    (hS.hA.sideAttach_iff hn by_omega hd htd c).2
      (by rw [hS.mod' hd.le]; omega)
  have hsec := attach_ray_left hAM hσ' hL₀ hceq
  obtain ⟨T', hT', hdom', hout', hadm', hnS', hsub'⟩ := inner_exit hE.hGM hE.hNF.1
    zttmc hD.hAi zthp ht0 ht1 ztoac hσ' hsec
    (fun C hC => C.snd_le_top_of_mem_set ztrrj)
  obtain ⟨h10, h11⟩ := hcomp hsec hD.hch T' hT' hdom' hout' hadm' hnS' hsub'
  obtain ⟨T'', hT'', hstr, hposf, hfe, hfp, hadm'', hA1, hA2, hiff⟩ := hex h10 h11
  have hdomM : ∀ t, 0 < t → t < T'' →
      rayPt _ _ t ∈ E.M.D :=
    fun t h0 h1 => (Chazelle.Chain.regionsIn_subset zttmc ztrse).1
  -- valid
  have hrange := far_range hE hfe (fun C hC => by
    rw [hposf, rayPt_snd]; exact (C.set_subset_box ztrrj).2)
  have hv : c'.nreg _ = 1 := ev.2 ⟨h10, h11, hrange⟩
  have hbad : ¬ CountOK E.M _ _
      _
      ((ct'.nreg 83012 : ℝ) + E.M.param _ ztgoq) :=
    fun hc => hf1 (efl (hiff.2 (by zuofz; exact hc)))
  obtain ⟨α0, αarr⟩ := arrival_off hS ztwht hcA hAO haC hσ' hL₀ hceq hoO hkopen
    hD.hsetD hT'' hdomM hposf hA2
  obtain ⟨Rp1, Rp2, Rp7⟩ := Rp hs1
  rw [heM] at Rp1
  rw [hp, h55] at Rp2
  rw [hp, h55, key_pz, ← htE] at Rp7
  refine ⟨by_omega, hv, by rw [Rp1, show g' + d - g' = d by omega], Rp7, off E.M.W.n g ((ct'.nreg 83012 : ℝ) +
    E.M.param _ ztgoq), α0, αarr,
    fun hOX => ?_⟩
  obtain ⟨ex, px', tx', hex', hX, hX', hXX', hkxa, hkx', hgood⟩ := hD.hXc
  have hXn : dX < E.M.W.n := by have := hD.hXL; have := hS.hLn; omega
  have hxa : ztwx ≠ ((ztbe % E.M.W.n : ℕ) : ℝ) + tE := by
    zufhz
    obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos ht0 ht1 he
    have := WalkEmbed.add_mod_inj hXn hdn e1
    zumo
    exact hne (by rw [ho, ← e2, add_zero])
  have hxa' : ztwx ≠
      (ct'.nreg 83012 : ℝ) + E.M.param zti ztgoq := by
    zufhz
    obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos hfp.1 hfp.2.1 he
    have hα : off E.M.W.n g ((ct'.nreg 83012 : ℝ) +
        E.M.param zti ztgoq) = dX := by
      rw [← he, off_key hS.hg hXn le_rfl one_pos, add_zero]
    zqbel
    exact hOX ((αarr ztnub ztnub).symm.trans hα)
  obtain ⟨-, -, hside, hrot⟩ := end_gend hS ztwht hM hE.hNF.1.2.1 hE.hNF.1.1
    (family_ne hE.hNF hE.hr hD.hch) hD.hAi hD.hAj hD.hij hcA hAO hd ht0 ht1 hdt hσ' hL₀ hceq hoO
    hkopen hD.hsetD hT'' hdomM hposf hadm'' hA1 hA2 ztoac hbad hex'
    hD.hXL hX hX' hXX' hkxa hkx' hgood hxa hxa'
  rw [e3, e4, heM, hp, h55, ← hJ, hkx] at R6
  refine ⟨fun _ => by rw [ho]; exact hside.trans (R6 hv hJr).symm, fun u hu => ?_⟩
  rw [Rp1, Rp2, hkx, e3, e4, ho]
  exact hrot u hu
theorem dirOf1 : dirOf 1 = 1 := by_rfl
theorem dirOf0 : dirOf 0 = -1 := by_rfl

/-- **The decision at a node**: after a node run at chord `k` that set no success, the chosen
child is above the target region `T` (which is below the node). -/
theorem node_dec (hE : FGood E c₀) {Hα : Host} {Nα : NF} {Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) {c c' : Config} (hR : SRegs c g g' L Dα Bα)
    {reg : ℕ → Set Point} {ai bi aj bj : ℝ} {dX : ℕ} {regα : ℕ → Set Point} {T : ℕ}
    (hD : DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T)
    (hJ : aj = E.M.key zti ztke)
    (hJr : 0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) (hw : FWin E c)
    {k : ℕ} (hk : k < Nα.nChords) (hb : Nα.Below ztckt T)
    (hraw : NodeRaw E c₀ Cα Nα k c c') (hf : c'.nreg 81007 = 0) :
    Nα.Below (c'.nreg 81150) T := by
  obtain ⟨c₁, c₂, c₃, c₄, ⟨u52, u53, u54, u55, F1⟩, fl₁, R₂, f₂, m₂, hw₂, R₃, f₃, m₃, x81, xC, xAll,
    fl₄, hch, fl'⟩ := hraw
  zuqv
  zuglu
  zucmh
  zuerw
  zuiyc
  zuln
  zubkd

  -- flags
  have f4 : c₄.nreg 81007 = 0 := by_omega
  have f3 : c₃.nreg 81007 = 0 := by_omega
  have f2 : ztpni := by
    have := hw₂.1
    grind
  have f1 : c₁.nreg 81007 = 0 := by
    have := hw.1
    grind
  -- registers
  have g2 : zthpb :=
    fun q a b => f₂ q by_omega by_omega ztcml
  have g3 : zthpc :=
    fun q a b => f₃ q by_omega by_omega ztcml
  have a30 : c₁.nreg 81130 = g := by_grind
  have a31 : ztuql := by_grind
  have a32 : c₁.nreg 81132 = L := by_grind
  have a35 : c₁.nreg 81135 = g' + L := by_grind
  have a40 : ztmvf := by_grind
  have a41 : ztmvg := by_grind
  have b30 : c₂.nreg 81130 = g := by_grind
  have b31 : zturk := by_grind
  have b32 : c₂.nreg 81132 = L := by_grind
  have b35 : c₂.nreg 81135 = g' + L := by_grind
  have b40 : c₂.nreg 81140 = c.nreg 81140 := by_grind
  have b41 : c₂.nreg 81141 = c.nreg 81141 := by_grind
  have b53 : ztoqu := by_grind
  have b54 : ztoqv := by_grind
  have b55 : ztlya := by_grind
  have d30 : c₃.nreg 81130 = g := by_grind
  have d31 : ztusk := by_grind
  have d32 : c₃.nreg 81132 = L := by_grind
  have d53 : ztoqy := by_grind
  have d54 : ztoqz := by_grind
  -- the chord
  have hcF : (Nα.chord k).toSet _ _ ∈ Nα.F ztbdc zti :=
    ⟨_, Dec.chord_mem hk, rfl⟩
  have hcA := hP.hNα.1.2.1 hcF
  have hne := Gran.lpt_ne_rpt hP.hNα hMα hk
  obtain ⟨hseg, hy, hopen, -, -⟩ := hMα.attach_seg hcA hat.1 hat.2 hne
  set A := sidePt (chainModel Cα).W (Nα.chord k).lp
    ((chainModel Cα).param zti (Nα.chord k).lpos) with hAdef
  set B := sidePt (chainModel Cα).W (Nα.chord k).rp
    ((chainModel Cα).param zti (Nα.chord k).rpos) with hBdef
  have hAB1 : A.1 < B.1 := by
    have hm : B ∈ (Nα.chord k).toSet _ _ := hat.2.2.2.2.1
    have h1 : A.1 ≤ B.1 := hm.2.1
    grind
  have hL₀ : 0 < B.1 - A.1 := by_linarith
  have hrA : rayPt A (dirOf 1) ztsvh = B := by
    have := eq_rayPt ztp hy.symm
    zvohi at this; rw [dirOf1]; grind
  have hrB : rayPt B (dirOf 0) ztsvh = A := by
    have := eq_rayPt ztbt hy
    rw [show -1 * (A.1 - B.1) = B.1 - A.1 by ring] at this; rw [dirOf0]; grind
  have hJ1 : aj = E.M.key zti ztrbs := by_grind
  have hJ2 : aj = E.M.key zti ztrbw := by_grind
  have EA := end_info hE hS hGα hD R₂ a30 a31 a35 u53 u55 hpA
    rfl hcA hat.1 hat.2 hL₀
    (by show _ = Chazelle.segment A ztruw; grind) hrA
    (by show ∀ s ∈ Ioo (0 : ℝ) 1, lerp A ztruw s ∈ Cα.dom
        rw [hrA]; tauto) hJ1
    by_grind f1 by_omega
  have EB := end_info hE hS hGα hD R₃ b30 b31 b35 b54 b55 hpB
    rfl hcA hat.2 hat.1 hL₀
    (by show _ = Chazelle.segment B ztrux
        rw [hrB, Chazelle.Geometry.segment_comm]; omega) hrB
    (by show ∀ s ∈ Ioo (0 : ℝ) 1, lerp B ztrux s ∈ Cα.dom
        rw [hrB]; exact WalkAx.open_rev hopen) hJ2 by_grind f2
    by_omega
  zvmxv at EA EB
  have tA0 : 0 ≤ (chainModel Cα).param _ (Nα.chord k).lpos := hpA.2.1.1
  have tA1 : (chainModel Cα).param _ (Nα.chord k).lpos < 1 := hpA.2.1.2.1
  have tB0 : 0 ≤ (chainModel Cα).param _ (Nα.chord k).rpos := hpB.2.1.1
  have tB1 : (chainModel Cα).param _ (Nα.chord k).rpos < 1 := hpB.2.1.2.1
  have hpAn : (Nα.chord k).lp < (chainModel Cα).W.n := hpA.1
  have hpBn : (Nα.chord k).rp < (chainModel Cα).W.n := hpB.1
  set tA : ℝ := (chainModel Cα).param _ ⟨(Nα.chord k).lp, (Nα.chord k).h + 1⟩ with htA
  set tB : ℝ := (chainModel Cα).param _ ⟨(Nα.chord k).rp, (Nα.chord k).h + 1⟩ with htB
  replace tA0 : 0 ≤ tA := tA0
  replace tA1 : tA < 1 := tA1
  replace tB0 : 0 ≤ tB := tB0
  replace tB1 : tB < 1 := tB1
  set da : ℝ := off (chainModel Cα).W.n g' ((Nα.chord k).lp + tA) with hda
  set db : ℝ := off (chainModel Cα).W.n g' ztgvm with hdb
  obtain ⟨inA, neA, stA⟩ := EA
  obtain ⟨inB, neB, stB⟩ := EB
  zqbel
  -- the offsets of the ends
  have offE : ∀ (p : ℕ) (t : ℝ), p < (chainModel Cα).W.n → 0 ≤ t → t < 1 →
      0 < off (chainModel Cα).W.n g' ztk → off (chainModel Cα).W.n g' ztk < L →
      g' ≤ p ∧ p - g' < L ∧ off (chainModel Cα).W.n g' ztk = ((p - g' : ℕ) : ℝ) + t := by
    intro p t hp t0 t1 a b
    obtain ⟨i1, i2, -⟩ := (inE_iff hS hp t0 t1).2 ztbqy
    refine ⟨i1, by_omega, ?_⟩
    have e := endα_off hS (d := p - g') by_omega t0 t1
    rwa [show g' + zttvf = p by omega] at e
  have offU : ∀ u : ℕ, u < L → off (chainModel Cα).W.n g' (((g' + u : ℕ) : ℝ)) = u := by
    zubgt
    have e := endα_off hS hu le_rfl one_pos
    rwa [add_zero, add_zero] at e
  -- the end data
  obtain ⟨αa, ha0, haa, hgA, rotA⟩ : ∃ αa : ℝ, 0 ≤ αa ∧ (0 < αa → αa < L → αa = db) ∧
      GEnd L da αa ztlmn dX ∧
      (0 < da → da < L → ∀ u, u < L →
        (sideInArc (E.M.key zti ⟨c₂.nreg 81161, c₂.nreg 81162⟩)
          (E.M.key zti ⟨c₂.nreg 81163, c₂.nreg 81164⟩) ((ztesw % E.M.W.n : ℕ) : ℝ) ↔
          sideInArc da αa u)) := by
    by_cases hi : 0 < da ∧ da < L
    · obtain ⟨-, -, -, -, α, h0, h1, h2⟩ := stA hi.1 hi.2
      obtain ⟨h3, h4⟩ := h2 neB
      zqbem
    · exact ⟨0, le_rfl, fun h => absurd h ztgkw, fun h => absurd h hi,
        fun a b => absurd ztbqy hi⟩
  obtain ⟨αb, hb0, hbb, hgB, rotB⟩ : ∃ αb : ℝ, 0 ≤ αb ∧ (0 < αb → αb < L → αb = da) ∧
      GEnd L db αb ztlmo dX ∧
      (0 < db → db < L → ∀ u, u < L →
        (sideInArc (E.M.key zti ⟨c₃.nreg 81171, c₃.nreg 81172⟩)
          (E.M.key zti ⟨c₃.nreg 81173, c₃.nreg 81174⟩) ((ztesw % E.M.W.n : ℕ) : ℝ) ↔
          sideInArc db αb u)) := by
    by_cases hi : 0 < db ∧ db < L
    · obtain ⟨-, -, -, -, α, h0, h1, h2⟩ := stB hi.1 hi.2
      obtain ⟨h3, h4⟩ := h2 neA
      zqbem
    · exact ⟨0, le_rfl, fun h => absurd h ztgkw, fun h => absurd h hi,
        fun a b => absurd ztbqy hi⟩
  zuiyb
  have hgn : (g' : ℝ) < (chainModel Cα).W.n := by
    rw [hnα]; have := hS.hgL; have := hS.hL0; exact_mod_cast (by omega : g' < 2 * Cα.m + 7)
  have hkA0 : (0 : ℝ) ≤ (Nα.chord k).lp + tA := by_positivity
  have hkB0 : (0 : ℝ) ≤ (Nα.chord k).rp + tB := by_positivity
  have hkAn : ((Nα.chord k).lp : ℝ) + tA < (chainModel Cα).W.n := by
    have : ((Nα.chord k).lp : ℝ) + 1 ≤ (chainModel Cα).W.n := by exact_mod_cast hpAn
    linarith
  have hkBn : ((Nα.chord k).rp : ℝ) + tB < (chainModel Cα).W.n := by
    have : ((Nα.chord k).rp : ℝ) + 1 ≤ (chainModel Cα).W.n := by exact_mod_cast hpBn
    linarith
  have hda0 := off_nonneg hkA0 hgn
  have hdb0 := off_nonneg hkB0 hgn
  have hdab : da ≠ db := by
    zuq
    obtain ⟨e1, e2⟩ := nat_add_frac tA0 tA1 tB0 tB1 (off_inj hg0 hgn hkA0 hkAn hkB0 hkBn h)
    zufqo
    show sidePt _ (Nα.chord k).lp tA = sidePt _ (Nα.chord k).rp tB
    zuea
  have hWX : WOK L da db αa αb _ _ (dX : ℕ) :=
    ⟨hX0, hXL, fun h => neA h.symm, fun h => neB h.symm, hgA, hgB⟩
  -- the registers of the left end at `c₃`
  have q60 : c₃.nreg 81160 = c₂.nreg 81160 := g3 _ by_norm_num by_norm_num
  have q61 : c₃.nreg 81161 = c₂.nreg 81161 := g3 _ by_norm_num by_norm_num
  have q62 : c₃.nreg 81162 = c₂.nreg 81162 := g3 _ by_norm_num by_norm_num
  have q63 : c₃.nreg 81163 = c₂.nreg 81163 := g3 _ by_norm_num by_norm_num
  have q64 : c₃.nreg 81164 = c₂.nreg 81164 := g3 _ by_norm_num by_norm_num
  have q65 : c₃.nreg 81165 = c₂.nreg 81165 := g3 _ by_norm_num by_norm_num
  have q66 : c₃.nreg 81166 = c₂.nreg 81166 := g3 _ by_norm_num by_norm_num
  have q67 : c₃.nreg 81167 = c₂.nreg 81167 := g3 _ by_norm_num by_norm_num
  -- passing the tests ↔ the candidate condition
  have toW : ∀ u : ℕ, WOK L da db αa αb ztlmn ztlmo (u : ℝ) →
      WCand E c₀ c₃ u := by
    rintro u ⟨w0, wL, wa, wb, wga, wgb⟩
    have hu : u < L := by exact_mod_cast wL
    zultx
    zulrv
    zvoak
    refine ⟨hu, (hD.hcnt u hu).1, ?_, ?_, fun h1 h5 => ?_, fun h1 h5 => ?_⟩
    · zuei
      zuhhf
      zqben
      have t0 : tA = 0 := by
        have := bit7.2; zvncq at this; simp at this; linarith
      apply wa
      have e : off (chainModel Cα).W.n g' zteim = u := by
        zuezt
      exact e.symm
    · zuei
      zuhhg
      zqbeo
      have t0 : tB = 0 := by
        have := bit7.2; zvncq at this; simp at this; linarith
      apply wb
      have e : off (chainModel Cα).W.n g' (((Nα.chord k).rp : ℝ) + tB) = u := by
        zuezt
      exact e.symm
    · zuhhf
      rw [rotA a b u hu]; exact wga ztbqy
    · zuhhg
      rw [rotB a b u hu]; exact wgb ztbqy
  have fromW : ∀ u : ℕ, 1 ≤ u → WCand E c₀ c₃ u →
      WOK L da db αa αb ztlmn ztlmo (u : ℝ) := by
    intro u hu1 hW
    unfold WCand GAt at hW
    zvmxv at hW
    zvoak at hW
    obtain ⟨hu, -, nA, nB, gA, gB⟩ := hW
    have hu0 : ztiwu := by_positivity
    have huL : (u : ℝ) < L := by exact_mod_cast hu
    refine ⟨hu0, huL, fun h => ?_, fun h => ?_, fun ⟨a, b⟩ => ?_, fun ⟨a, b⟩ => ?_⟩
    · zufev

      obtain ⟨i1, -, i3⟩ := offE _ _ hpAn tA0 tA1 a b
      zulhi
      obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos tA0 tA1 ztmcy
      zqben
      exact nA ⟨inA.2 ztbqy, by_omega, by
        have := bit7.1; have h7 := bit7.2; rw [← e2] at h7; simp at h7; omega⟩
    · zufev

      obtain ⟨i1, -, i3⟩ := offE _ _ hpBn tB0 tB1 a b
      zulhi
      obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos tB0 tB1 ztmcy
      zqbeo
      exact nB ⟨inB.2 ztbqy, by_omega, by
        have := bit7.1; have h7 := bit7.2; rw [← e2] at h7; simp at h7; omega⟩
    · obtain ⟨-, v5, -⟩ := stA a b
      have := gA (inA.2 by_omega) v5
      rw [rotA a b u hu] at this; omega
    · obtain ⟨-, v5, -⟩ := stB a b
      have := gB (inB.2 by_omega) v5
      rw [rotB a b u hu] at this; omega
  -- the child
  zuicf
  obtain ⟨Dd, hRT⟩ := hD.hRT
  have hneα : (Nα.F _ _).Nonempty := ⟨_, hcF⟩
  have hdn := (hRT.ends_lt k hk).2
  obtain ⟨-, hj, hjr⟩ := region_arc hMα hP.hNα hD.hregsα hneα hdn
  have hXn : ztmvt := by rw [hnα]; have := hD.hXL; omega
  have offX : off (chainModel Cα).W.n g' _ = dX := offU dX hD.hXL
  have hpa : ztjby ≠ (Nα.chord k).lp + tA := by
    intro h; apply neA
    show off (chainModel Cα).W.n g' _ = dX
    zujmc
  have hpb : ztjby ≠ (Nα.chord k).rp + tB := by
    intro h; apply neB
    show off (chainModel Cα).W.n g' _ = dX
    zujmc
  have CS := child_side hGα hP.hNα hRT hD.hregsα hk hat.1 hat.2 hne hD.hT hXn hD.hfT hpa hpb hj hjr
  by_cases hw1 : c₄.nreg 81181 = 1
  · obtain ⟨hU, xe, hu1⟩ := xC hw1
    have hu := fromW _ hu1 hU
    have huL : ztusy := by have := hU.1; rw [d32] at this; omega
    have hside := witness_side_ok ha0 haa hb0 hbb hda0 hdb0 hdab hu hWX
    have hkU : (chainModel Cα).key zti ztfwe =
        (ztlzg : ℝ) := by rw [key_vtx, xe, d31]
    have hUn : (ztlzg : ℝ) < (chainModel Cα).W.n := by
      have : g' + c₄.nreg 81180 < (chainModel Cα).W.n := by rw [hnα]; omega
      zufc
    have hiff : sideInArc ztwmh
        ztwmi
        ztymx ↔
        sideInArc ztwmh
        ztwmi (ztmyy : ℝ) := by
      rw [hkU]
      show sideInArc zteim ztgvm _ ↔
        sideInArc zteim ztgvm _
      rw [sideInArc_rot hg0 hgn hkA0 hkAn hkB0 hkBn ztdlc hUn,
        sideInArc_rot hg0 hgn hkA0 hkAn hkB0 hkBn ztdlc (by exact_mod_cast hXn),
        offU _ huL, offX]
      omega
    obtain ⟨hlo, hhi⟩ := hch hw1
    by_cases hc : (sideInArc ztwmh
        ztwmi (ztmyy : ℝ) ↔
      ((chainModel Cα).key zti (Nα.arc ztcrs).s =
          (chainModel Cα).key zti (Nα.chord k).lpos ∨
        sideInArc ztwmh
          ztwmi
          ztxtu))
    · rw [hlo (hiff.trans hc)]; exact below_lo hDec hk hb (CS.1 hc)
    · rw [hhi (fun h => hc (hiff.symm.trans h))]; exact below_hi hDec hk hb (CS.2 hc)
  · exfalso
    rcases witness_exists ha0 haa hb0 hbb hda0 hdb0 hWX with h | ⟨a, b, h⟩ | ⟨a, b, h⟩
    · exact hw1 (xAll (Or.inl (toW 1 (by rw [Nat.cast_one]; exact h))))
    · obtain ⟨-, -, i3⟩ := offE _ _ hpAn tA0 tA1 a b
      have fl : ⌊da⌋₊ = (Nα.chord k).lp - g' := by
        show ⌊off (chainModel Cα).W.n g' _⌋₊ = _
        zugvv

      exact hw1 (xAll (Or.inr (Or.inl ⟨by rw [q60]; exact inA.2 ztbqy,
        by rw [d53, d31, ← fl]; exact toW _ h⟩)))
    · obtain ⟨-, -, i3⟩ := offE _ _ hpBn tB0 tB1 a b
      have fl : ⌊db⌋₊ = (Nα.chord k).rp - g' := by
        show ⌊off (chainModel Cα).W.n g' _⌋₊ = _
        zugvv

      exact hw1 (xAll (Or.inr (Or.inr ⟨inB.2 ztbqy,
        by rw [d54, d31, ← fl]; exact toW _ h⟩)))
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)

/-- The number of walk vertices the leaf visits on an arc from the start edge `se` to the end
edge `ee` (walk of length `N`); `w = 0` iff the start key is not below the end key. -/
def arcCnt (N se ee w : ℕ) : ℕ := ztqmk % N + 1 + (if se = ee ∧ w = 0 then N else 0)

/-- **Every integer key on the closed arc is visited.** -/
theorem arc_int {N se ee w : ℕ} {a b : ℝ} (hse : se < N) (hee : ee < N) (ha0 : (se : ℝ) ≤ a)
    (ha1 : a < se + 1) (hb0 : (ee : ℝ) ≤ b) (hb1 : b < ee + 1) (hw : w = 0 ∨ a < b)
    {x : ℕ} (hx : x < N) (hc : ClosedArc a b x) :
    ∃ i, i < arcCnt N se ee w ∧ (se + i) % N = x := by
  refine ⟨ztgmu % N, ?_, ?_⟩
  swap
  · have : se + ztgmu % N ≡ x [MOD N] := by
      rw [Nat.ModEq, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show se + ztgmu = x + N by
        omega, Nat.add_mod_right]
    rw [this, Nat.mod_eq_of_lt hx]
  zuhqp
  by_cases hsp : se = ee ∧ w = 0
  · rw [ite_eq_left hsp]
    have := Nat.mod_lt ztgmu (by omega : 0 < N)
    omega
  rw [ite_eq_right hsp]
  have hxa : ∀ y : ℕ, (y : ℝ) = a → y = se := fun y h => by
    have h1 : (se : ℝ) ≤ y := h ▸ ha0
    have h2 : (y : ℝ) < se + 1 := h ▸ ha1
    have h1' : se ≤ y := by exact_mod_cast h1
    have h2' : y < se + 1 := by exact_mod_cast h2
    omega
  have hxb : ∀ y : ℕ, (y : ℝ) = b → y = ee := fun y h => by
    have h1 : (ee : ℝ) ≤ y := h ▸ hb0
    have h2 : (y : ℝ) < ee + 1 := h ▸ hb1
    have h1' : ee ≤ y := by exact_mod_cast h1
    have h2' : y < ee + 1 := by exact_mod_cast h2
    omega
  zuik
  · zuhaz
    split_ifs at hc with hab
    · -- a < x < b
      have h1 : ztsmd := by
        have : ztmsc := by_grind
        zufc
      have h2 : ztsmw := by
        have : ztmsf := by_grind
        zufc
      have h3 : se ≤ ee := by
        omega
      rw [show x + N - se = ztudt + N by omega, Nat.add_mod_right,
        show ee + N - se = (ee - se) + N by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega, Nat.mod_eq_of_lt by_omega]
      omega
    · -- b ≤ a
      have hab' : ee ≤ se := by
        have : ztmrj := by_linarith
        zuhvg

      have hne : ee ≠ se := by
        grind
      have hlt : ee < se := by_omega
      rw [Nat.mod_eq_of_lt (by omega : ee + N - se < N)]
      zunk
      · have h1 : se ≤ x := by
          have : ztmsc := by_linarith
          have : ztsmd := by exact_mod_cast this
          omega
        rw [show x + N - se = ztudt + N by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega]
        omega
      · have h2 : x ≤ ee := by
          have : ztmsf := by_linarith
          have : ztsmw := by exact_mod_cast this
          omega
        zuey
        omega
  · have := hxa x hc
    zumo
    simp
  grind

/-- **The leaf above the target is the target.** -/
theorem leaf_target {N : NF} {d : ℕ} (hD : IsDecomp N d) {r T : ℕ} (hr : r < N.nRegions)
    (hT : T < N.nRegions) (hb : N.Below ztwy T) : r = T :=
  (hD.2.2.2.2.2.2.2.1 r T hr hT hb).symm
variable {E : FEnv} {c₀ : Config} {Cα : Chain} {g g' L : ℕ}

/-- **The good vertex is on the closed arc of an arc record of the target.** -/
theorem arc_of_target (hGα : GoodModel ztbdc) {Nα : NF}
    (hNα : IsNF ztbdc zti Nα)
    {reg : ℕ → Set Point} {ai bi aj bj : ℝ} {dX : ℕ} {regα : ℕ → Set Point} {T : ℕ}
    (hD : DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T)
    (hXn : g' + dX < (chainModel Cα).W.n) :
    ∃ t, t < (Nα.region T).arcs.length ∧
      (Nα.region T).arcs.getD t 0 < Nα.arcs.length ∧
      ClosedArc ((chainModel Cα).key zti (Nα.arc ztmyf).s)
        ((chainModel Cα).key zti (Nα.arc ztmyf).e)
        ((g' + dX : ℕ) : ℝ) := by
  obtain ⟨hcorr, -, harcs, -⟩ := hD.hregsα
  have hFam := hNα.1
  obtain ⟨U, hU, a, b, harc, hcl, hev⟩ := arc_after hGα hFam hXn
  have hTU := hcorr.1 T hD.hT
  obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := ((hD.hfT.and hev).and ztctd).exists
  have hfU := harc.2.2.2.2.2.2 _ ε hXn h3.1 h3.2 h2
  have hUT : U = regα T := WalkAx.faces_unique hU hTU hfU h1
  subst hUT
  obtain ⟨j, hj, hjr, hjs, hje⟩ := harcs.2.2.1 T hD.hT a b harc
  have hmem : j ∈ (Nα.region T).arcs := (harcs.2.2.2 T hD.hT j).2 zthnb
  obtain ⟨t, ht, htj⟩ := List.mem_iff_getElem.1 hmem
  have hget : (Nα.region T).arcs.getD t 0 = j := by
    simp_all
  grind
end
end Restore
end Chazelle.Core
section
set_option hygiene false
local macro "zqyb" : tactic => `(tactic| (zvmwg; zumxt))
local macro "zqyc" : tactic => `(tactic| (zunag; zuncf
                                          grind))
local macro "zqyd" : tactic => `(tactic| (simp only [okB, okI, FScr, FOut]; norm_num))
local macro "zqye" : tactic => `(tactic| refine ⟨?_, ?_, ?_, ?_, ?_, fun q h1 h2 h3 h4 h5 h6 h7 => ?_⟩)
local macro "zqyf" : tactic => `(tactic| (refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩))
local macro "zqyg" : tactic => `(tactic| refine (FRS.block hB _ hI ok).mono by_rfl zthi)
local macro "zqyh" : tactic => `(tactic| (zvmwg; simp [leafInitL, regB, regI, upd, k5]; simp_all))
local macro "zqyi" : tactic => `(tactic| obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR)
set_option hygiene true

/-!
# WP-E, the search on the RAM (`FindOK`), part 21: the leaf of the descent

At the leaf region `r` (`81121`) of the piece's normal form (handle `81134`), visit the arcs of
`r` one by one; on an arc, visit `arcCnt` walk vertices of `Cα`'s walk from the start edge, and
test (both directions) the host vertex of every visited vertex strictly inside the stretch.

* `arcLoad`: the arc `j = arcs(r)[t]` (`81102`) and its ends `(81103, 81106)`, `(81107, 81108)`.
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs NFLoc

/-- The reads of the arc index `j = arcs(r)[t]`. -/
def arcL1 : List Instr :=
  [.addN 81114 81134 81015, .loadN 81114 81114, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81012, .loadN 81114 81114,
    .addN 81115 81134 81016, .loadN 81115 81115, .addN 81114 81115 81114,
    .addN 81114 81114 81100, .loadN 81102 81114]

/-- The reads of the ends of the arc `j`. -/
def arcL2 : List Instr :=
  [.addN 81114 81134 81014, .addN 81114 81114 81012, .loadN 81114 81114,
    .addN 81114 81114 81102, .addN 81114 81114 81102, .addN 81114 81114 81102,
    .addN 81114 81114 81102, .addN 81114 81114 81102, .addN 81114 81114 81012,
    .loadN 81103 81114, .addN 81114 81114 81012, .loadN 81106 81114,
    .addN 81114 81114 81012, .loadN 81107 81114, .addN 81114 81114 81012, .loadN 81108 81114]

/-- **The arc of the leaf at index `t`.** -/
def arcLoad : Stmt := .seq (Stmt.block arcL1) (Stmt.block arcL2)
variable {E : FEnv} {c₀ c : Config}
theorem arcLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N)
    (hr : c.nreg 81121 < N.nRegions) (ht : c.nreg 81100 < (N.region ztfgt).arcs.length)
    (hj : (N.region ztfgt).arcs.getD zthuz 0 < N.arcs.length) :
    FRS B E.P E.W c₀ arcLoad c 30 (fun c' =>
      c'.nreg 81102 = (N.region ztfgt).arcs.getD zthuz 0 ∧
      c'.nreg 81103 = (N.arc ztcgj).s.edge ∧
      c'.nreg 81106 = (N.arc ztcgj).s.hgt ∧
      c'.nreg 81107 = (N.arc ztcgj).e.edge ∧
      c'.nreg 81108 = (N.arc ztcgj).e.hgt ∧
      ∀ q, q ≠ 81102 → q ≠ 81103 → q ≠ 81106 → q ≠ 81107 → q ≠ 81108 → q ≠ 81114 →
        q ≠ 81115 → c'.nreg q = c.nreg q) := by
  have hN' : ztiyn :=
    Robust.transport hN hI.hm
  zuclx

  zubnp
  zuki
  zuese
  zudqm
  have rj := hl _ ht
  obtain ⟨-, s1, s2, s3, s4⟩ := hNA.2.2.2.2.2.2.1 _ hj
  zujwr
  have b2 := hlb _ hr _ ht
  zujws
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81015 = 5 ∧ c'.nreg 81016 = 7 ∧ c'.nreg 81014 = 3 ∧
      c'.nreg 81012 = 1 := fun c' h =>
    ⟨by zuoaf, by zuoag,
      by zuoah, by zuoai⟩
  zueja
  have e5 : c.nmem ztfqh + c.nreg 81121 + c.nreg 81121 + c.nreg 81121 +
      c.nreg 81121 + c.nreg 81121 + 1 = c.nmem ztfqh + 5 * c.nreg 81121 + 1 := by_ring
  -- stage 1
  have ok1 : okB E.W c.nmem arcL1 c.nreg := by
    simp only [arcL1, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k7, k1]
    grind
  zuhiv
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem arcL1 c.nreg q := fun q => by zvnbm
  zulp
  have v02 : c₁.nreg 81102 = (N.region ztfgt).arcs.getD zthuz 0 := by
    zumwx; simp [arcL1, regB, regI, upd, k5, k7, k1]
    grind
  have f₁ : ∀ q, q ≠ 81102 → q ≠ 81114 → q ≠ 81115 → c₁.nreg q = c.nreg q := fun q h1 h2 h3 => by
    zugct
    simp only [arcL1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> zvmwd <;> omega
  obtain ⟨-, -, k3₁, k1₁⟩ := fx c₁ hI₁
  have w34 := f₁ 81134 by_norm_num by_norm_num by_norm_num
  zujxl
  generalize hjdef : (N.region _).arcs.getD _ 0 = j at v02 b3 s1 s2 s3 s4 ⊢
  -- stage 2
  have ok2 : okB E.W c₁.nmem arcL2 c₁.nreg := by
    simp only [arcL2, okB, okI, regI, upd]
    simp only [FScr, FOut, k3₁, k1₁, w34, v02, m₁]
    norm_num
    zujhw
    omega
  refine (FRS.block hB _ hI₁ ok2).mono by_rfl (fun c₂ h₂ => ?_)
  have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem arcL2 c₁.nreg q := fun q => by rw [h₂]
  have ea : c.nmem zthvb + j + j + j + j + j + 1 =
      c.nmem zthvb + 5 * j + 1 := by_ring
  zqye
  · rw [e₂, regB_other _ _ _ ztdp, v02]
    zufbi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> zvmwd <;> omega
  · zunag; zuncf; grind
  · zqyc
  · zqyc
  · zqyc
  · rw [e₂, regB_other _ _ _ ztdp, f₁ q h1 h6 h7]
    zufbi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> zvmwd <;> omega

/-- Run `S` if `a = b`. -/
def ifEq (a b : ℕ) (S : Stmt) : Stmt := .ifLtN a b .skip (.ifLtN b a .skip S)
variable {B : Finset ℕ} {P : Polygon} {W : ℕ} {a b : ℕ} {S : Stmt} {K : ℕ} {Q : Config → Prop} {Cα : Chain} {N se ee w : ℕ}
theorem FRS.ifEq_eq
 (h : c.nreg a = c.nreg b) (hS : FRS B P W c₀ S c K Q) :
    FRS B P W c₀ ztrsh c ztfns Q :=
  (FRS.ifF by_omega (FRS.ifF by_omega hS)).mono by_omega by_simp_all
theorem FRS.ifEq_ne
 (hI : FInv W c₀ c) (h : c.nreg a ≠ c.nreg b) (hq : Q c) :
    FRS B P W c₀ ztrsh c ztfns Q := by
  zubai
  · exact (FRS.ifT h1 (FRS.skip (K := 0) hI hq)).mono by_omega by_simp_all
  · exact (FRS.ifF h1 (FRS.ifT by_omega (FRS.skip (K := 0) hI hq))).mono by_omega
      by_simp_all

/-- **The count of an arc**: `w` (`81110`), the count (`81104`), the next arc index. -/
def cntS : Stmt :=
  .seq (Stmt.block [.constN 81110 0, .loadN 81111 81134])
    (.seq (.ifLtN 81011 81111 (ifEq 81103 81107
        (.seq (cmpA 81112 81103 81106 81107 81108) (Stmt.block [.copyN 81110 81112]))) .skip)
      (.seq (Stmt.block [.addN 81104 81107 81105, .subN 81104 81104 81103])
        (.seq (.ifLtN 81104 81105 .skip (Stmt.block [.subN 81104 81104 81105]))
          (.seq (Stmt.block [.addN 81104 81104 81012])
            (.seq (ifEq 81103 81107 (.ifLtN 81011 81110 .skip
                (Stmt.block [.addN 81104 81104 81105])))
              (Stmt.block [.addN 81100 81100 81012]))))))

/-- The cost bound of `cntS`. -/
def csK : ℕ := 11040

/-- The bit `w` of an arc with ends `(se, sh)`, `(ee, eh)` (normal form with `nc` chords). -/
noncomputable def wBit (Cα : Chain) (Q : Polygon) (nc se sh ee eh : ℕ) : ℕ := by
  classical
  exact if 0 < nc ∧ se = ee ∧ (chainModel Cα).key Q ztujm < (chainModel Cα).key Q ztugn
    then 1 else 0
theorem wBit_spec {Q : Polygon} {nc se sh ee eh : ℕ} :
    wBit Cα Q nc se sh ee eh = 0 ∨
      (chainModel Cα).key Q ztujm < (chainModel Cα).key Q ztugn := by
  unfold wBit; grind

/-- The registers `cntS` writes. -/
def CsW (q : ℕ) : Prop := KeyW q ∨ q = 81100 ∨ q = 81104 ∨ (81110 ≤ q ∧ q ≤ 81113)
theorem cntS_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztdq c₀.nmem ztcpp)
    (hC : ChainDescAt c₀.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hse : c.nreg 81103 < c.nreg 81105) (hee : c.nreg 81107 < c.nreg 81105)
    (hNW : 2 * c.nreg 81105 ≤ E.W)
    (hpos : 0 < N.nChords → PosOK Cα zti E.P.n ztrbk ∧
      PosOK Cα zti E.P.n ztrbl)
    (htW : c.nreg 81100 + 1 ≤ E.W)
    (hroom : c.nreg ALLOC + csK ≤ E.W) :
    FRS B E.P E.W c₀ cntS c csK (fun c' =>
      c'.nreg 81104 = arcCnt ztviu ztmgk ztmgl (c'.nreg 81110) ∧
      c'.nreg 81110 = wBit Cα zti N.nChords ztmgk ztviv ztmgl
        ztviw ∧
      c'.nreg 81100 = c.nreg 81100 + 1 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ CsW q → c'.nreg q = c.nreg q) := by
  zubgm
  zuhr
  have hN' : ztiyn :=
    Robust.transport hN hI.hm
  zuglr
  -- stage 1
  have ok1 : okB E.W c.nmem [.constN 81110 0, .loadN 81111 81134] c.nreg := by
    zqyd
  refine FRS.seq (K₂ := csK - 2) ztbbr ztiy |>.mono
    by_rfl ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.constN 81110 0, .loadN 81111 81134] c.nreg q :=
    by simp_all
  have v10 : c₁.nreg 81110 = 0 := by_tauto
  have v11 : c₁.nreg 81111 = N.nChords := by zumwx; zumxd; exact hNA.1
  have f₁ : ∀ q, q ≠ 81110 → q ≠ 81111 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    zuib
  zudhe
  have r := fun q (h : 81100 ≤ q ∧ q ≤ 81109) => f₁ q by_omega by_omega
  have w33 : c₁.nreg 81133 = c.nreg 81133 := by_simp_all
  -- stage 2: the bit `w`
  zukhy
  refine FRS.seq (K₁ := 11017) (K₂ := 18) (Q₁ := fun c' =>
      c'.nreg 81110 = wBit Cα zti N.nChords ztmgk ztviv ztmgl
        ztviw ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ 81110 → q ≠ 81112 → q ≠ 81113 →
        c'.nreg q = c₁.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨hw₂, f₂⟩ => ?_) |>.mono
    by_decide ztb
  · by_cases a1 : c₁.nreg 81011 < c₁.nreg 81111
    swap
    · refine (FRS.ifF a1 (FRS.skip (K := 0) hI₁ ztdiv)).mono
        by_omega ztb
      rw [v10]; unfold wBit; simp_all
    refine (FRS.ifT a1 ?_).mono (K := 11017) by_omega ztb
    have hpos' := hpos by_omega
    by_cases e : c₁.nreg 81103 = c₁.nreg 81107
    swap
    · refine FRS.ifEq_ne hI₁ e ztdiv
      rw [v10]; unfold wBit
      simp_all
    refine FRS.ifEq_eq e ((FRS.seq (K₂ := 1) (cmpA_fs₀ hE hB hI₁ ztfm
      ⟨by_norm_num, by_norm_num⟩ ⟨by_norm_num, by_norm_num⟩ ⟨by_norm_num, by_norm_num⟩
      ⟨by_norm_num, by_norm_num⟩ ztqj ztqj
      ztqj ztqj by_simp_all
      (by rw [w33]; exact hC) hWm
      by_grind
      by_simp_all
      (by rw [hA₁']; unfold csK at hroom; omega)) (fun c' hI' _ ⟨b12, _, f'⟩ => ?_)).mono by_norm_num (fun _ h => h))
    have okc : okB E.W c'.nmem [.copyN 81110 81112] c'.nreg := by
      zqyd
    refine (FRS.block hB _ hI' okc).mono by_simp ztgix
    have e' : ∀ q, c''.nreg q = regB c'.nmem [.copyN 81110 81112] c'.nreg q := fun q => by rw [h'']
    refine ⟨?_, fun q a b hk h1 h2 h3 => ?_⟩
    · zqyb
      have hb := b12
      rw [r 81103 by_omega, r 81106 by_omega,
        r 81107 by_omega, r 81108 by_omega] at hb
      have hpc : 0 < N.nChords := by_omega
      have he : c.nreg 81103 = c.nreg 81107 := by
        grind
      unfold wBit
      by_cases hk : (chainModel Cα).key zti ztrbk <
          (chainModel Cα).key zti ztrbl
      · rw [ite_eq_left by_grind]; exact hb.2.2 hk
      · rw [ite_eq_right by_grind]
        have := hb.1; have h2 : c'.nreg 81112 ≠ 1 := fun h => hk (hb.2.1 h); omega
    · zvmwg; simp only [regB, regI, upd, ite_eq_right h1]; grind
  -- stage 3 on: the count
  have r₂ : ∀ q, 81100 ≤ q → q ≤ 81109 → c₂.nreg q = c.nreg q := fun q a b => by
    rw [f₂ q by_omega by_omega ztqj by_omega by_omega by_omega,
      f₁ q by_omega by_omega]
  zueho
  zudpz
  have x03 := r₂ 81103 by_norm_num by_norm_num
  have x05 := r₂ 81105 by_norm_num by_norm_num
  have x07 := r₂ 81107 by_norm_num by_norm_num
  have x00 := r₂ 81100 by_norm_num by_norm_num
  have ok3 : okB E.W c₂.nmem [.addN 81104 81107 81105, .subN 81104 81104 81103] c₂.nreg := by
    simp only [okB, okI, FScr, FOut, x05, x07]; grind
  refine FRS.seq (K₂ := 16) ztgdu ztcnf |>.mono
    by_simp ztb
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.addN 81104 81107 81105, .subN 81104 81104 81103]
      c₂.nreg q := fun q => by zunbh
  have u04 : c₃.nreg 81104 = c.nreg 81107 + c.nreg 81105 - c.nreg 81103 := by
    zumzv; simp [regB, regI, upd, x03, x05, x07]
  have f₃ : ∀ q, q ≠ 81104 → c₃.nreg q = c₂.nreg q := fun q h => by
    zublu
  have u05 : c₃.nreg 81105 = c.nreg 81105 := by_grind
  -- the modulus
  refine FRS.seq (K₁ := 3) (K₂ := 13) (Q₁ := fun c' =>
      c'.nreg 81104 = ztghk % c.nreg 81105 ∧
      ∀ q, q ≠ 81104 → c'.nreg q = c₃.nreg q) ?_ (fun c₄ hI₄ hA₄ ⟨u04', f₄⟩ => ?_) |>.mono
    by_omega ztb
  · by_cases a : c₃.nreg 81104 < c₃.nreg 81105
    · refine (FRS.ifT a (FRS.skip (K := 0) hI₃ ztdiv)).mono by_omega
        ztb
      rw [u04] at a ⊢; rw [u05] at a; zuosw
    · have okm : okB E.W c₃.nmem [.subN 81104 81104 81105] c₃.nreg := by
        zqyd
      zuhio
      have e' : ∀ q, c'.nreg q = regB c₃.nmem [.subN 81104 81104 81105] c₃.nreg q :=
        fun q => by zvmxl
      zqyf
      zqyb
      rw [u04, u05] at *
      have h2 : c.nreg 81107 + c.nreg 81105 - c.nreg 81103 - c.nreg 81105 < c.nreg 81105 := by
        omega
      rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt h2]
  have hN0 : 0 < c.nreg 81105 := by_omega
  have hml := Nat.mod_lt ztghk hN0
  have k1₄ : c₄.nreg 81012 = 1 := by rw [hI₄.hin _ ztbc, hE.k1]
  have g4 : ∀ q, q ≠ 81104 → c₄.nreg q = c₂.nreg q := fun q h => by rw [f₄ q h, f₃ q h]
  have ok5 : okB E.W c₄.nmem [.addN 81104 81104 81012] c₄.nreg := by
    simp only [okB, okI, FScr, FOut, k1₄, u04']; grind
  refine FRS.seq (K₂ := 12) ztpyo zthgv |>.mono
    by_simp ztb
  have e₅ : ∀ q, c₅.nreg q = regB c₄.nmem [.addN 81104 81104 81012] c₄.nreg q := fun q => by
    zueyl
  have v₅ : c₅.nreg 81104 = ztghk % c.nreg 81105 + 1 := by
    zunkr; simp [regB, regI, upd, k1₄, u04']
  have f₅ : ∀ q, q ≠ 81104 → c₅.nreg q = c₂.nreg q := fun q h => by
    zunkr; zundx; exact g4 q h
  have y03 : c₅.nreg 81103 = c.nreg 81103 := by rw [f₅ _ by_norm_num, x03]
  have y05 : c₅.nreg 81105 = c.nreg 81105 := by rw [f₅ _ by_norm_num, x05]
  have y07 : c₅.nreg 81107 = c.nreg 81107 := by rw [f₅ _ by_norm_num, x07]
  have y10 : c₅.nreg 81110 = c₂.nreg 81110 := f₅ _ by_norm_num
  zukhz
  refine FRS.seq (K₁ := 7) (K₂ := 5) (Q₁ := fun c' =>
      c'.nreg 81104 = arcCnt ztviu ztmgk ztmgl (c₂.nreg 81110) ∧
      ∀ q, q ≠ 81104 → c'.nreg q = c₅.nreg q) ?_ (fun c₆ hI₆ hA₆ ⟨v₆, f₆⟩ => ?_) |>.mono
    by_omega ztb
  · zuhqp
    by_cases e : c₅.nreg 81103 = c₅.nreg 81107
    · refine FRS.ifEq_eq e ?_
      rw [y03, y07] at e
      by_cases a : c₅.nreg 81011 < c₅.nreg 81110
      · refine (FRS.ifT a (FRS.skip (K := 0) hI₅ ztdiv)).mono by_omega
          ztb
        rw [v₅, ite_eq_right by_omega]
      · have oka : okB E.W c₅.nmem [.addN 81104 81104 81105] c₅.nreg := by
          simp only [okB, okI, FScr, FOut, v₅, y05]; grind
        refine (FRS.ifF a ztpyp).mono by_simp zthi
        have e' : ∀ q, c'.nreg q = regB c₅.nmem [.addN 81104 81104 81105] c₅.nreg q :=
          fun q => by zvmxl
        zqyf
        zqyb
        rw [v₅, y05, ite_eq_left by_omega]
    · refine FRS.ifEq_ne hI₅ e ztdiv
      grind
  have k1₆ : c₆.nreg 81012 = 1 := by rw [hI₆.hin _ ztbc, hE.k1]
  have z00 : c₆.nreg 81100 = c.nreg 81100 := by rw [f₆ _ by_norm_num, f₅ _ by_norm_num, x00]
  have ok7 : okB E.W c₆.nmem [.addN 81100 81100 81012] c₆.nreg := by
    simp only [okB, okI, FScr, FOut, k1₆, z00]; grind
  refine (FRS.block hB _ hI₆ ok7).mono by_simp zthi
  have e' : ∀ q, c'.nreg q = regB c₆.nmem [.addN 81100 81100 81012] c₆.nreg q := fun q => by
    zuczu
  have f' : ∀ q, q ≠ 81100 → c'.nreg q = c₆.nreg q := fun q hq => by
    zubls
  have w' : c'.nreg 81110 = c₂.nreg 81110 := by
    rw [f' _ by_norm_num, f₆ _ by_norm_num, y10]
  refine ⟨by rw [f' _ by_norm_num, v₆, w'], by_omega, ?_, fun q a b hq => ?_⟩
  · zvmwg; simp [regB, regI, upd, k1₆, z00]
  · unfold CsW at hq
    rw [f' q by_omega, f₆ q by_omega, f₅ q by_omega,
      f₂ q a b by_grind by_omega by_omega by_omega, f₁ q by_omega by_omega]

/-- **A vertex step of the leaf**: test the host vertex of `v` (`81103`) if `v` is strictly inside
the stretch, then `v ← v + 1 mod N`, `cnt ← cnt - 1`. -/
def vStep (sT : Stmt) : Stmt :=
  .seq (.ifLtN 81131 81103 (.ifLtN 81103 81135
      (.seq (Stmt.block [.subN 81071 81103 81131, .addN 81071 81071 81130])
        ztffa)
      .skip) .skip)
    (.seq (Stmt.block [.addN 81103 81103 81012, .subN 81104 81104 81012])
      (.ifLtN 81103 81105 .skip (Stmt.block [.constN 81103 0])))

/-- The cost bound of `vStep`. -/
def vsK (E : FEnv) : ℕ := tvK E + 20
theorem vStep_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hv : c.nreg 81103 < c.nreg 81105) (hNW : 2 * c.nreg 81105 ≤ E.W)
    (hg : c.nreg 81130 < E.M.W.n) (hL : c.nreg 81135 - c.nreg 81131 ≤ E.M.W.n)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + vsK E ≤ E.W) :
    FRS B E.P E.W c₀ (vStep E.sT) c (vsK E) (fun c' => FWin E c' ∧
      c'.nreg 81103 = ztllc % c.nreg 81105 ∧ c'.nreg 81104 = c.nreg 81104 - 1 ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81103 → q ≠ 81104 →
        c'.nreg q = c.nreg q) ∧
      ztfn ∧
      (c.nreg 81131 < c.nreg 81103 → c.nreg 81103 < c.nreg 81135 →
        ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
          VSet E ztbcy → ∀ σb, σb ≤ 1 →
          GoodAt E reg ztbcy σb →
          c'.nreg 81007 = 1)) := by
  have n17 : ztuoj := by zunic
  zufvq
  -- the test
  refine FRS.seq (K₁ := tvK E + 15) (K₂ := 5) (Q₁ := fun c' => FWin E c' ∧
      ztegm ∧
      ztfn ∧
      (c.nreg 81131 < c.nreg 81103 → c.nreg 81103 < c.nreg 81135 →
        ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
          VSet E ztbcy → ∀ σb, σb ≤ 1 →
          GoodAt E reg ztbcy σb →
          c'.nreg 81007 = 1)) ?_ (fun c₁ hI₁ hA₁ ⟨hw₁, f₁, m₁, g₁⟩ => ?_) |>.mono
    by_rfl ztb
  · by_cases a1 : c.nreg 81131 < c.nreg 81103
    swap
    · exact (FRS.ifF a1 (FRS.skip (K := 0) hI by_grind)).mono by_omega ztb
    refine (FRS.ifT a1 ?_).mono le_rfl ztb
    by_cases a2 : c.nreg 81103 < c.nreg 81135
    swap
    · exact (FRS.ifF a2 (FRS.skip (K := 0) hI by_simp_all)).mono by_omega ztb
    refine (FRS.ifT a2 ?_).mono le_rfl ztb
    have ok1 : okB E.W c.nmem [.subN 81071 81103 81131, .addN 81071 81071 81130] c.nreg := by
      simp only [okB, okI, regI, upd, FScr, FOut]; grind
    refine FRS.seq (K₂ := tvK E + 9) ztbbr ztiy |>.mono
      by_grind ztb
    zuhph
    have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.subN 81071 81103 81131, .addN 81071 81071 81130]
        c.nreg q := by_simp_all
    have v71 : c₁.nreg 81071 = c.nreg 81103 - c.nreg 81131 + c.nreg 81130 := by
      tauto
    have f₁ : ztkoi := fun q h => by
      zukq
    zufxb
    have hlt : c.nreg 81103 - c.nreg 81131 + c.nreg 81130 < 2 * E.M.W.n := by_omega
    refine FRS.seq (K₁ := 3) (K₂ := tvK E + 4) (Q₁ := fun c' =>
        c'.nreg 81071 = (c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n ∧
        ∀ q, q ≠ 81071 → c'.nreg q = c.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v₂, f₂⟩ => ?_) |>.mono
      by_omega ztb
    · zuhrw
      · refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨?_, f₁⟩)).mono by_omega ztb
        rw [v71, n17₁] at *
        zvmyc; ring
      · have okm : ztlyp := by
          zqyd
        refine (FRS.ifF a ztpyk).mono by_simp zthi
        have e' : zthpd :=
          by simp_all
        refine ⟨?_, fun q hq => by zvmwg; zumyf; simp_all⟩
        zqyb
        rw [v71, n17₁] at *
        zuzu
    have hv2 : zturj := by rw [v₂]; exact Nat.mod_lt _ hn
    zuizq
    refine (vTest_fs hE hB hBT hI₂ hw₂ hv2 (by unfold vsK at hroom; omega)).mono le_rfl
      (fun c' ⟨w', fr', m', g'⟩ => ⟨w', fun q a b h1 h2 => by rw [fr' q a b h1, f₂ q h2],
        fun h => m' (by rw [f₂ _ by_norm_num]; exact h), fun _ _ reg hr hch hs σb hσb hg => ?_⟩)
    zueec

  -- the step
  zubrc
  have z03 := f₁ 81103 by_norm_num by_norm_num ztod by_norm_num
  have z04 := f₁ 81104 by_norm_num by_norm_num ztod by_norm_num
  have z05 := f₁ 81105 by_norm_num by_norm_num ztod by_norm_num
  have ok2 : okB E.W c₁.nmem [.addN 81103 81103 81012, .subN 81104 81104 81012] c₁.nreg := by
    simp only [okB, okI, FScr, FOut, k1₁, z03]; grind
  refine FRS.seq (K₂ := 3) ztjiu ztcne |>.mono
    by_simp ztb
  have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem [.addN 81103 81103 81012, .subN 81104 81104 81012]
      c₁.nreg q := fun q => by rw [h₂]
  have v03 : c₂.nreg 81103 = c.nreg 81103 + 1 := by zunag; simp [regB, regI, upd, k1₁, z03]
  have v04 : c₂.nreg 81104 = c.nreg 81104 - 1 := by zunag; simp [regB, regI, upd, k1₁, z04]
  have f₂ : ∀ q, q ≠ 81103 → q ≠ 81104 → c₂.nreg q = c₁.nreg q := fun q h1 h2 => by
    zunag; zunbs
  have v05 : ztshc := by_grind
  have hw₂ := hw₁.congr' (fun q a b => f₂ q by_omega by_omega)
  have fin : ∀ c' : Config, (∀ q, q ≠ 81103 → c'.nreg q = c₂.nreg q) →
      c'.nreg 81103 = ztllc % c.nreg 81105 →
      FWin E c' ∧ c'.nreg 81103 = ztllc % c.nreg 81105 ∧
      c'.nreg 81104 = c.nreg 81104 - 1 ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81103 → q ≠ 81104 →
        c'.nreg q = c.nreg q) ∧
      ztfn ∧
      (c.nreg 81131 < c.nreg 81103 → c.nreg 81103 < c.nreg 81135 →
        ∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
          VSet E ztbcy → ∀ σb, σb ≤ 1 →
          GoodAt E reg ztbcy σb →
          c'.nreg 81007 = 1) := by
    intro c' hf h3
    have e07 : ztmuj := by
      grind
    refine ⟨hw₂.congr' by_grind, h3, by_grind,
      fun q a b h1 h2 h3 h4 => by rw [hf q h3, f₂ q h3 h4, f₁ q a b h1 h2], by_grind, fun a b reg hr hch hs σb hσb hg => by
        rw [e07]; exact g₁ a b reg hr hch hs σb hσb hg⟩
  by_cases a : c₂.nreg 81103 < c₂.nreg 81105
  · refine (FRS.ifT a (FRS.skip (K := 0) hI₂ (fin c₂ by_omega ?_))).mono by_omega
      ztb
    rw [v03] at a ⊢; rw [v05] at a; zuosw
  · have okz : okB E.W c₂.nmem [.constN 81103 0] c₂.nreg := by
      zqyd
    refine (FRS.ifF a ztpyl).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.constN 81103 0] c₂.nreg q := fun q => by zvmxl
    refine fin c' ztchy ?_
    zqyb
    rw [v03, v05] at a
    rw [show c.nreg 81103 + 1 = c.nreg 81105 by omega, Nat.mod_self]

/-! ## The leaf loop -/

/-- The arc of index `t` of the region `r`. -/
def lj (N : NF) (r t : ℕ) : ℕ := (N.region r).arcs.getD t 0

/-- The count of the arc of index `t` of the region `r`. -/
noncomputable def lcnt (Cα : Chain) (Q : Polygon) (N : NF) (r nα t : ℕ) : ℕ :=
  arcCnt nα (N.arc ztbvz).s.edge (N.arc ztbvz).e.edge
    (wBit Cα Q N.nChords (N.arc ztbvz).s.edge (N.arc ztbvz).s.hgt
      (N.arc ztbvz).e.edge (N.arc ztbvz).e.hgt)

/-- The arc of index `t` covers `x₀` (for every admissible bit). -/
def Covered (Cα : Chain) (Q : Polygon) (N : NF) (r nα t x₀ : ℕ) : Prop :=
  ∀ w, (w = 0 ∨ (chainModel Cα).key Q (N.arc ztbvz).s <
      (chainModel Cα).key Q (N.arc ztbvz).e) →
    ∃ i, i < arcCnt nα (N.arc ztbvz).s.edge (N.arc ztbvz).e.edge w ∧
      ((N.arc ztbvz).s.edge + i) % nα = x₀

/-- A good vertex of the stretch for the leaf: strictly inside, with a good host candidate. -/
def LGood (E : FEnv) (g g' L x₀ : ℕ) : Prop :=
  g' < x₀ ∧ x₀ < g' + L ∧ ∃ reg, NFRegs E.M zti E.N reg ∧ (E.N.region E.r).chords ≠ [] ∧
    VSet E ztjci ∧ ∃ σb, σb ≤ 1 ∧
      GoodAt E reg ztjci σb

/-- The setup of the leaf. -/
def leafInitL : List Instr :=
  [.addN 81114 81134 81015, .loadN 81114 81114, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .loadN 81101 81114, .constN 81100 0, .constN 81104 0,
    .addN 81115 81133 81013, .loadN 81115 81115, .addN 81105 81115 81115,
    .addN 81105 81105 81016, .subN 81109 81101 81100]

/-- The loop guard: `cnt + (na - t)`. -/
def guardL : List Instr := [.subN 81109 81101 81100, .addN 81109 81109 81104]

/-- **The leaf.** -/
def leafS (sT : Stmt) : Stmt :=
  .seq ztvdm (.whileLtN 81011 81109
    (.seq ztipu ztqct))

/-- The cost of a loop body of the leaf. -/
def lbK (E : FEnv) : ℕ := vsK E + csK + 34

/-- The registers the leaf writes. -/
def LeafW (q : ℕ) : Prop := KeyW q ∨ VertW q ∨ q = 81071 ∨ ztnhx
theorem arc_edges {Q : Polygon} {N : NF} (hNF : IsNF ztbdc Q N) {j : ℕ}
    (hj : j < N.arcs.length) :
    (N.arc j).s.edge < (chainModel Cα).W.n ∧ (N.arc j).e.edge < (chainModel Cα).W.n := by
  obtain ⟨-, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hNF
  zuls

  have h1 : ztict := by
    have := harc.2.1; have := hs.1
    show ((N.arc j).s.edge : ℝ) < _
    zulbd
  have h2 : ztics := by
    have := harc.2.2.2.1; have := he.1
    zulbd
  simp_all
theorem leafInit_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N)
    (hr : c.nreg 81121 < N.nRegions) {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztdq c₀.nmem ztcpp)
    (hC : ChainDescAt c₀.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W) :
    FRS B E.P E.W c₀ ztvdm c 15 (fun c' =>
      c'.nreg 81101 = (N.region ztfgt).arcs.length ∧ c'.nreg 81100 = 0 ∧
      c'.nreg 81104 = 0 ∧ c'.nreg 81105 = 2 * Cα.m + 7 ∧
      c'.nreg 81109 = (N.region ztfgt).arcs.length ∧
      ∀ q, q ≠ 81100 → q ≠ 81101 → q ≠ 81104 → q ≠ 81105 → q ≠ 81109 → q ≠ 81114 →
        q ≠ 81115 → c'.nreg q = c.nreg q) := by
  have hN' : ztiyn :=
    Robust.transport hN hI.hm
  zuglr
  obtain ⟨hB7, -, -, hrb, -, -⟩ := nf_bounds hN'
  zufje
  zubnp
  zuki
  zumbo
  zuese
  obtain ⟨hna, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
  zujwr
  have hm : c.nmem _ = Cα.m := hC'.2.2.2.1
  zuwl
  zubog

  have e5 : c.nmem ztfqh + c.nreg 81121 + c.nreg 81121 + c.nreg 81121 +
      c.nreg 81121 + c.nreg 81121 = c.nmem ztfqh + 5 * c.nreg 81121 := by_ring
  have ok : okB E.W c.nmem leafInitL c.nreg := by
    simp only [leafInitL, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k7, k2]
    grind
  zqyg
  have e' : ∀ q, c'.nreg q = regB c.nmem leafInitL c.nreg q := by_simp_all
  zqye
  · zqyh
  · tauto
  · tauto
  · zvmwg; simp [leafInitL, regB, regI, upd, k2, k7, hm]; ring
  · zqyh
  · zuczs
    simp only [leafInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> zvmwd <;> omega

/-- The total number of loop steps of the leaf. -/
noncomputable def lmu (Cα : Chain) (Q : Polygon) (N : NF) (r nα : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (N.region r).arcs.length, ztlqr

/-- The remaining loop steps of the leaf in the configuration `d`. -/
noncomputable def lmuAt (Cα : Chain) (Q : Polygon) (N : NF) (r nα : ℕ) (d : Config) : ℕ :=
  d.nreg 81104 + ∑ t ∈ Finset.Ico (d.nreg 81100) (N.region r).arcs.length, ztlqr
theorem arcCnt_pos : 1 ≤ arcCnt N se ee w := by unfold arcCnt; omega
theorem arcCnt_le (hN : 0 < N) : arcCnt N se ee w ≤ 2 * N := by
  zuhqp
  have := Nat.mod_lt ztqmk hN
  grind

/-- **The invariant of the leaf loop** without the guard (from the leaf's start `c`). -/
def LInv0 (E : FEnv) (c : Config) (Cα : Chain) (Nα : NF) (r g g' L : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → d.nreg q = c.nreg q) ∧
  ztdmr ∧
  d.nreg 81101 = (Nα.region r).arcs.length ∧ d.nreg 81105 = 2 * Cα.m + 7 ∧
  d.nreg 81100 ≤ (Nα.region r).arcs.length ∧
  (d.nreg 81100 = 0 → d.nreg 81104 = 0) ∧
  (0 < d.nreg 81100 →
    d.nreg 81104 ≤ lcnt Cα zti Nα r ztgb ztfqy ∧
    d.nreg 81103 = ((Nα.arc ztzmu).s.edge +
      (lcnt Cα zti Nα r ztgb ztfqy - d.nreg 81104)) %
        ztgb) ∧
  (∀ t', (t' + 1 < d.nreg 81100 ∨ (t' + 1 = d.nreg 81100 ∧ d.nreg 81104 = 0)) →
    ∀ x₀, LGood E g g' L x₀ → Covered Cα zti Nα r ztgb t' x₀ →
      d.nreg 81007 = 1) ∧
  (0 < d.nreg 81100 → ∀ x₀, LGood E g g' L x₀ → ∀ i,
    i < lcnt Cα zti Nα r ztgb ztfqy - d.nreg 81104 →
    ((Nα.arc ztzmu).s.edge + i) % ztgb = x₀ →
      d.nreg 81007 = 1)

/-- **The invariant of the leaf loop.** -/
def LInv (E : FEnv) (c : Config) (Cα : Chain) (Nα : NF) (r g g' L : ℕ) (d : Config) : Prop :=
  LInv0 E c Cα Nα r g g' L d ∧
    d.nreg 81109 = d.nreg 81104 + ((Nα.region r).arcs.length - d.nreg 81100)
theorem LInv0.congr {cs d d' : Config} {Cα : Chain} {Nα : NF} {r g g' L : ℕ}
    (h : LInv0 E cs Cα Nα r g g' L d) (he : ∀ q, q ≠ 81109 → d'.nreg q = d.nreg q) :
    LInv0 E cs Cα Nα r g g' L d' := by
  obtain ⟨hw, fr, mo, l01, l05, l00, l0, lc, ldone, lcur⟩ := h
  have e00 := he 81100 by_norm_num
  have e01 := he 81101 by_norm_num
  have e03 := he 81103 by_norm_num
  have e04 := he 81104 by_norm_num
  have e05 := he 81105 by_norm_num
  have e07 := he 81007 by_norm_num
  refine ⟨hw.congr' by_grind, fun q a b hq => by
    rw [he q (fun e => hq ztbh), fr q a b hq],
    by grind, by_omega, by_omega,
    by omega, by_omega, by_grind,
    by grind, by rw [e00, e04, e07]; omega⟩

/-- The guard keeps the invariant. -/
theorem guard_fs (hB : dBands ⊆ B) {cs : Config} {Cα : Chain} {Nα : NF}
    {r g g' L : ℕ} (hI : FInv E.W c₀ c) (h : LInv0 E cs Cα Nα r g g' L c)
    (hW : c.nreg 81104 + (Nα.region r).arcs.length ≤ E.W) :
    FRS B E.P E.W c₀ ztqct c 2 (fun c' => LInv E cs Cα Nα r g g' L c' ∧
      lmuAt Cα zti Nα r ztgb c' = lmuAt Cα zti Nα r ztgb c) := by
  have l01 := h.2.2.2.1
  have ok : okB E.W c.nmem guardL c.nreg := by
    simp only [guardL, okB, okI, regI, upd, FScr, FOut]; grind
  zqyg
  have e' : ∀ q, c'.nreg q = regB c.nmem guardL c.nreg q := by_simp_all
  have f' : ∀ q, q ≠ 81109 → c'.nreg q = c.nreg q := fun q hq => by
    zvmwg; simp [guardL, regB, regI, upd, hq]
  refine ⟨⟨h.congr f', ?_⟩, ?_⟩
  · rw [f' 81104 by_norm_num, f' 81100 by_norm_num, e']
    simp [guardL, regB, regI, upd, l01]; omega
  · unfold lmuAt; simp_all

/-- The body of the leaf loop. -/
def leafBody (sT : Stmt) : Stmt :=
  .seq ztipu ztqct

/-- **One step of the leaf loop** keeps the invariant and decreases the remaining steps. -/
theorem leaf_body (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) {cs : Config}
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs cs g g' L Dα Bα) {r : ℕ}
    (hr : cs.nreg 81121 = r) (hrn : r < Nα.nRegions) (hnW : 2 * E.M.W.n ≤ E.W)
    (h2α : 2 * ztgb ≤ E.W)
    (hWa : 2 * ztgb + (Nα.region r).arcs.length ≤ E.W)
    (hI : FInv E.W c₀ c) (hL : LInv E cs Cα Nα r g g' L c) (hg : c.nreg 81011 < c.nreg 81109)
    (hroom : c.nreg ALLOC + lbK E ≤ E.W) :
    FRS B E.P E.W c₀ (leafBody E.sT) c ztvxz (fun c' => LInv E cs Cα Nα r g g' L c' ∧
      lmuAt Cα zti Nα r ztgb c' < lmuAt Cα zti Nα r ztgb c) := by
  zqyi
  obtain ⟨⟨hw, fr, mo, l01, l05, l00, l0, lc, ldone, lcur⟩, l09⟩ := hL
  zuglu
  zuln
  have hNα := hP.hNα
  zuerw
  obtain ⟨-, -, -, regα, -, -, harcs, -, -, -, -⟩ := id hNα
  have hj : ∀ t, t < (Nα.region r).arcs.length → lj Nα r t < Nα.arcs.length := fun t ht =>
    ((harcs.2.2.2 r hrn _).1 (by
      unfold lj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
      simp)).1
  zubgm
  have nl : ∀ q, ¬ ztnhx → q ≠ 81071 → ¬ VertW q → ¬ KeyW q → ¬ LeafW q :=
    fun q a b d e h => by
      zuzp
      · grind
      · grind
      · omega
      omega
  have rg : ∀ q, 81116 ≤ q → q < 82000 → c.nreg q = cs.nreg q := fun q a b =>
    fr q by_omega by_omega (nl q by_omega by_omega ztod
      ztqj)
  have x30 : c.nreg 81130 = g := by rw [rg _ by_norm_num by_norm_num, r30]
  have x31 : c.nreg 81131 = g' := by rw [rg _ by_norm_num by_norm_num, r31]
  have x33 : c.nreg 81133 = Dα := by rw [rg _ by_norm_num by_norm_num, r33]
  have x34 : c.nreg 81134 = Bα := by rw [rg _ by_norm_num by_norm_num, r34]
  have x35 : c.nreg 81135 = g' + L := by rw [rg _ by_norm_num by_norm_num, r35]
  have x21 : c.nreg 81121 = r := by rw [rg _ by_norm_num by_norm_num, hr]
  have hna : (Nα.region r).arcs.length ≤ E.W := by_omega
  refine FRS.seq (Q₁ := fun d =>
      LInv0 E cs Cα Nα r g g' L d ∧ d.nreg 81104 ≤ 2 * ztgb ∧
      lmuAt Cα _ Nα r _ d < lmuAt Cα _ Nα r _ c) ?_
    (fun d hId _ ⟨h0, hb, hμ⟩ => (guard_fs hB hId h0 by_omega).mono le_rfl
      (fun d' ⟨h1, h2⟩ => ⟨h1, h2 ▸ hμ⟩)) |>.mono by_rfl (fun _ h => h)
  by_cases hcnt : c.nreg 81011 < c.nreg 81104
  · -- a vertex step
    have hc0 : 0 < c.nreg 81104 := by_omega
    have ht0 : 0 < c.nreg 81100 := by
      omega
    obtain ⟨lcle, lv⟩ := lc ht0
    have hnα0 : 0 < 2 * Cα.m + 7 := by_omega
    have hv : c.nreg 81103 < c.nreg 81105 := by rw [lv, l05]; exact Nat.mod_lt _ hnα0
    refine (FRS.ifT hcnt (vStep_fs hE hB hBT hI hw hv by_omega
      (by rw [x30]; exact hS.hg) (by rw [x35, x31]; have := hS.hLn; omega) hnW
      ztnvx)).mono by_omega
      (fun c₂ ⟨w₂, v₂, n₂, f₂, m₂, g₂⟩ => ?_)
    have fq : ∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c₂.nreg q = c.nreg q := fun q a b hq =>
      f₂ q a b ztbakd ztwix
        ztwix 
        ztwix
    have y00 : ztshb := f₂ _ by_norm_num by_norm_num
      ztod by_norm_num by_norm_num by_norm_num
    have y01 : c₂.nreg 81101 = c.nreg 81101 := f₂ _ by_norm_num by_norm_num
      ztod by_norm_num by_norm_num by_norm_num
    have y05 : ztshc := f₂ _ by_norm_num by_norm_num
      ztod by_norm_num by_norm_num by_norm_num
    rw [l05] at v₂
    have cur' : ∀ x₀, LGood E g g' L x₀ → ∀ i,
        i < lcnt Cα zti Nα r ztgb ztllb - c₂.nreg 81104 →
        ((Nα.arc ztbnd).s.edge + i) % ztgb = x₀ →
          c₂.nreg 81007 = 1 := by
      intro x₀ hx i hi he
      rw [n₂] at hi
      by_cases hlt : i < lcnt Cα zti Nα r ztgb ztllb - c.nreg 81104
      · exact m₂ (lcur ht0 x₀ hx i hlt he)
      · have hieq : i = lcnt Cα zti Nα r ztgb ztllb - c.nreg 81104 := by
          omega
        rw [hieq, ← lv] at he
        zulsz
        obtain ⟨a, b, reg, hreg, hch, hvs, σb, hσb, hgd⟩ := hx
        rw [x30, x31, x35] at g₂
        exact g₂ a b reg hreg hch hvs σb hσb hgd
    refine ⟨⟨w₂, fun q a b hq => by rw [fq q a b hq, fr q a b hq], by_grind,
      by omega, by_omega, by_omega, by_grind,
      fun _ => ztbbk, ?_, fun _ => by rw [y00]; omega⟩, ?_, ?_⟩
    · rw [v₂, lv, y00, n₂, Nat.mod_add_mod]
      zugjy
    · zukjv
      rw [y00] at ht'
      zugrx
      · exact m₂ (ldone t' zteg x₀ hx hcov)
      · obtain ⟨i, hi, he⟩ := hcov _ wBit_spec
        rw [show t' = c.nreg 81100 - 1 by omega] at hi he
        exact cur' x₀ hx i (by zvmzn; exact hi) he
    · rw [n₂]; have := arcCnt_le (se := (Nα.arc ztbnd).s.edge)
        (ee := (Nα.arc ztbnd).e.edge)
        (w := wBit Cα zti Nα.nChords (Nα.arc ztbnd).s.edge
          (Nα.arc ztbnd).s.hgt (Nα.arc ztbnd).e.edge
          (Nα.arc ztbnd).e.hgt) hnα0
      unfold lcnt at lcle; omega
    · unfold lmuAt; grind
  · -- an arc step
    have hc0 : c.nreg 81104 = 0 := by_omega
    have htn : c.nreg 81100 < (Nα.region r).arcs.length := by
      grind
    have hjt := hj _ htn
    obtain ⟨ese, eee⟩ := arc_edges hNα hjt
    rw [hnα] at ese eee
    refine (FRS.ifF hcnt (FRS.seq (K₂ := csK) (arcLoad_fs hE hB hI (N := Nα)
      (by rw [x34]; exact hP.hNW) by_omega by_grind
      (by rw [x21]; tauto)) (fun c₂ hI₂ hA₂ ⟨a02, a03, a06, a07, a08, af⟩ => ?_))).mono
      by_omega ztb
    rw [x21] at a02 a03 a06 a07 a08
    have af' : ∀ q, 81116 ≤ q → c₂.nreg q = c.nreg q := fun q a => af q by_omega by_omega
      by_omega by_omega by_omega by_omega by_omega
    have z05 : c₂.nreg 81105 = 2 * Cα.m + 7 := by
      rw [af _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num, l05]
    have z00 : ztshb := af _ by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num
    have hne : 0 < Nα.nChords → (Nα.F ztbdc zti).Nonempty := fun h =>
      ⟨_, _, Dec.chord_mem h, rfl⟩
    refine (cntS_fs hE hB hI₂ (N := Nα) (by rw [af' _ by_norm_num, x34]; exact hP.hNW)
      (by zuoaj; exact hP.hwf)
      (by zuoaj; exact hP.hD) hP.hWm (by rw [a03, z05]; tauto) (by rw [a07, z05]; tauto)
      by_omega
      (fun h => by rw [a03, a06, a07, a08]; exact arc_posOK hsimp hNα (hne h) hjt)
      by_omega ztnvx).mono le_rfl
      (fun c₃ ⟨b04, b10, b00, bf⟩ => ?_)
    have bf' : ∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c₃.nreg q = c.nreg q := fun q a b hq => by
      have h1 : ¬ CsW q := fun h => by
        zuzp
        · exact hq zteg
        all_goals exact hq ztbh
      rw [bf q by_omega by_omega h1, af q ztwix
        ztwix
        ztwix
        ztwix
        ztwix
        ztwix
        ztwix]
    have nCs : ∀ q, (q = 81007 ∨ q = 81008 ∨ q = 81009 ∨ q = 81010 ∨ q = 81101 ∨ q = 81103 ∨
        q = 81105) → c₃.nreg q = c₂.nreg q := fun q hq =>
      bf q by_omega by_omega (by unfold CsW KeyW; omega)
    have c07 : c₃.nreg 81007 = c.nreg 81007 := by
      rw [nCs _ by_omega, af _ by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num by_norm_num]
    have hw₃ := hw.congr' (fun q a b => by
      rw [nCs q by_omega, af q by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega])
    have hlc : c₃.nreg 81104 = lcnt Cα zti Nα r ztgb zthuz := by
      rw [b04, b10, a03, a06, a07, a08, z05]; rfl
    have hv3 : c₃.nreg 81103 = (Nα.arc (lj Nα r zthuz)).s.edge := by
      rw [nCs _ by_omega, a03]; rfl
    rw [z00] at b00
    have hlpos : 1 ≤ lcnt Cα zti Nα r ztgb zthuz := arcCnt_pos
    refine ⟨⟨hw₃, fun q a b hq => by rw [bf' q a b hq, fr q a b hq], fun h => by
      grind, by rw [nCs _ by_omega, af _ by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num by_norm_num by_norm_num, l01],
      by rw [nCs _ by_omega, z05], by_omega, by_grind,
      fun _ => ⟨by rw [b00, hlc]; simp, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · rw [b00, hlc, hv3, Nat.add_sub_cancel, Nat.sub_self, Nat.add_zero,
        Nat.mod_eq_of_lt ese]
    · zukjv
      rw [b00, hlc] at ht'
      rw [c07]
      zugrx
      · rcases Nat.lt_or_ge _ _ with h' | h'
        · exact ldone t' zthrp x₀ hx hcov
        · exact ldone t' by_omega x₀ hx hcov
      · omega
    · intro _ x₀ _ i hi
      rw [b00, hlc] at hi
      grind
    · rw [hlc]; unfold lcnt; exact arcCnt_le by_omega
    · unfold lmuAt
      rw [b00, hlc, hc0, Finset.sum_eq_sum_Ico_succ_bot htn]
      omega

/-- **The leaf**: every good vertex of the stretch covered by an arc of the leaf region sets the
success flag. -/
theorem leaf_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs c g g' L Dα Bα) {r : ℕ}
    (hr : c.nreg 81121 = r) (hrn : r < Nα.nRegions) (hnW : 2 * E.M.W.n ≤ E.W)
    (h2α : 2 * ztgb ≤ E.W)
    (hWa : 2 * ztgb + (Nα.region r).arcs.length ≤ E.W)
    (hroom : c.nreg ALLOC + 15 + ztczt * lmu Cα zti Nα r ztgb ≤ E.W) :
    FRS B E.P E.W c₀ (leafS E.sT) c
      (15 + (ztczt * lmu Cα zti Nα r ztgb + 2)) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c'.nreg q = c.nreg q) ∧
      ztfn ∧
      ∀ t', t' < (Nα.region r).arcs.length → ∀ x₀, LGood E g g' L x₀ →
        Covered Cα zti Nα r ztgb t' x₀ → c'.nreg 81007 = 1) := by
  zuiww
  zqyi
  refine FRS.seq (K₁ := 15) (leafInit_fs hE hB hI (N := Nα) ztgfz
    by_omega (by zupao; exact hP.hwf) (by zupao; exact hP.hD) hP.hWm)
    (fun c₁ hI₁ hA₁ ⟨i01, i00, i04, i05, i09, fi⟩ => ?_)
  zvnel at i01 i09
  have fr₁ : ∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c₁.nreg q = c.nreg q := fun q a b hq =>
    fi q ztwix
      ztwix
      ztwix
      ztwix
      ztwix
      ztwix
      ztwix
  have e07 : ztmve := by_grind
  have hL₁ : LInv E c Cα Nα r g g' L c₁ := by
    refine ⟨⟨hw.congr' by_grind, fr₁, by_grind, i01, i05,
      by omega, by_omega, by_grind, by_grind,
      by grind⟩, by_omega⟩
  have hμ₁ : lmuAt Cα zti Nα r ztgb c₁ = lmu Cα zti Nα r ztgb := by
    unfold lmuAt lmu; rw [i04, i00, Finset.range_eq_Ico]; simp
  zucna
  refine (FRS.while (a := 81011) (b := 81109) (body := leafBody E.sT) (LInv E c Cα Nα r g g' L)
    (lmuAt Cα zti Nα r ztgb) ztvxz ztpbj
    (fun d hId hd hgd hroomd => leaf_body hE hB hBT hP hR' hr hrn hnW h2α hWa hId hd hgd hroomd)
    hI₁ hL₁ by_grind).mono (by rw [hμ₁]) (fun c' ⟨hL', hex⟩ => ?_)
  · obtain ⟨⟨-, -, -, -, -, l00, -, -, -, -⟩, l09⟩ := hd
    unfold lmuAt
    by_cases hc : 0 < d.nreg 81104
    · omega
    · have htn : d.nreg 81100 < (Nα.region r).arcs.length := by_omega
      rw [Finset.sum_eq_sum_Ico_succ_bot htn]
      omega
  · obtain ⟨⟨hw', fr', mo', l01, l05, l00, l0, lc, ldone, lcur⟩, l09⟩ := hL'
    have z11 : c'.nreg 81011 = 0 := by
      rw [fr' _ by_norm_num by_norm_num (by unfold LeafW KeyW VertW; omega)]
      grind
    refine ⟨hw', fr', mo', fun t' ht' x₀ hx hcov => ldone t' ?_ x₀ hx hcov⟩
    rw [z11] at hex
    omega
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs NFLoc

/-- Load the root code. -/
def rootL : List Instr :=
  [.addN 81150 81134 81016, .addN 81150 81150 81013, .loadN 81150 81150, .constN 81142 0]

/-- The parity of the code: `81121 = x / 2`, `81151 = 1 - x mod 2`. -/
def parS : Stmt :=
  .seq ztoxv (.seq halfS (Stmt.block [.subN 81151 81012 81122]))

/-- The cost bound of `parS`. -/
def paK (E : FEnv) (x : ℕ) : ℕ := halfK E.P.n x + 2
variable {E : FEnv} {c₀ c : Config}
theorem halfK_mono {n x y : ℕ} (h : x ≤ y) : halfK n x ≤ halfK n y := by
  unfold halfK
  have := Nat.div_le_div_right (c := 2 * (n / 2)) h
  omega
theorem ndK_mono {x y : ℕ} (h : x ≤ y) : ndK E x ≤ ndK E y := by
  unfold ndK clK
  have := halfK_mono (n := E.P.n) h
  omega
theorem rootLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N) :
    FRS B E.P E.W c₀ ztvdo c 4 (fun c' =>
      c'.nreg 81150 = N.root ∧ c'.nreg 81142 = 0 ∧
      ∀ q, q ≠ 81150 → q ≠ 81142 → c'.nreg q = c.nreg q) := by
  have hN' : ztiyn :=
    Robust.transport hN hI.hm
  zuglr
  obtain ⟨hB7, -⟩ := nf_bounds hN'
  have hB11 :=
    robust_addr fun m' hm' => (hN m' hm').2.2.2.2.1
  zubnp
  zuki
  zubog

  have ok : okB E.W c.nmem rootL c.nreg := by
    simp only [rootL, okB, okI, regI, upd, FScr, FOut, k7, k2]; grind
  zucpb
  have e' : ∀ q, c'.nreg q = regB c.nmem rootL c.nreg q := by_simp_all
  refine ztfcz
  · zvmwg; simp [rootL, regB, regI, upd, k7, k2]; exact hNA.2.2.2.1
  · tauto
  · zvmwg; simp [rootL, regB, regI, upd, h1, h2]
theorem parS_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    (hroom : c.nreg ALLOC + paK E ztmgm ≤ E.W) :
    FRS B E.P E.W c₀ parS c (paK E ztmgm) (fun c' =>
      c'.nreg 81121 = c.nreg 81150 / 2 ∧ c'.nreg 81151 = 1 - c.nreg 81150 % 2 ∧
      ∀ q, ¬ ztnhy → q ≠ 81151 → c'.nreg q = c.nreg q) := by
  have ok1 : ztmwh := by
    zuph
  refine FRS.seq (K₂ := halfK E.P.n ztmgm + 1) ztbbr
    ztiy |>.mono (by unfold paK; grind) ztb
  have e₁ : ztiei := by_simp_all
  have v20 : c₁.nreg 81120 = c.nreg 81150 := by_tauto
  have f₁ : ztkoj := fun q h => by
    zukq
  zuhwm
  refine FRS.seq (K₂ := 1) (halfS_fs hE hB hI₁ v20 (by rw [hA₁']; unfold paK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨h21, h22, f₂⟩ => ?_)
  zubrb
  have ok3 : okB E.W c₂.nmem [.subN 81151 81012 81122] c₂.nreg := by
    zuph
  zucpc
  have e' : ∀ q, c'.nreg q = regB c₂.nmem [.subN 81151 81012 81122] c₂.nreg q := by_simp_all
  refine ztfcz
  · zukqq
  · zvmwg; simp [regB, regI, upd, k1, h22]
  · zvmwg; zundw
    grind

/-- A valid decomposition code. -/
def VCode (N : NF) (x : ℕ) : Prop :=
  ztkgw ∨ ztkgx
theorem VCode.le {N : NF} {x : ℕ} (h : VCode N x) : x ≤ 2 * ztnnc + 1 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The registers the descent writes. -/
def DescW (q : ℕ) : Prop := NodeW q ∨ LeafW q ∨ q = 81151 ∨ q = 81142

/-- The completeness clause of the descent at the code `x` (from the descent's start `c`). -/
def DComp (E : FEnv) (c₀ c : Config) (Cα : Chain) (Nα : NF) (g g' L : ℕ) (f x : ℕ) : Prop :=
  ∀ (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ),
    DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T →
    aj = E.M.key zti ztke →
    ztceg → f = 1 ∨ Nα.Below x T

/-- **The invariant of the descent loop** (from the descent's start `c`). -/
def DInv (E : FEnv) (c₀ c : Config) (Cα : Chain) (Nα : NF) (g g' L : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → d.nreg q = c.nreg q) ∧
  ztdmr ∧ VCode Nα ztmio ∧
  d.nreg 81151 = 1 - d.nreg 81150 % 2 ∧ d.nreg 81121 = d.nreg 81150 / 2 ∧
  Nα.parentCode^[d.nreg 81142] ztmio = Nα.root ∧
  (∀ t, t < d.nreg 81142 → Nα.parentCode^[t] ztmio ≠ Nα.root) ∧
  DComp E c₀ c Cα Nα g g' L ztqlt ztmio

/-- The body of the descent loop. -/
def descBody (sT : Stmt) : Stmt :=
  .seq (nodeS sT) (.seq parS (Stmt.block [.addN 81142 81142 81012]))

/-- The largest code of a normal form. -/
def maxCode (N : NF) : ℕ := 2 * ztnnc + 1

/-- The cost of a descent step. -/
def dbK (E : FEnv) (N : NF) : ℕ := ndK E ztkas + paK E ztkas + 1
theorem desc_body (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) {cs : Config}
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs cs g g' L Dα Bα) {dd : ℕ}
    (hDd : IsDecomp Nα dd)
    (hJ : cs.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztrbo)
    (hdW : dd + 1 ≤ E.W)
    (hI : FInv E.W c₀ c) (hL : DInv E c₀ cs Cα Nα g g' L c) (hg : c.nreg 81011 < c.nreg 81151)
    (hroom : c.nreg ALLOC + dbK E Nα ≤ E.W) :
    FRS B E.P E.W c₀ (descBody E.sT) c zttix (fun c' => DInv E c₀ cs Cα Nα g g' L c' ∧
      dd + 1 - c'.nreg 81142 < dd + 1 - c.nreg 81142) := by
  obtain ⟨hw, fr, mo, hv, h51, h21, hpath, hnot, hcomp⟩ := hL
  zubgm
  have hev : c.nreg 81150 % 2 = 0 := by_omega
  have hk : c.nreg 81150 / 2 < Nα.nChords := by rcases hv with h | h <;> omega
  have hx : c.nreg 81150 = 2 * ztlld := by_omega
  -- the depth bound
  have hdep : c.nreg 81142 ≤ dd := by
    obtain ⟨j, hj, hjr⟩ := hDd.2.2.2.2.2.2.1 ztmgm ztrpt
    grind
  have nd : ∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → ¬ NodeW q := fun q _ _ h h' => h zthrp
  have rg : ∀ q, ztgzl → c.nreg q = cs.nreg q := fun q h =>
    fr q by_omega by_omega (fun h' => by
      rcases h' with h' | h' | h' | h'
      · unfold NodeW KeyW VertW at h'; omega
      · unfold LeafW KeyW VertW at h'; omega
      · omega
      · omega)
  zuqv
  have hRc : SRegs c g g' L Dα Bα := ⟨by_grind, by_grind,
    by grind, by_grind, by_grind,
    by grind⟩
  have hJc : c.nreg 81140 < E.M.W.n ∧
      ProperPos E.M zti E.P.n ztke := by
    grind
  have hx' : 2 * ztlld ≤ maxCode Nα := by unfold maxCode; omega
  refine FRS.seq (K₁ := ndK E (2 * ztlld)) (K₂ := paK E ztqti + 1)
    (node_fs hE hB hBT hI hw hP hRc hJc hx hk (by
      have := ndK_mono (E := E) hx'; unfold dbK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨w₂, f₂, m₂, lh₂, raw₂⟩ => ?_) |>.mono
    (by unfold dbK; have := ndK_mono (E := E) hx'; omega) ztb
  -- the child
  set k := c.nreg 81150 / 2 with hkdef
  have hchild : VCode Nα ztmid ∧ c₂.nreg 81150 ≠ Nα.root ∧
      Nα.parentCode ztmid = 2 * k := by
    have h9 := hDd.2.2.2.2.2.2.2.2.1 k hk _ lh₂
    refine ⟨h9.2, h9.1, ?_⟩
    rcases lh₂ with h | h <;> zvmwc
    · exact (hDd.2.2.1 k hk).1
    · exact (hDd.2.2.1 k hk).2
  obtain ⟨hv₂, hnr₂, hpar₂⟩ := hchild
  have hx₂ : c₂.nreg 81150 ≤ maxCode Nα := hv₂.le
  have hnd := ndK_mono (E := E) hx'
  have hpk : paK E ztmid ≤ paK E ztqti := by
    have := halfK_mono (n := E.P.n) hx₂; unfold paK; omega
  have hroom2 : c₂.nreg ALLOC + paK E ztmid ≤ E.W := by unfold dbK at hroom; omega
  refine FRS.seq (K₂ := 1) (parS_fs hE hB hI₂ hroom2)
    (fun c₃ hI₃ hA₃ ⟨p21, p51, f₃⟩ => ?_) |>.mono
    by_omega ztb
  have k1 : c₃.nreg 81012 = 1 := by rw [hI₃.hin _ ztbc, hE.k1]
  have y42 : c₃.nreg 81142 = c.nreg 81142 := by
    rw [f₃ _ by_omega by_norm_num, f₂ _ by_norm_num by_norm_num
      (by unfold NodeW KeyW VertW; omega)]
  have ok : okB E.W c₃.nmem [.addN 81142 81142 81012] c₃.nreg := by
    simp only [okB, okI, FScr, FOut, k1, y42]; grind
  refine (FRS.block hB _ hI₃ ok).mono by_simp ztqnl
  have e₄ : ∀ q, c₄.nreg q = regB c₃.nmem [.addN 81142 81142 81012] c₃.nreg q := fun q => by
    zumok
  have f₄ : ∀ q, q ≠ 81142 → c₄.nreg q = c₃.nreg q := fun q h => by
    zunce; zundx
  have v42 : c₄.nreg 81142 = c.nreg 81142 + 1 := by zunce; simp [regB, regI, upd, k1, y42]
  have z50 : c₄.nreg 81150 = c₂.nreg 81150 := by
    zugcu
  have z07 : c₄.nreg 81007 = c₂.nreg 81007 := by
    zugcu
  refine ⟨⟨w₂.congr' (fun q a b => by rw [f₄ q by_omega, f₃ q by_omega by_omega]),
    fun q a b hq => ?_, fun h => by_grind, by_grind,
    by rw [f₄ _ by_norm_num, p51, z50], by rw [f₄ _ by_norm_num, p21, z50],
    by rw [v42, z50, Function.iterate_succ_apply, hpar₂, ← hx]; omega, fun t ht => ?_,
    fun reg ai bi aj bj dX regα T hD hJ' hJr' => ?_⟩, by_omega⟩
  · rw [f₄ q ztwix,
      f₃ q ztwxe
        ztwix, f₂ q a b (nd q a b hq), fr q a b hq]
  · rw [v42] at ht
    rw [z50]
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · exact hnr₂
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ztgpo
      rw [Function.iterate_succ_apply, hpar₂, ← hx]
      exact hnot s by_omega
  · rw [z07, z50]
    rcases hcomp reg ai bi aj bj dX regα T hD hJ' hJr' with h | hb
    · grind
    · by_cases hf₂ : c₂.nreg 81007 = 1
      · omega
      · right
        have h0 : ztpni := by have := w₂.1; omega
        zvnly at hb
        exact node_dec hE hP hRc hD ztiim
          ztiim hw hk hb raw₂ h0

/-- **The descent of a stretch.** -/
def descS (sT : Stmt) : Stmt :=
  .seq ztvdo (.seq parS (.seq (.whileLtN 81011 81151 (descBody sT)) (leafS sT)))

/-- A bound on the leaf steps of every region. -/
noncomputable def lmuB (Cα : Chain) (Q : Polygon) (N : NF) : ℕ :=
  (Finset.range N.nRegions).sup (fun r => lmu Cα Q N r ztgb)

/-- The cost bound of the descent. -/
noncomputable def descK (E : FEnv) (Cα : Chain) (N : NF) (dd : ℕ) : ℕ :=
  4 + (paK E ztkas + ((ztjtw * ztnxn + 2) +
    (15 + (ztczt * lmuB Cα zti N + 2))))
theorem desc_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs c g g' L Dα Bα) {dd : ℕ}
    (hDd : IsDecomp Nα dd) (hdW : dd + 1 ≤ E.W)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hnW : 2 * E.M.W.n ≤ E.W) (h2α : 2 * ztgb ≤ E.W)
    (hWa : ∀ r, r < Nα.nRegions → 2 * ztgb + (Nα.region r).arcs.length ≤ E.W)
    (hroom : c.nreg ALLOC + descK E Cα Nα dd ≤ E.W) :
    FRS B E.P E.W c₀ (descS E.sT) c (descK E Cα Nα dd) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → c'.nreg q = c.nreg q) ∧
      ztfn ∧
      ∀ (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ),
        DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T →
        aj = E.M.key zti ztke →
        ztceg → c'.nreg 81007 = 1) := by
  zuiww
  zuqv
  have k0c := k0_of hE hI
  have hv0 : VCode Nα Nα.root := hDd.2.2.2.2.2.2.2.2.2
  -- the root
  refine FRS.seq (K₁ := 4) (K₂ := descK E Cα Nα dd - 4)
    (rootLoad_fs hE hB hI (N := Nα) ztgfz)
    (fun c₁ hI₁ hA₁ ⟨v50, v42, f₁⟩ => ?_) |>.mono ztqgk ztb
  have hpk : paK E ztvmt ≤ paK E ztqti := by
    have := halfK_mono (n := E.P.n) (v50 ▸ hv0.le : c₁.nreg 81150 ≤ maxCode Nα); unfold paK; omega
  refine FRS.seq (K₁ := paK E ztvmt)
    (K₂ := (ztqlv * ztnxn + 2) + (15 + ztykk))
    (parS_fs hE hB hI₁ ztnvq)
    (fun c₂ hI₂ hA₂ ⟨p21, p51, f₂⟩ => ?_) |>.mono ztqgk ztb
  have g₂ : ∀ q, 81011 ≤ q → q < 83000 → ¬ DescW q → c₂.nreg q = c.nreg q := fun q a b hq => by
    rw [f₂ q ztwxe
      ztwix,
      f₁ q ztwxe
        ztwix]
  have y50 : c₂.nreg 81150 = Nα.root := by
    grind
  have y42 : c₂.nreg 81142 = 0 := by
    grind
  have e07 : ∀ q, 81007 ≤ q → q ≤ 81010 → c₂.nreg q = c.nreg q := fun q a b => by
    rw [f₂ q by_omega by_omega, f₁ q by_omega by_omega]
  have hL₂ : DInv E c₀ c Cα Nα g g' L c₂ := by
    refine ⟨hw.congr' e07, g₂, fun h => by rw [e07 _ le_rfl by_norm_num]; exact h,
      by grind, by_omega,
      by omega, by rw [y42, y50]; rfl, by_grind,
      fun reg ai bi aj bj dX regα T hD _ _ => Or.inr (by rw [y50]; exact below_root hDd hD.hT)⟩
  -- the loop
  have nDW : ∀ q, (q = 81011 ∨ ztgzl ∨ q = 81007) → ¬ DescW q := fun q hq h => by
    zuzp
    · unfold NodeW KeyW VertW at h; omega
    · unfold LeafW KeyW VertW at h; omega
    · omega
    · omega
  refine FRS.seq (K₁ := ztqlv * ztnxn + 2)
    (K₂ := 15 + ztykk)
    ((FRS.while (a := 81011) (b := 81151) (body := descBody E.sT) (DInv E c₀ c Cα Nα g g' L)
      (fun d => dd + 1 - d.nreg 81142) zttix ztpbj
      (fun d hId hd hgd hroomd => desc_body hE hB hBT hP hR' hDd hJ hdW hId hd hgd hroomd)
      hI₂ hL₂ (by rw [y42, Nat.sub_zero]; unfold descK at hroom; omega)).mono
      by_simp ztb)
    (fun c₃ hI₃ hA₃ ⟨hL₃, hex⟩ => ?_) |>.mono le_rfl ztb
  · obtain ⟨-, frd, -, hvd, h51d, -, -, hnotd, -⟩ := hd
    rw [frd _ by_norm_num by_norm_num ztzxf, k0c, h51d] at hgd
    have hk : d.nreg 81150 / 2 < Nα.nChords := by rcases hvd with h | h <;> omega
    obtain ⟨j, hj, hjr⟩ := hDd.2.2.2.2.2.2.1 _ ztrpt
    have : d.nreg 81142 ≤ j := by
      zumv
      exact hnotd j by_omega hjr
    omega
  obtain ⟨hw₃, fr₃, mo₃, hv₃, h51₃, h21₃, -, -, hcomp₃⟩ := hL₃
  rw [fr₃ _ by_norm_num by_norm_num ztzxf, k0c, h51₃] at hex
  have hodd : c₃.nreg 81150 % 2 = 1 := by_omega
  have hrn : c₃.nreg 81150 / 2 < Nα.nRegions := by rcases hv₃ with h | h <;> omega
  have rg₃ : ∀ q, ztgzl → c₃.nreg q = c.nreg q := fun q h =>
    fr₃ q by_omega by_omega (nDW q by_omega)
  have hR₃ : SRegs c₃ g g' L Dα Bα := ⟨by rw [rg₃ _ by_omega, r30], by rw [rg₃ _ by_omega, r31],
    by rw [rg₃ _ by_omega, r32], by rw [rg₃ _ by_omega, r33], by rw [rg₃ _ by_omega, r34],
    by rw [rg₃ _ by_omega, r35]⟩
  have hlm : lmu Cα _ Nα _ _ ≤ lmuB Cα _ Nα :=
    Finset.le_sup (f := fun r => lmu Cα zti Nα r _) (Finset.mem_range.2 hrn)
  have hlm' := Nat.mul_le_mul_left ztczt hlm
  refine (leaf_fs hE hB hBT hI₃ hw₃ hP hR₃ h21₃ hrn hnW h2α (hWa _ hrn)
    ztnvq).mono by_omega
    (fun c' ⟨w', f', m', gl⟩ => ⟨w', fun q a b hq => by
      rw [f' q a b ztbakd, fr₃ q a b hq], fun h => m' (mo₃ h), ?_⟩)
  intro reg ai bi aj bj dX regα T hD hJa hJr
  rcases hcomp₃ reg ai bi aj bj dX regα T hD hJa hJr with h | hb
  · omega
  have hx2 : c₃.nreg 81150 = 2 * (c₃.nreg 81150 / 2) + 1 := by_omega
  rw [hx2] at hb
  have hrT := leaf_target hDd hrn hD.hT hb
  zuglu
  zuln
  have hGα : ztebh := Or.inl ztkir
  zuerw
  have hXn : ztmvt := by
    rw [hnα]; have := hD.hXL; have := hS.hgL; omega
  obtain ⟨t, ht, hjt, hcl⟩ := arc_of_target hGα hP.hNα hD hXn
  rw [← hrT] at ht hjt hcl
  refine gl t ht zttks ⟨by have := hD.hX0; omega, by have := hD.hXL; omega, reg, hD.hregs,
    hD.hch, ?_, ?_⟩ ?_
  · zunkq
    intro C hC
    exact hD.hinB C hC (hS.memM hD.hXL le_rfl one_pos)
  · zunkq; exact hD.hgX
  · zucdk
    unfold lj at hw ⊢
    obtain ⟨-, -, -, regβ, -, -, -, -, -, -, hpp⟩ := hP.hNα
    obtain ⟨hs, he⟩ := hpp _ hjt
    obtain ⟨ese, eee⟩ := arc_edges hP.hNα hjt
    rw [hnα] at ese eee hXn
    exact arc_int ese eee (by unfold Model.key; zuofw) (by unfold Model.key; zuntj)
      (by unfold Model.key; zuntk) (by unfold Model.key; linarith [he.2.1]) hw hXn hcl
