module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvStopFin6
public import Chazelle.Core.SweepIoBruteLoop
public import Chazelle.Core.SweepEvGenR
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.SweepEvPrep

namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
namespace Cand1
def BruteBody (bruteS : Stmt → Stmt) (κB : ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      SymPtIn c sO s → s.Lt P.n → s.eval zta = z → z ∉ J.left.set →
      |z.1| < J.whole.radius → |z.2| < J.whole.radius → z.2 ≤ J.left.top.2 → c.nreg bL = 1 →
      AccOK P accA ztdm J.whole.radius z ztba L c →
      c.nreg ALLOC + κB * ztyz * ztwju ≤ W →
      IRS P W c₀ ztqek c ztbaps
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius z
              ztba L' c' ∧ L ⊆ L' ∧
            ztbakr ∧
            (FreeAt J.left z ztba →
              J.left.hitParam z ztba ∈ L')) ∧
          PartFr c c')
theorem bruteBody_of (h : BruteSpec) : ∃ bruteS κB, BruteBody bruteS κB := h

/-- The body of `TabStepSpec`. -/
def TabBody (tabB : Stmt) (κT : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ)
    (z : Point),
    AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
    c.nreg qJ < 2 * N₂.nChords → endOrigin J zta N₂ ztccx = z →
    endDir ztccx = dirOf ztql →
    z ∈ J.right.set → z ≠ J.shared → z ≠ J.right.top →
    AccOK P accA ztdm J.whole.radius z ztba L c →
    c.nreg ALLOC + κT ≤ W →
    IRS P W c₀ tabB c κT
      (fun c' =>
        (∃ L', AccOK P accA ztdm J.whole.radius z
            ztba L' c' ∧ L ⊆ L' ∧
          ztwjm ∧
          (J.whole.hitParam z ztba ∈ L' ∨
            J.whole.hitParam z ztba = J.right.hitParam z ztba)) ∧
        CandFr c c')
theorem tabBody_of (h : TabStepSpec) : ∃ tabB κT, TabBody tabB κT := h

/-- The body of `ShrStepSpec`. -/
def ShrBody (shrB : Stmt → Stmt) (κS : ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      1 ≤ c.nreg qH → c.nreg qH ≤ P.n → ((Qof P).vtx ztbmn).2 = J.shared.2 →
      FreeAt J.whole J.shared ztba → c.nreg bL = 1 →
      AccOK P accA ztdm J.whole.radius J.shared
        ztba L c →
      c.nreg ALLOC + ztbakn ≤ W →
      IRS P W c₀ ztiax c
        ztbakn
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius J.shared
              ztba L' c' ∧ L ⊆ L' ∧
            ztxar ∧
            J.left.hitParam J.shared ztba ∈ L') ∧
          CandFr c c')
theorem shrBody_of (h : ShrStepSpec) : ∃ shrB κS, ShrBody shrB κS := h

/-! ## The branches -/
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}

/-- `bL = 1` from the run-time test. -/
theorem bL_one (hq : QState P J 1 z c) (hK : Consts c₂) (fr : CandFr c c₂)
    (hb : c₂.nreg K0 < c₂.nreg bL) : c.nreg bL = 1 := by
  have := hq.hbL.1; rw [hK.1, candFr_bL fr] at hb; omega
theorem bL_zero (hq : QState P J 1 z c) (hK : Consts c₂) (fr : CandFr c c₂)
    (hb : ¬ c₂.nreg K0 < c₂.nreg bL) : ¬ z.2 ≤ J.left.top.2 := fun h => by
  have := (hq.hbL.2).2 h; rw [hK.1, candFr_bL fr] at hb; omega
theorem modB_left {l r : ℕ} (h : l = 1) : ModB J l r 0 = J.left := by simp [ModB, h]

/-- **The box class.** -/
theorem boxB_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hbox : c.nreg qE = 1 ∨ c.nreg qE = 3)
    (hroom : c₂.nreg ALLOC + lhsK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ ztmcr c₂ (lhsK ztdg ztwiu zto + 2)
      ztio := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, -, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  zubqo

  zugky

  unfold boxB
  zumiy
  · zudoj

    obtain ⟨hgL, hposL, hparL⟩ := lhGeo_boxL hbox hgeo by_simp_all
      by_simp_all
    have h := lhsL_irs (e := qE) hsh hBs hXl hA ztnvj hI₂ (z := z)
      (by rw [eE, cm_n]; omega)
      (by zvpby; unfold ProperPos; rw [hparL]; tauto)
      by_simp_all
      by_tauto
      by_omega
      (by zunle; exact hM.1) by_norm_num (modB_left hb1) rfl hroom
    zuevu
    rintro c' ⟨⟨L', a', s', g', geo'⟩, fr', hA', hm'⟩
    zudts

    have hM' := mid_step hM a' s'
      ztcca
      (candFr_lhw fr' hA' hm')
    zulfa
  · zufgn

/-- **The brute-force class.** -/
theorem bruteB_irs {bruteS : Stmt → Stmt} {κB : ℕ} (hBr : BruteBody bruteS κB)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hnb : ¬ ztbvu) (hns : z ≠ J.shared)
    (hroom : c₂.nreg ALLOC + (16707 + κB * ztyz * ztwju) ≤ W) :
    IRS P W c₀ ztepp c₂
      (16707 + κB * ztyz * ztwju + 2)
      ztio := by
  zucv
  obtain ⟨hzC, -, hcls⟩ := tour_set J.right zta hpc hnb hpp.1 hpp.2.1
  zukwo
  zubqo

  zugky

  unfold bruteB
  zumiy
  · zudoj

    have hsym := callSym_irs (re := qE) (rh := qH) (o := sw 3230) hI₂
      (AEnv.ctxR hA hI₂) by_decide by_decide
      by_omega by_simp_all
      by_simp_all by_simp_all by_omega
    refine IRS.seq hsym ?_
    rintro c₃ hI₃ hA₃ hA₃' ⟨sp, hsp, hlt, hev, hfr3, hal3, hm3⟩
    have fr3 := candFr_regs (S := fun r => sw 3230 ≤ r ∧ r ≤ sw 3233)
      zthhc
      (fun r a b d => hfr3 r a (by unfold sw at b ⊢; omega) d) hal3 hm3
    have fr3' := candFr_trans fr fr3
    have eD3 := candFr_qD fr3'
    have eL3 := candFr_bL fr3'
    have eR3 := candFr_bR fr3'
    rw [eE, eH, hzpos] at hev
    have hacc3 : AccOK P accA (ModB J (c₃.nreg bL) (c₃.nreg bR)) J.whole.radius z
        (dirOf (c₃.nreg qD)) L c₃ := by
      rw [eD3, eL3, eR3]
      exact hM.1.transport (fun j hj => by
        rw [hfr3 _ ztxld
          zthk ztbjo])
    have hab := abs_lt_whole hzC
    have h := hBr sh Bs F X Ok hsh hBs hXl P W c₀ c₃ J H N₁ N₂ E L sp z hA hI₃
      by_tauto hlt hev (not_mem_left hA.hP hzC hns)
      hab.1 hab.2 h₁ by_omega hacc3 by_omega
    zuevu
    rintro c' ⟨⟨L', a', s', g', geo'⟩, pf⟩
    rw [eD3, eL3, eR3] at a'
    rw [eD3] at g' geo'
    have hM' := mid_step hM a' s'
      ztcca
      (candFr_trans fr3 (candFr_part pf))
    exact fin1 hq hM' (fun _ => geo' (freeAt_left_of J h₁ hq.hfree))
  · zufgn

/-- **A regular endpoint query**: the table step. -/
theorem tab_irs {tabB : Stmt} {κT : ℕ} (hT : TabBody tabB κT)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hnb : ¬ ztbvu)
    (hj : c.nreg qJ < 2 * N₂.nChords)
    (hend : ztccw = (sweepEndQ N₂.chords).getD ztccx ztt)
    (hns : z ≠ J.shared) (hnt : z ≠ J.right.top) (hroom : c₂.nreg ALLOC + κT ≤ W) :
    IRS P W c₀ tabB c₂ κT ztio := by
  zucv
  obtain ⟨hzC, -, -⟩ := tour_set J.right zta hpc hnb hpp.1 hpp.2.1
  zukwo
  obtain ⟨ho, hd⟩ := endQ_facts hA.hNF₂ hj hend
  rw [hzpos] at ho
  zumar
  zulhd
  zudxt

  have h := hT P W X Ok J H N₁ N₂ E c₀ c₂ L z hA hI₂ by_omega
    by_simp_all by_simp_all hzC hns hnt
    ztirn hroom
  zuyf

  exact fin2 (mid_step hM a' s' g' fr') hh

/-- **The shared vertex.** -/
theorem shr_irs {shrB : Stmt → Stmt} {κS : ℕ} (hS : ShrBody shrB κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c) (hI₂ : IInv W c₀ c₂)
    (hM : Mid P J z c c₂ L) (hzs : z = J.shared)
    (hroom : c₂.nreg ALLOC +
      ztbaov ≤ W) :
    IRS P W c₀ ztiax c₂ ztbaov
      ztio := by
  zucv
  subst hzs
  zumar
  have eH := candFr_qH fr
  zudxt

  have h₁ := J.left.snd_le_top_of_mem_set J.shared_mem_left
  have hb1 := (hq.hbL.2).2 h₁
  have h := hS sh Bs F X Ok hsh hBs hXl P W c₀ c₂ J H N₁ N₂ E L hA hI₂
    by_omega by_omega by_simp_all
    (by zunle; exact hq.hfree) by_omega ztirn hroom
  zuyf

  have hM' := mid_step hM a' s'
    ztcca fr'
  zulfa
end Cand1
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
namespace Cand1
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}
variable {a b : ℕ} {t e : Stmt} {K K' : ℕ} {Q : Config → Prop}
theorem irs_ifEq' (hK : K + 4 ≤ K')
    (ht : c.nreg a = c.nreg b → IRS P W c₀ t c K Q)
    (he : c.nreg a ≠ c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ ztqri c K' Q :=
  (irs_ifEq ht he).mono hK ztb
theorem irs_ite' (hK : K + 2 ≤ K')
    (ht : c.nreg a < c.nreg b → IRS P W c₀ t c K Q)
    (he : ¬ c.nreg a < c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ ztva c K' Q :=
  (IRS.ite ht he).mono hK ztb

/-- `Mid` survives a step writing only `sw 4800 … 4999` (and the oracle bands). -/
theorem mid_keep {c₃ : Config} (hM : Mid P J z c c₂ L)
    (h : ∀ r, bandOf r ∉ oracleBands → (r < sw 4800 ∨ sw 4999 < r) → r ≠ ALLOC →
      c₃.nreg r = c₂.nreg r)
    (ha : c₂.nreg ALLOC ≤ c₃.nreg ALLOC) (hm : ∀ a, a < c₂.nreg ALLOC → c₃.nmem a = c₂.nmem a) :
    Mid P J z c c₃ L := by
  refine mid_step hM (hM.1.transport (fun j hj => h _
    ztxld
    zthk ztbjo)) subset_rfl
    (fun τ hτ => Or.inl hτ) ?_
  exact candFr_regs (S := fun r => sw 4800 ≤ r ∧ r ≤ sw 4999)
    zthhc
    (fun r a b d => h r a by_omega d) ha hm

/-- The budget of the decision tree (the leaves). -/
def kD (κT κS LK KB : ℕ) : ℕ := 16749 + κT + κS + LK + KB
section Tree
variable {tabB : Stmt} {shrB bruteS : Stmt → Stmt} {κT κS κB KB : ℕ}

/-- The common hypotheses of the decision tree at the state `c₂`. -/
structure TreeH (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c c₂ : Config) (z : Point)
    (L : Set ℝ) (F : ℕ → ℕ) (κB KB : ℕ) : Prop where
  hA : AEnv P W X Ok J H N₁ N₂ E c₀
  hq : QState P J 1 z c
  hend : c.nreg qJ < 2 * N₂.nChords →
    ztccw = (sweepEndQ N₂.chords).getD ztccx ztt
  hKB : BruteQ J N₂ ztccx z →
    κB * ztyz * ztwju ≤ KB
  hI₂ : IInv W c₀ c₂
  hM : Mid P J z c c₂ L
  hnb : ¬ ztbvu
  vE : c₂.nreg qE = c.nreg qE
  vy : c₂.nreg y34 = 2 * J.m₂ + 6
  vk : c₂.nreg k2 = N₂.nChords
  vj : c₂.nreg jx = c.nreg qJ - N₂.nChords
  vt : c₂.nreg tgt = 6 + midT J.right
  v41 : c₂.nreg ztbex = cstR J 1
  hK : Consts c₂
variable (hT : TabBody tabB κT) (hS : ShrBody shrB κS) (hBr : BruteBody bruteS κB)
  (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)

/-- The position facts of a tour query. -/
theorem tree_pos (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB) :
    (chainModel J.right).pos zta zthz = z ∧
      c.nreg qE < (chainModel J.right).W.n ∧
      0 ≤ (chainModel J.right).param zta zthz ∧
      (chainModel J.right).param zta zthz < 1 := by
  obtain ⟨hzpos, hqE, hpp, -⟩ := q1_facts h.hq
  exact ⟨hzpos, hqE, hpp.1, hpp.2.1⟩
include hT in
theorem leaf_tab (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB)
    (hj : c.nreg qJ < 2 * N₂.nChords) (hns : z ≠ J.shared) (hnt : z ≠ J.right.top)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK ztdg ztwiu
      zto) KB ≤ W) :
    IRS P W c₀ tabB c₂ (kD κT κS ztbajg KB)
      ztio :=
  (tab_irs hT h.hA h.hq h.hI₂ h.hM h.hnb hj (h.hend hj) hns hnt
    zthfx).mono (by unfold kD; omega) (fun _ h => h)
include hS hsh hBs hXl in
theorem leaf_shr (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB) (hzs : z = J.shared)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK ztdg ztwiu
      zto) KB ≤ W) :
    IRS P W c₀ ztiax c₂
      (kD κT κS ztbajg KB)
      ztio :=
  (shr_irs hS hsh hBs hXl h.hA h.hq h.hI₂ h.hM hzs
    zthfx).mono (by unfold kD; omega) (fun _ h => h)
include hBr hsh hBs hXl in
theorem leaf_brute (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB)
    (hbq : BruteQ J N₂ ztccx z) (hns : z ≠ J.shared)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK ztdg ztwiu
      zto) KB ≤ W) :
    IRS P W c₀ ztepp c₂
      (kD κT κS ztbajg KB)
      ztio := by
  have hk := h.hKB hbq
  exact (bruteB_irs hBr hsh hBs hXl h.hA h.hq h.hI₂ h.hM h.hnb hns
    zthfx).mono (by unfold kD; omega) (fun _ h => h)
include hT hBr hsh hBs hXl in
/-- **A vertex position other than the shared vertex.** -/
theorem topT_irs (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB) (hns : z ≠ J.shared)
    (h0 : (chainModel J.right).param zta zthz = 0)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK ztdg ztwiu
      zto) KB ≤ W) :
    IRS P W c₀ ztlue c₂
      (kD κT κS ztbajg KB + 14)
      ztio := by
  zueui
  have htop := top_iffR h.hA.hP zta hx hp0 hp1
  rw [hzpos] at htop
  dsimp only at htop
  zumfk
  zugyd
  unfold topT
  refine irs_ite' (K := KK + 12) by_omega zthxe zthxe
  · zucjl
    have hj' : c.nreg qJ < 2 * N₂.nChords := by_omega
    refine irs_ifEq' (K := KK + 8) by_omega ztdnv ztdnv
    · zuiid
      exact (leaf_brute hBr hsh hBs hXl h (Or.inr (htop.2 ztryu)) hns hroom).mono
        by_omega ztb
    · refine irs_ifEq' (K := KK + 4) by_omega zteez zteez
      · zucjk
        zujxd
        exact (leaf_brute hBr hsh hBs hXl h (Or.inr (htop.2 ⟨h0, Or.inr ztvbv⟩))
          hns hroom).mono by_omega (fun _ h => h)
      · refine irs_ifEq' (K := KK) le_rfl zthxc zthxc
        · zuiic
          exact leaf_brute hBr hsh hBs hXl h (Or.inr (htop.2 ⟨h0, Or.inr (Or.inr e'')⟩)) hns
            hroom
        · zuiid
          zucjk
          zuiic
          have hnt : z ≠ J.right.top := fun hz => by
            simp_all
          exact leaf_tab hT h hj' hns hnt hroom
  · zucjl
    exact (leaf_brute hBr hsh hBs hXl h ztec hns hroom).mono by_omega
      ztb
include hT hS hBr hsh hBs hXl in
/-- **The decision tree** of a tour position. -/
theorem dec_irs (h : TreeH P W X Ok J H N₁ N₂ E c₀ c c₂ z L F κB KB)
    (vH : c₂.nreg tH = nhgt ztj zta zthz)
    (hroom : c₂.nreg ALLOC + kD κT κS (lhsK ztdg ztwiu
      zto) KB ≤ W) :
    IRS P W c₀ ztgqk c₂
      (kD κT κS ztbajg KB + 28)
      ztio := by
  zueui
  have hsh' := shared_iffR h.hA.hP zta hx hp0 hp1
  rw [hzpos] at hsh'
  dsimp only at hsh'
  zugyd
  have k0 := h.hK.1
  zumfk
  have hz0 := nhgt_eq_zero_iff ztj zta zthz
  refine irs_ite' (K := KK + 26) by_omega ztrqi ztrqi
  · -- parameter positive
    zuilc
    have hne : (chainModel J.right).param zta zthz ≠ 0 :=
      fun e => by_simp_all
    have hns : ztsno := fun e => hne (hsh'.1 e).1
    have hnt : z ≠ J.right.top := fun e => by
      have := (top_iffR h.hA.hP zta hx hp0 hp1).1 by_simp_all
      simp_all
    unfold genT
    refine irs_ite' (K := KK) by_omega zthxe zthxe
    · zucjl
      exact leaf_tab hT h by_omega hns hnt hroom
    · zucjl
      exact leaf_brute hBr hsh hBs hXl h ztec hns hroom
  · -- parameter zero
    zuilc
    have h0 : (chainModel J.right).param zta zthz = 0 :=
      hz0.1 by_omega
    unfold zeroT
    refine irs_ifEq' (K := KK + 22) by_omega ztdnv ztdnv
    · zuiib
      exact (leaf_shr hS hsh hBs hXl h (hsh'.2 ztryu) hroom).mono by_omega
        ztb
    · zuiib
      refine irs_ifEq' (K := KK + 18) by_omega zteez zteez
      · zucjk
        refine irs_ifEq' (K := KK + 14) by_omega zthxc zthxc
        · zuiia
          zujxd
          exact (leaf_shr hS hsh hBs hXl h (hsh'.2 ⟨h0, Or.inr ⟨e1, e''⟩⟩) hroom).mono
            by_omega ztb
        · zuiia
          have hns : ztsno := fun hz => by
            simp_all
          exact topT_irs hT hBr hsh hBs hXl h hns h0 hroom
      · zucjk
        have hns : ztsno := fun hz => by
          simp_all
        exact (topT_irs hT hBr hsh hBs hXl h hns h0 hroom).mono by_omega ztb
end Tree
end Cand1
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
namespace Cand1
theorem prepL_val (m f : ℕ → ℕ) :
    regB m prepL f tE = f qE ∧ regB m prepL f tH = f qH ∧
      regB m prepL f y34 = f zthy - f K1 ∧ regB m prepL f k2 = m ztbaht ∧
      regB m prepL f jx = f qJ - m ztbaht ∧
      (∀ q, (q < sw 4800 ∨ sw 4806 < q) → regB m prepL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩ <;>
    simp [prepL, regB, regI, upd, tE, tH, y34, k2, jx, sw, qE, qH, qJ, K1]
  unfold sw at hq
  grind
theorem prepL_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m prepL f := by
  have s : ∀ j, 4800 ≤ j → j ≤ 4806 → IScr ztgc := fun j h1 h2 =>
    iscr_sw ztce ztce
  simp only [prepL, okB, okI]
  tauto
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}
variable {tabB : Stmt} {shrB bruteS : Stmt → Stmt} {κT κS κB KB : ℕ}
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000 in
/-- **A tour position.** -/
theorem tourB_irs (hT : TabBody tabB κT) (hS : ShrBody shrB κS) (hBr : BruteBody bruteS κB)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c)
    (hend : c.nreg qJ < 2 * N₂.nChords →
      ztccw = (sweepEndQ N₂.chords).getD ztccx ztt)
    (hKB : BruteQ J N₂ ztccx z →
      κB * ztyz * ztwju ≤ KB)
    (hI₂ : IInv W c₀ c₂) (hM : Mid P J z c c₂ L) (hnb : ¬ ztbvu)
    (hroom : c₂.nreg ALLOC + (kD κT κS (lhsK ztdg ztwiu
      zto) KB + 11068) ≤ W) :
    IRS P W c₀ ztqxk c₂
      (kD κT κS ztbajg KB + 11068)
      ztio := by
  zucv
  obtain ⟨-, h6, -⟩ := tour_set J.right zta hpc hnb hpp.1 hpp.2.1
  simp only at h6
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -, -, -, -, -⟩ := hA.hst
  obtain ⟨KK, hKK⟩ : ∃ KK, KK = kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      zto) KB := ⟨_, rfl⟩
  rw [← hKK] at hroom ⊢
  zubqo

  zulhd
  zuheg
  obtain ⟨p1, p2, p3, p4, p5, po⟩ := prepL_val c₂.nmem c₂.nreg
  zumvf
  refine (IRS.seq (K₁ := 5) (K₂ := 11015 + (20 + (KK + 28)))
    ((IRS.block prepL hI₂ (prepL_ok c₂.nmem c₂.nreg)).mono by_rfl ztb)
    ?_).mono by_omega (fun _ h => h)
  zubup
  simp only at hA₃ hA₃'
  have hA3 : regB c₂.nmem prepL c₂.nreg ALLOC = c₂.nreg ALLOC :=
    po _ by_decide
  have hM₃ : Mid P J z c { c₂ with nreg := regB c₂.nmem prepL c₂.nreg } L :=
    mid_keep hM (fun r _ hr _ => po r (by unfold sw at hr ⊢; omega)) by_omega
      ztcj
  zulil
  have hns := normS_irs (dsc := sw 21) (pe := tE) (ph := tH) (o := nO) hI₃ hK₃
    (AEnv.ctxR hA hI₃) by_decide by_decide
    by_simp_all
    by_simp_all
    (fun h => by
      simp_all)
    by_grind
  refine IRS.seq hns ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨n1, n2, n3, n4, n5⟩
  simp only at n1 n2 n3 n4 n5 hA₄ hA₄'
  have hM₄ : Mid P J z c c₄ L := mid_keep hM₃
    (fun r a b d => n3 r a (by unfold sw at b; unfold tH sw; omega)
      ztjrf ztjrf d) n4 n5
  have hK₄ := hA.hK.fix hI₄
  refine IRS.seq (midB_irs hI₄ hK₄ (AEnv.ctxR hA hI₄)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨t1, t2, t3⟩
  have tA : ztcrj := t2 _ (by unfold OutM ALLOC sw; omega)
  have hM₅ : Mid P J z c c₅ L := mid_keep hM₄ (fun r _ hr _ => t2 r (by unfold OutM; unfold sw at hr ⊢; omega))
    (by rw [tA]) (fun a _ => by rw [t3])
  -- the values at `c₅`
  have k3 : ∀ q, OutM q → q ≠ tH → q ≠ nO → q ≠ nO + 1 → q ≠ ALLOC → bandOf q ∉ oracleBands →
      c₅.nreg q = regB c₂.nmem prepL c₂.nreg q := fun q a b d e f g => by
    grind
  have nb : ztcge := fun q h1 h2 =>
    not_oracle_sw h1 h2
  have h34' : c₂.nreg zthy = 2 * J.right.m + 7 := by
    rw [hI₂.hin _ by_trivial]; omega
  have k1 : ztgat := hK₂.2.1
  have hNF : c₂.nmem (c₂.nreg ztbz) = N₂.nChords := by
    zugdf
    exact (hA.hN₂ c₂.nmem (fun a ha => hI₂.hm a (by have := hA.hE; omega))).1
  have hm : ztdjs := rfl
  have tree : TreeH P W X Ok J H N₁ N₂ E c₀ c c₅ z L F κB KB :=
    { hA := hA, hq := hq, hend := hend, hKB := hKB, hI₂ := hI₅, hM := hM₅, hnb := hnb
      vE := candFr_qE hM₅.2.2.2
      vy := by
        rw [k3 y34 (by unfold OutM y34 sw; omega) by_decide
          by_decide by_decide
          by_decide (nb _ by_decide
          by_decide), p3, h34', k1, hm]
        omega
      vk := by
        rw [k3 k2 (by unfold OutM k2 sw; omega) by_decide
          by_decide by_decide
          by_decide (nb _ by_decide
          by_decide), p4, hNF]
      vj := by
        rw [k3 jx (by unfold OutM jx sw; omega) by_decide
          by_decide by_decide
          by_decide (nb _ by_decide
          by_decide), p5, hNF, eJ]
      vt := t1
      v41 := by
        rw [hI₅.hin _ by_trivial]; grind
      hK := hA.hK.fix hI₅ }
  have vH : c₅.nreg tH = nhgt ztj zta zthz := by
    rw [t2 tH (by unfold OutM tH sw; omega), n2, p1, p2, eE, eH]
  have hd := dec_irs hT hS hBr hsh hBs hXl tree vH by_omega
  grind
set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000 in
/-- **The candidate step of side `1`.** -/
theorem cand1P_irs (hT : TabBody tabB κT) (hS : ShrBody shrB κS) (hBr : BruteBody bruteS κB)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) (hq : QState P J 1 z c)
    (hend : c.nreg qJ < 2 * N₂.nChords →
      ztccw = (sweepEndQ N₂.chords).getD ztccx ztt)
    (hKB : BruteQ J N₂ ztccx z →
      κB * ztyz * ztwju ≤ KB)
    (hacc0 : c.nreg accA = 0)
    (hroom : c.nreg ALLOC + (lhsK ztdg ztwiu zto +
      (kD κT κS ztbajg KB + 11076)) ≤ W) :
    IRS P W c₀ (cand1P tabB shrB bruteS sh) c
      (lhsK ztdg ztwiu zto +
        (kD κT κS ztbajg KB + 11076))
      ztio := by
  zucv
  obtain ⟨LK, hLK⟩ : ∃ LK, LK = lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) :=
    ⟨_, rfl⟩
  obtain ⟨KK, hKK⟩ : ∃ KK, KK = kD κT κS LK KB := zths
  have hKK' : KK = 16749 + κT + κS + LK + KB := by_tauto
  rw [← hLK, ← hKK] at hroom ⊢
  have hbr1 : ztpmh := (hq.hbR.2).2 hz₂
  have hMod : ModB J ztcpq ztcpr 1 = J.right := by
    zujpw
  have hloc : ztbvu ∨ (6 ≤ c.nreg qE ∧ z ∈ J.right.set) := by
    by_cases hb : c.nreg qE = 1 ∨ c.nreg qE = 3
    · omega
    · obtain ⟨hzC, h6, -⟩ := tour_set J.right zta hpc hb hpp.1 hpp.2.1
      simp_all
  have hlhs := lhsR_irs (e := qE) (t := 1) hsh hBs hXl hA ztnvj hI
    hqE hpp hzpos habs hloc (accOK_init accA _ _ _ _ hacc0) by_norm_num hMod rfl
    by_omega
  rw [← hLK] at hlhs
  unfold cand1P
  refine IRS.seq (K₁ := LK) (K₂ := KK + 11076) hlhs ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨L', a', s', g', geo'⟩, fr', hA', hm'⟩
  have hM : Mid P J z c c₁ L' := ⟨a', fun τ hτ => (g' τ hτ).elim (fun h => absurd h by_simp)
    (fun h => ⟨h.1, onCB_of_right J h.2⟩), geo' hgeo, candFr_lhw fr' hA' hm'⟩
  zulii
  have eE := candFr_qE hM.2.2.2
  have hbox : ∀ hb : c.nreg qE = 1 ∨ c.nreg qE = 3,
      IRS P W c₀ ztmcr c₁ (KK + 11068) ztio := by
    zuhgn
    have h := boxB_irs hsh hBs hXl hA hq hI₁ hM hb by_omega
    rw [← hLK] at h
    exact h.mono by_omega ztb
  refine irs_ifEq' (K := KK + 11072) by_omega ztdnv ztdnv
  · zuihq
    exact (hbox ztccj).mono by_omega ztb
  · zuihq
    refine irs_ifEq' (K := KK + 11068) by_omega zteez zteez
    · zuihr
      simp_all
    · zuihr
      have ht := tourB_irs hT hS hBr hsh hBs hXl hA hq hend hKB hI₁ hM
        by_omega by_grind
      simp_all
end Cand1
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def shO : ℕ := sw 4840

/-- **The shared-vertex step.** -/
def shrB (sh : Stmt) : Stmt :=
  .seq (callArr ztiw ztbuy K0 qD shO) (Cand1.lhs ztbbz ztea ztna ztfum 0 sh)
set_option maxHeartbeats 4000000 in
/-- **The shared-vertex step of a side-1 query.** -/
theorem shrStep : ShrStepSpec := by
  refine ⟨shrB, 35007, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L hA hI hq1 hqn hqh hfree hbL hacc hroom
  zujnf
  zubkr
  zuhee
  zuiwt
  zuhg
  have h46 : ztzje := by
    zuiis
  zudpw
  obtain ⟨hlt, hpp0, hpos0⟩ := Cand1.shared_posL hP zta P.n
  have hsL : J.shared ∈ J.left.set := J.shared_mem_left
  have hsT : J.shared.2 ≤ J.left.top.2 := J.left.snd_le_top_of_mem_set hsL
  have hyR : ztsns := by
    rw [radius_left J]; exact (Cand1.abs_lt_whole J.shared_mem_right).2
  have hctx := AEnv.ctxL hA hI
  have hPL : J.left.P.Simple := hctx.2.2.2.2.1
  have hlK : 8 ≤ Cand1.lhsK ztdg ztwiu zto := by
    unfold Cand1.lhsK; omega
  -- the arrival position of the shared vertex
  refine (IRS.seq (K₁ := 35007) (callArr_irs (dsc := sw 20) (re := sw 46) (rh := K0) (rd := qD)
    (o := shO) hI hctx by_decide by_decide
    by_omega by_simp_all by_simp_all
    by_omega) ?_).mono le_rfl (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨hArr, fr1, hal1, hm1⟩
  rw [h46, k0] at hArr
  unfold ArrAt at hArr
  rw [hpos0] at hArr
  obtain ⟨-, hon, hoff⟩ := hArr
  have fr1' : ∀ r, 240000 ≤ r → r < 250000 → (r < shO ∨ shO + 2 < r) → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1 r ztsg by_omega by_omega by_omega
      ztu
  have qD1 : ztizm := fr1' _ by_decide by_decide
    by_decide
  have qH1 : c₁.nreg qH = c.nreg qH := fr1' _ by_decide by_decide
    by_decide
  have hfL : FreeAt J.left J.shared σ := freeAt_left_of J hsT hfree
  obtain ⟨p, t, harr⟩ := (freeAt_iff_arr J.left hPL hσ (Or.inl hsL)).1 hfL
  have f1 : c₁.nreg shO = 1 := by
    grind
  obtain ⟨hpn, -, harr'⟩ := hon f1
  obtain ⟨hgeo, hposx, hparx⟩ := Cand1.lhGeo_arr harr' (h := c.nreg qH - 1) by_omega hqh hsT
    (d := c.nreg qD) rfl
  have eH : ztmuq := Nat.sub_add_cancel hq1
  rw [eH] at hgeo hposx hparx
  obtain ⟨-, ht0, ht1, -, -⟩ := harr'
  have hacc₁ : AccOK P accA ztdm J.whole.radius J.shared
      ztqma L c₁ := by
    rw [qD1]
    exact hacc.transport (fun i hi => fr1' _ zthk
      zthk (by unfold accA shO sw; omega))
  have hpp : ProperPos ztbw zta P.n ⟨c₁.nreg ztfum, c₁.nreg qH⟩ := by
    rw [qH1]; exact ⟨by_grind, by_grind, hqn⟩
  have hloc : (c₁.nreg ztfum = 1 ∨ c₁.nreg ztfum = 3) ∨
      (6 ≤ c₁.nreg ztfum ∧ J.shared ∈ J.left.set) := by
    have hc := posClass_of (C := J.left) (Q := Qof P) (x := ⟨c₁.nreg ztfum, c.nreg qH⟩) hpn
      by_grind by_grind by_grind
      ztzz
    rcases hc with h | h | h
    · grind
    · grind
    grind
  have hMod : ModB J ztcpq ztcpr 0 = J.left := by simp [ModB, hbL]
  refine (Cand1.lhsL_irs (e := shO + 1) (t := 0) hsh hBs hXl hA (by unfold Cand1.OutL shO sw; omega)
    hI₁ hpn hpp by_grind hyR hloc hacc₁ by_norm_num hMod (radius_left J)
    by_omega).mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', geo'⟩, fr, hal, hm⟩
  rw [qD1] at a' g' geo'
  refine ⟨⟨L', a', s', g', geo' by_grind⟩,
    fun r hr0 hr1 hr2 hr3 hr4 => ?_, hal1.trans hal, fun a ha => ?_⟩
  · rw [fr r hr0 (by unfold LHW sw at *; omega) hr4]
    exact fr1 r hr0 ztggu ztggu
      ztggu hr4
  grind
open Chazelle.Chain (sidePt)
def tbA : ℕ := sw 4820
/-- The flag of the table entry. -/
def tbF : ℕ := sw 4821
/-- The walk edge of the table entry. -/
def tbE : ℕ := sw 4822
/-- The height code of the table entry. -/
def tbH : ℕ := sw 4823
/-- The tag `2` (the walk of `C`). -/
def tbT : ℕ := sw 4824

/-- The loads of the table entry `qJ`. -/
def tabL : List Instr :=
  [.copyN tbA ztps, .addN tbA tbA qJ, .addN tbA tbA qJ, .addN tbA tbA qJ, .loadN tbF tbA,
    .addN tbA tbA K1, .loadN tbE tbA, .addN tbA tbA K1, .loadN tbH tbA, .constN tbT 2]

/-- **The table step.** -/
def tabB : Stmt := .seq (block tabL) (.ifLtN tbF K1 .skip (offer accA ztjl tbE tbH tbT qD))

/-- The cost of the table step. -/
def tabK : ℕ := offerK + 20
theorem tabL_val (m f : ℕ → ℕ) (hk : f K1 = 1) :
    regB m tabL f tbA = f ztps + 3 * f qJ + 2 ∧
      regB m tabL f tbF = m (f ztps + 3 * f qJ) ∧
      regB m tabL f tbE = m (f ztps + 3 * f qJ + 1) ∧
      regB m tabL f tbH = m (f ztps + 3 * f qJ + 2) ∧
      regB m tabL f tbT = 2 ∧
      ∀ q, ztofb → regB m tabL f q = f q := by
  zufvb
  simp only [tabL, regB, regI, upd, tbA, tbF, tbE, tbH, tbT, sw, qJ, K1]
  grind
theorem tabL_ok {W : ℕ} (m f : ℕ → ℕ) (hk : f K1 = 1)
    (hW : f ztps + 3 * f qJ + 2 ≤ W) : okB W m tabL f := by
  zufvb
  have hW' : f 240302 + 3 * f 243227 + 2 ≤ W := hW
  have s : ∀ i, 4820 ≤ i → i ≤ 4824 → IScr ztcdy := fun i h1 h2 =>
    iscr_sw ztce ztce
  simp only [tabL, okB, okI, regI, upd, tbA, tbF, tbE, tbH, tbT, qJ, K1, sw]
  norm_num [hk']
  refine ⟨s 4820 by_norm_num by_norm_num, ztiop,
    ⟨s 4820 by_norm_num by_norm_num, ?_⟩, ⟨s 4820 by_norm_num by_norm_num, ?_⟩,
    s 4821 by_norm_num by_norm_num, ztiop,
    s 4822 by_norm_num by_norm_num, ztiop,
    s 4823 by_norm_num by_norm_num, ⟨s 4824 by_norm_num by_norm_num, ?_⟩⟩ <;> omega
set_option maxHeartbeats 4000000 in
/-- **The table step of a regular endpoint query of side `1`.** -/
theorem tabStep : TabStepSpec := by
  refine ⟨tabB, tabK, ?_⟩
  intro P W X Ok J H N₁ N₂ E c₀ c L z hA hI hj hz hd hzR hzs hzt hacc hroom
  zuhee
  zucnb
  set j := c.nreg qJ with hjdef
  zujnf
  zubkr
  have hB : c.nreg ztps = rd c₀ bSweep 302 := hI.hin _ by_trivial
  zumey
  have hAl := hI.hA
  have hroom' : c.nreg ALLOC + offerK + 20 ≤ W := by_tauto
  have hW : c.nreg ztps + 3 * c.nreg qJ + 2 ≤ W := by
    omega
  have hmem : ∀ i, i ≤ 2 → c.nmem (c.nreg ztps + 3 * c.nreg qJ + i) =
      c₀.nmem (rd c₀ bSweep 302 + 3 * j + i) := by
    zug
    rw [hB]
    zuitj
  -- the facts of the table entry
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTab, hFl⟩ := hA.hout
  have hT := hTab j hj by_simp_all by_simp_all by_simp_all
  obtain ⟨hf1, hPW⟩ := hFl j hj
  have hfree : FreeAt J.whole z σ := by
    simp_all
  have hz2 : ztsnr := J.whole.snd_le_top_of_mem_set (J.right_set_subset hzR)
  obtain ⟨hτ0, hon⟩ := hit_onCB J.whole hz2 hσ hfree
  -- the loads
  refine IRS.seq (K₁ := 10) (K₂ := offerK + 2) (IRS.block tabL hI (tabL_ok _ _ k1 hW)) ?_ |>.mono
    by_decide ztb
  zugn
  obtain ⟨-, vF, vE, vH, vT, vo⟩ := tabL_val c.nmem c.nreg k1
  have o1 : ∀ q, ztofb → c₁.nreg q = c.nreg q := fun q hq => by
    simp_all
  zufp
  have f1 : c₁.nreg tbF = c₀.nmem zteap := by
    zvmwl; simp only; rw [vF]; simpa using hmem 0 by_norm_num
  have e1 : c₁.nreg tbE = c₀.nmem (rd c₀ bSweep 302 + 3 * j + 1) := by
    simp_all
  have h1 : c₁.nreg tbH = c₀.nmem (rd c₀ bSweep 302 + 3 * j + 2) := by
    simp_all
  have t1 : c₁.nreg tbT = 2 := by_simp_all
  have a1 : ztdc := o1 _ by_decide
  have k1₁ : ztcpf := (hA.hK.fix hI₁).2.1
  have qD1 : ztizm := o1 _ by_decide
  have acc1 : AccOK P accA ztdm J.whole.radius z σ L c₁ :=
    hacc.transport (fun i hi => o1 _ (by unfold accA tbA sw; omega))
  have fr1 : ∀ r, ¬ ztbwg → c₁.nreg r = c.nreg r := fun r hr =>
    o1 r (by unfold tbA tbT sw at *; omega)
  refine IRS.ite ztyr ztrqe
  · -- no entry: the first hit of `C` is that of `C₂`
    have hf0 : c₀.nmem zteap ≠ 1 := by_omega
    zuhxp

    rw [ite_eq_right hf0] at hT2
    rw [hz, hd] at hT2
    refine IRS.skip hI₁ ⟨⟨L, acc1, subset_rfl, fun τ h => Or.inl h, Or.inr hT2⟩,
      fun r _ _ _ h3 _ => fr1 r h3, by rw [a1], fun a _ => by zvnmf⟩
  · -- an entry: offer the first hit of `C`
    have hf : ztbacn := by_omega
    obtain ⟨hPe, hPp, -⟩ := hPW hf
    zuhxp

    rw [ite_eq_left hf] at hT2
    obtain ⟨-, hpt, -⟩ := hT2
    rw [hz, hd] at hpt
    have hM2 : ModB J ztcpq ztcpr (c₁.nreg tbT) = J.whole := by
      rw [t1]; rfl
    have hW3 : ztmd := by have := hA.hWh; unfold hostWords at this; omega
    have sw' : ∀ i, i < 10000 → 240000 ≤ sw i ∧ sw i < 250000 := fun i hi => by
      zumvd
    refine (offer_irs (A := accA) (dsc := sw 2) (e := tbE) (h := tbH) (t := tbT) (dR := qD)
      (Mod := ModB J ztcpq ztcpr) (R₀ := J.whole.radius) (z := z) (L := L)
      (τ := J.whole.hitParam z σ) hI₁ hA.hK hA.hG hW3
      by_decide
      by_decide
      by_decide
      by_grind (by rw [t1])
      (by zupdf; exact AEnv.ctxW hA hI₁) (by zupdf)
      by_grind by_grind
      (by rw [hM2, e1, h1, qD1]; exact hpt) (Cand1.abs_lt_whole hzR).2
      by_omega).mono le_rfl ?_
    rintro c' ⟨hacc', hk, hal, hm⟩
    rw [qD1] at hacc'
    refine ⟨⟨insert ztbyn L, hacc', Set.subset_insert _ _, fun τ hτ => ?_,
      Or.inl ztfoq⟩, fun r hr0 hr1 hr2 hr3 hr4 => ?_, by_omega,
      fun a ha => by rw [hm a by_omega, m1]⟩
    · grind
    · rw [hk r hr0 ztmer hr4]
      grind
namespace Cand1
theorem lhsK_le (T Fg D : ℕ) : lhsK T Fg D ≤ SweepEv.κGen D * ztbbs := by
  have := SweepEv.genK_le Fg D T
  unfold SweepEv.genK at this
  unfold lhsK
  omega
end Cand1
set_option maxRecDepth 200000 in
open Classical in
/-- **The candidate step of side `1`**, from the contracts of its parts. -/
theorem cand1Spec_of (hB : BruteSpec) (hT : TabStepSpec) (hS : ShrStepSpec) : Cand1Spec := by
  obtain ⟨bruteS, κB, hBr⟩ := Cand1.bruteBody_of hB
  obtain ⟨tabB, κT, hTb⟩ := Cand1.tabBody_of hT
  obtain ⟨shrB, κS, hSb⟩ := Cand1.shrBody_of hS
  refine ⟨Cand1.cand1P tabB shrB bruteS,
    fun D => 2 * SweepEv.κGen D + κB + κT + κS + 30000, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E z hA hI hq hend hacc0 hroom
  zubmr
  obtain ⟨KB, hKB⟩ : ∃ KB, KB = (if BruteQ J N₂ (c.nreg qJ) z then
      ztwxr * ztyz *
        ztwju else 0) := ⟨_, rfl⟩
  rw [← hKB] at hroom ⊢
  have hKB' : BruteQ J N₂ ztccx z →
      κB * ztyz * ztwju ≤ KB := by
    grind
  have hLK := Cand1.lhsK_le ztdg ztwiu zto
  have h1 : κB + κT + κS + 30000 ≤
      ztokv * ztwit :=
    Nat.le_mul_of_pos_right _ by_omega
  have e : ztwxr *
      ztwit =
      2 * (SweepEv.κGen zto * ztwit) +
        ztokv * ztwit := by_ring
  have hcost : Cand1.lhsK ztdg ztwiu zto +
      (Cand1.kD κT κS (Cand1.lhsK ztdg ztwiu zto) KB +
        11076) ≤
      ztwxr *
        ztwit + KB := by
    unfold Cand1.kD; omega
  exact (Cand1.cand1P_irs hTb hSb hBr hsh hBs hXl hA hI hq hend hKB' hacc0
    by_omega).mono hcost (fun _ h => h)

/-- **The candidate step of side `1`** (piece F). -/
theorem cand1Spec (hB : BruteSpec) : Cand1Spec := cand1Spec_of hB tabStep shrStep
open Chazelle.Chain (sideLeft sideInArc)
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable (J : Merge.Junction) (i : ℕ)
theorem sideChain_cases {i : ℕ} (hi : i ≤ 1) :
    (i = 0 ∧ sideChain J i = J.left) ∨ (i = 1 ∧ sideChain J i = J.right) := by
  zueve
  · tauto
  tauto
theorem sideChain_P : (sideChain J i).P = J.P := by
  zulcd
theorem sideChain_radius :
    (sideChain J i).radius = J.whole.radius := FuseMath.radius_of_P J (sideChain_P J i)
theorem sideChain_set : (sideChain J i).set ⊆ J.whole.set := by
  zumuo
  · exact J.left_set_subset
  · exact J.right_set_subset
theorem sideChain_top : (sideChain J i).top.2 ≤ J.whole.top.2 := by
  zumuo
  · exact J.left_top_le
  · exact J.right_top_le

/-- **The facts of a query point.** -/
theorem query_facts {Q : Polygon} {i : ℕ} {q : ℕ × ℕ × ℕ}
    (hq : QueryOK J Q i q) :
    PosClass ztgi Q ztpo ∧
    |((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2| < J.whole.radius ∧
    ((chainModel ztgi).pos Q ztpo).2 ≤ (sideChain J i).top.2 ∧
    ((chainModel ztgi).pos Q ztpo).2 ≤ J.whole.top.2 ∧
    ((chainModel ztgi).pos Q ztpo ∈ J.whole.set ∨
      (|((chainModel ztgi).pos Q ⟨q.1, q.2.1⟩).1| = J.whole.radius ∧
        |((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩).2| < J.whole.radius)) := by
  obtain ⟨he, -, -, h0, h1, htop, hsec⟩ := hq
  zullu
  have hsec' : sideLeft (chainModel ztgi).W q.1
      ((chainModel ztgi).param Q ztpo)
      (rayPt ztxjt zthwj 1) := by
    rw [show rayPt _ _ 1 =
      (((chainModel _).pos Q ztpo).1 + dirOf q.2.2,
        ((chainModel _).pos Q ztpo).2) by
      unfold rayPt; zuoev]
    omega
  have hy := query_abs he h0 h1 htop hσ hsec'
  have hR := sideChain_radius J i
  zuher
  refine ⟨hcls, by_simp_all, htop, htop.trans (sideChain_top J i), ?_⟩
  rcases posClass_pt hcls h0 h1 hy with h | ⟨h, h'⟩
  · exact Or.inl (sideChain_set J i h)
  simp_all

/-- **The conversion of a position of the model of `C₁`** with the stage-0 constants. -/
theorem convL_val {P : Polygon} {c : Config} {H : Host} {J : Merge.Junction}
    (hst : SweepEv.St0S P c H J) (hP : J.P.Simple) {Q : Polygon} {e h : ℕ}
    (hv : PosClass J.left Q ztcq) :
    convVal ztyii ztyil ztyip ztyiq
        ztyit ztwru e < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param Q ⟨convVal ztyii ztyil
        ztyip ztyiq ztyit ztwru e, h⟩ =
        (chainModel J.left).param Q ztcq ∧
      (chainModel J.whole).pos Q ⟨convVal ztyii ztyil
        ztyip ztyiq ztyit ztwru e, h⟩ =
        (chainModel J.left).pos Q ztcq := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, h33, -, h35, -⟩ := hst
  have e0 : ztxbs := by
    rw [show sw 45 = sw _ from rfl, h45 0 by_norm_num]; rfl
  have e1 : ztxps := by
    rw [show sw 45 + 1 = sw ztngs from rfl, h45 1 by_norm_num]; rfl
  have e2 : c.nreg ztdaj = Sweep.lL1 J := by
    rw [show sw 45 + 2 = sw (45 + 2) from rfl, h45 2 by_norm_num]; rfl
  have e4 : c.nreg ztdak = Sweep.lδ J := by
    rw [show sw 45 + 4 = sw (45 + 4) from rfl, h45 4 by_norm_num]; rfl
  have en : c.nreg ztna = (chainModel J.left).W.n := by rw [h33, cm_n]
  zubtf

  exact conv_pos (sideConvL J hP) Q hv

/-- **The conversion of a position of the model of `C₂`** with the stage-0 constants. -/
theorem convR_val {P : Polygon} {c : Config} {H : Host} {J : Merge.Junction}
    (hst : SweepEv.St0S P c H J) (hP : J.P.Simple) {Q : Polygon} {e h : ℕ}
    (hv : PosClass J.right Q ztcq) :
    convVal ztwmp ztyik ztyin ztyio
        ztyir ztwru e < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param Q ⟨convVal ztwmp ztyik
        ztyin ztyio ztyir ztwru e, h⟩ =
        (chainModel J.right).param Q ztcq ∧
      (chainModel J.whole).pos Q ⟨convVal ztwmp ztyik
        ztyin ztyio ztyir ztwru e, h⟩ =
        (chainModel J.right).pos Q ztcq := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, h35, -⟩ := hst
  have e0 : ztxbt := by
    rw [show sw 40 = sw _ from rfl, h40 0 by_norm_num]; rfl
  have e1 : ztxpr := by
    rw [show sw 40 + 1 = sw ztngi from rfl, h40 1 by_norm_num]; rfl
  have e2 : c.nreg ztdah = Sweep.rL1 J := by
    rw [show sw 40 + 2 = sw (40 + 2) from rfl, h40 2 by_norm_num]; rfl
  have e4 : c.nreg ztdai = Sweep.rδ J := by
    rw [show sw 40 + 4 = sw (40 + 4) from rfl, h40 4 by_norm_num]; rfl
  have en : c.nreg zthy = (chainModel J.right).W.n := by rw [h34, cm_n]
  zubtf

  exact conv_pos (sideConvR J hP) Q hv

/-- A candidate on the chain or the box is not before the first hit. -/
theorem hitParam_le_of_onCB (C : Chain) {z : Point} {σ τ : ℝ} (hτ : 0 < τ)
    (h : OnCB C ztdpf) : C.hitParam z σ ≤ τ := by
  refine csInf_le (C.hitSet_bddBelow z σ) ⟨hτ, fun hd => ?_⟩
  obtain ⟨hb, hno⟩ := hd
  zude
  · tauto
  · exact absurd h (ne_of_lt hb.1)
  · exact absurd h (ne_of_lt hb.2)

/-- **The winner of the accumulator is the first hit.** -/
theorem winner_eq {P : Polygon} {A : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {J : Merge.Junction}
    {z : Point} {σ : ℝ} {L : Set ℝ} {c : Config} (hacc : AccOK P A Mod R₀ z σ L c)
    (hgood : ∀ τ ∈ L, 0 < τ ∧ OnCB J.whole ztdpf) (hT : J.whole.hitParam z σ ∈ L) :
    c.nreg A = 1 ∧ c.nreg zttf ≤ 2 ∧
      ProperPos ztbasn zta P.n ztxhv ∧
      c.nreg ztbo < (chainModel ztwuj).W.n ∧
      (chainModel ztwuj).pos zta ztxhv =
        rayPt z σ ztbyn := by
  obtain ⟨hle, h0, h1⟩ := hacc
  have hA : ztuom := by
    grind
  obtain ⟨τ, hτ, hmin, ht, hpp, he, hpos, -⟩ := h1 hA
  have e : τ = J.whole.hitParam z σ :=
    le_antisymm by_simp_all (hitParam_le_of_onCB J.whole by_simp_all by_simp_all)
  simp_all

/-! ## The winner in the walk of `C` -/

/-- Copy the winner's edge. -/
def cpW : Stmt := .instr (.copyN yE ztbef)

/-- **The winner, converted to the walk of `C`** (by its tag and the bits). -/
def winQ : Stmt :=
  .seq (.ifLtN ztbcm K1
      ztxua
      (.ifLtN ztbcm K2
        ztxub
        cpW))
    (.instr (.copyN yH ztcma))

/-- The converted edge of the winner. -/
def winVal (c : Config) : ℕ :=
  if c.nreg ztbcm = 0 ∧ c.nreg bL = 1 then
    convVal ztyii ztyil ztyip ztyiq
      ztyit ztwru ztbagi
  else if c.nreg ztbcm = 1 ∧ c.nreg bR = 1 then
    convVal ztwmp ztyik ztyin ztyio
      ztyir ztwru ztbagi
  else c.nreg ztbef
set_option maxHeartbeats 4000000 in
theorem winQ_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hb : c.nreg bL ≤ 1 ∧ c.nreg bR ≤ 1)
    (hl : c.nreg ztbcm = 0 → c.nreg bL = 1 → c.nreg ztbef < c.nreg ztna ∧
      c.nreg ztbwh < c.nreg ztna ∧ c.nreg ztna ≤ W ∧
      c.nreg ztbca < c.nreg zthg ∧ c.nreg zthg ≤ W)
    (hr : c.nreg ztbcm = 1 → c.nreg bR = 1 → c.nreg ztbef < c.nreg zthy ∧
      c.nreg ztbwf < c.nreg zthy ∧ c.nreg zthy ≤ W ∧
      c.nreg ztfg < c.nreg zthg ∧ c.nreg zthg ≤ W) :
    IRS P W c₀ winQ c 30 (fun c' => c'.nreg yE = winVal c ∧ c'.nreg yH = c.nreg ztcma ∧
      (∀ r, r ≠ yE → r ≠ yH → r ≠ cX → r ≠ cT → r ≠ cDd → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  zuhx
  zucww
  zujad
  have syE : IScr yE := iscr_sw by_decide by_decide
  have syH : IScr yH := iscr_sw by_decide by_decide
  have hyX : yE ≠ cX ∧ yE ≠ cT ∧ yE ≠ cDd := by_decide
  have hpe : accA + 1 ≠ cX ∧ accA + 1 ≠ cT ∧ accA + 1 ≠ cDd := by_decide
  -- the copy branch
  have cp : IRS P W c₀ cpW c 1 (fun c₁ => c₁.nreg yE = c.nreg ztbef ∧
      ztegt ∧ c₁.nmem = c.nmem) := by
    refine (IRS.instr1 (i := .copyN yE _) hI syE).mono le_rfl ?_
    zuu
    refine ⟨?_, fun r h1 _ _ _ => ?_, rfl⟩
    · rfl
    · show upd c.nreg yE _ r = _; simp_all
  have st1 : IRS P W c₀ (.ifLtN ztbcm K1
      ztxua
      (.ifLtN ztbcm K2
        ztxub
        cpW)) c 28 (fun c₁ => c₁.nreg yE = winVal c ∧
      ztegt ∧ c₁.nmem = c.nmem) := by
    by_cases t0 : c.nreg ztbcm < c.nreg K1
    · have t0' : c.nreg ztbcm = 0 := by_omega
      refine IRS.mono (IRS.ifT t0 ?_) le_rfl ztb
      by_cases b0 : c.nreg bL < c.nreg K1
      · zuhis
        zuxt

      · have b1 : c.nreg bL = 1 := by_omega
        obtain ⟨a1, a2, a3, a4, a5⟩ := hl t0' b1
        refine (IRS.ifF b0 (convS_irs ztbt ztp hpe by_simp_all hI hK a1 a2 a3
          a4 a5)).mono by_norm_num ?_
        zuhjr
        refine ⟨?_, fun r r1 r2 r3 r4 => h2 r (by
          unfold CvSet; omega), h3⟩
        zuhli
    · refine IRS.mono (IRS.ifF t0 ?_) le_rfl ztb
      by_cases t1 : c.nreg ztbcm < c.nreg K2
      · have t1' : c.nreg ztbcm = 1 := by_omega
        refine IRS.mono (IRS.ifT t1 ?_) le_rfl ztb
        by_cases b0 : c.nreg bR < c.nreg K1
        · zuhis
          zuxt

        · have b1 : ztpmh := by_omega
          obtain ⟨a1, a2, a3, a4, a5⟩ := hr t1' b1
          refine (IRS.ifF b0 (convS_irs ztp ztbt hpe by_simp_all hI hK a1 a2 a3
            a4 a5)).mono by_norm_num ?_
          zuhjr
          refine ⟨?_, fun r r1 r2 r3 r4 => h2 r (by
            unfold CvSet; omega), h3⟩
          zuhli
      · refine (IRS.ifF t1 cp).mono by_norm_num ?_
        zuxt

  refine (IRS.seq (K₂ := 1) st1 ?_).mono by_norm_num ztb
  rintro c₁ hI₁ - - ⟨h1, h2, h3⟩
  refine (IRS.instr1 (i := .copyN yH _) hI₁ syH).mono le_rfl ?_
  zuu
  refine ⟨?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, h3⟩
  · tauto
  · show upd c₁.nreg yH ztvmu yH = _
    rw [upd_same, h2 _ by_decide by_decide
      by_decide by_decide]
  · show upd c₁.nreg yH _ r = _
    rw [upd_other _ _ _ r2, h2 r r1 r3 r4 r5]

/-! ## The chain contexts of the answer phase -/
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A pipeline scratch register. -/
def tAq : ℕ := sw 3228

/-- **Read the query** `j` (at `pA`) and its index. -/
def loadQ : Stmt :=
  block [.copyN qJ pJ, .loadN qE pA, .addN tAq pA K1, .loadN qH tAq, .addN tAq pA K2, .loadN qD tAq]
theorem loadQ_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hW : c.nreg pA + 2 ≤ W) :
    IRS P W c₀ loadQ c 6 (fun c' => c'.nreg qJ = c.nreg pJ ∧ c'.nreg qE = c.nmem (c.nreg pA) ∧
      c'.nreg qH = c.nmem (c.nreg pA + 1) ∧ c'.nreg qD = c.nmem (c.nreg pA + 2) ∧
      (∀ r, r ≠ qJ → r ≠ qE → r ≠ qH → r ≠ qD → r ≠ tAq → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  zuhx
  zucww
  zujad
  zubwu
  have ok : okB W c.nmem [.copyN qJ pJ, .loadN qE pA, .addN tAq pA K1, .loadN qH tAq,
      .addN tAq pA K2, .loadN qD tAq] c.nreg := by
    simp only [qJ, pJ, qE, pA, tAq, K1, K2, qH, qD, sw, Nat.reduceAdd] at k1 k2 hW ⊢
    simp only [okB, okI, regI, upd, Nat.reduceEqDiff, ite_false, k1, k2]
    grind
  refine (IRS.block _ hI ok).mono le_rfl ?_
  zuu
  simp only [qJ, pJ, qE, pA, tAq, K1, K2, qH, qD, sw, Nat.reduceAdd] at k1 k2 ⊢
  simp only [regB, regI, upd, Nat.reduceEqDiff, ite_false, ite_true, k1, k2]
  simp_all

/-! ## The bits -/

/-- The position `(6, 0)` of a chain model is the top. -/
theorem top_pos (C : Chain) (Q : Polygon) : (chainModel C).pos Q ztbcw = C.top := by
  show Geometry.lerp ((chainModel C).wa 6) ((chainModel C).wb 6) 0 = C.top
  rw [Geometry.lerp_zero]; exact C.sideWalk_vtx_six _

/-- Registers of the bit test. -/
def sZ : ℕ := sw 3240
def sTq : ℕ := sw 3244
def kO : ℕ := sw 3249

/-- **The bit `bt`**: `1` iff the height of the query code is not above the top of the chain of
the descriptor `dsc`. -/
def bitT (dsc bt : ℕ) : Stmt :=
  .seq (block [.copyN sZ K0, .subN ztohn qH K1])
    (.seq (callSym dsc K6 K0 sTq) (.seq (callKb (sTq + 1) sZ 1 kO) (block [.subN bt K1 kO])))
set_option maxHeartbeats 4000000 in
theorem bitT_irs {dsc bt : ℕ} {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hctx : ChainCtx P W c dsc C) (hdsc : IFix dsc) (hbt : bt = bL ∨ bt = bR)
    (hqH : 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n) (hroom : c.nreg ALLOC + 16962 ≤ W) :
    IRS P W c₀ (bitT dsc bt) c 16962 (fun c' => c'.nreg bt ≤ 1 ∧
      (c'.nreg bt = 1 ↔ ((Qof P).vtx ztbmn).2 ≤ C.top.2) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ bt → ¬ ztdpp → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhx
  have k0 := hKc.1
  zucww
  zumbs
  have hWh := hctx.2.1
  zuku
  zubwu
  have hbt' : 243225 ≤ bt ∧ bt ≤ 243226 := by rcases hbt with rfl | rfl <;> zuoca
  have hdl : 240000 ≤ dsc ∧ dsc < 240700 := hdsc
  -- 1. the vertex point of the height code
  have ok1 : okB W c.nmem [.copyN sZ K0, .subN ztohn qH K1] c.nreg :=
    ⟨s _ by_decide by_decide,
      s _ by_decide by_decide, trivial⟩
  refine (IRS.seq (K₂ := 16960) ztrjo ?_).mono by_simp ztb
  zugn
  have v1 : c₁.nreg sZ = 0 ∧ c₁.nreg ztohn = c.nreg qH - 1 ∧
      (∀ r, r ≠ sZ → r ≠ sZ + 1 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    subst hc1
    simp only [sZ, K0, K1, qH, sw, Nat.reduceAdd] at k0 k1 ⊢
    simp only [regB, regI, upd, Nat.reduceEqDiff, ite_false, ite_true, k0, k1]
    simp_all
  obtain ⟨z1, z2, r1, m1⟩ := v1
  have hsz : SymPtIn c₁ sZ zteke := ⟨z1, z2⟩
  have hA1 : ztdc := r1 _ by_decide
    by_decide
  have hctx₁ := hctx.transport (r1 _ ztozx
    ztozx) by_simp_all (by zvnhf)
  have rK6 : ztpmz := by zunli; exact hKc.2.2.1
  have rK0 : zteib := by zunli; exact k0
  zubb
  zukk
  -- 2. the top
  have hpp : ProperPos ztc zta P.n ⟨c₁.nreg K6, c₁.nreg K0⟩ := by
    rw [rK6, rK0]; exact ⟨le_refl _, by_simp, Nat.zero_le _⟩
  refine IRS.seq (K₂ := 251 + 2) (callSym_irs hI₁ hctx₁ ⟨by_omega, by_omega,
      by decide, by_decide, by_decide,
      by decide⟩ ⟨by_decide, by_decide⟩
      by_omega hpp
      (by rw [rK6, rK0, top_pos]; exact absy_lt C C.top_mem_set)
      by_omega by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨sp, hsp, hlt, hev, f2, hA2, m2⟩
  rw [rK6, rK0, top_pos] at hev
  have hsz₂ : SymPtIn c₂ sZ _ := symPtIn_copy hsz
    (f2 _ ztmr
      ztbuo by_decide)
    (f2 _ ztmr
      ztbuo by_decide)
    (f2 _ ztmr
      ztbuo by_decide)
  -- 3. the sign test
  refine IRS.seq (callKb_irs by_norm_num hI₂ hG hWn
      ⟨by_decide, by_decide⟩
      ⟨by_decide, by_decide⟩
      ⟨by_decide, by_decide⟩ hsp hsz₂ hlt
      (show c.nreg qH - 1 < P.n by omega) by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨o1, o2, f3, hA3, m3⟩
  have k1₃ := (hK.fix hI₃).2.1
  refine (IRS.block [.subN bt K1 kO] hI₃ ztpft).mono by_norm_num ?_
  zuu
  have vb : regB c₃.nmem [.subN bt K1 kO] c₃.nreg bt = 1 - c₃.nreg kO := by
    simp only [regB, regI, upd_same, k1₃]
  have kb : ∀ r, r ≠ bt → regB c₃.nmem [.subN bt K1 kO] c₃.nreg r = c₃.nreg r := by
    intro r hr; zumxi; exact upd_other _ _ _ hr
  refine ⟨by_grind, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩
  · simp only; rw [vb]
    have : SignTest 1 ztbair ((SymPt.vtx ztbmn).eval zta)
        ztbair ↔ C.top.2 < ((Qof P).vtx ztbmn).2 := by
      rw [hev]; rfl
    grind
  · simp only; rw [kb r h2]
    have hsw : ∀ x, sw 3230 ≤ x → x < sw 3300 → True := by_grind
    rw [f3 r h1 ztxwq h4,
      f2 r h1 (by
        zucuy
        simp only [sTq, sw] at hh
        exact h3 ztcbm) h4,
      r1 r ztxwq ztxwq]
  · zubi
    rw [kb ALLOC (by rcases hbt with rfl | rfl <;> simp [bL, bR, ALLOC, sw])]; omega
  grind

/-- **The two bits**: the bit of the query chain is `1`, the other one is tested. -/
def bitsQ : Stmt :=
  .ifLtN sSide K1 (.seq (block [.copyN bL K1]) (bitT zted bR))
    (.seq (block [.copyN bR K1]) (bitT ztiw bL))
set_option maxHeartbeats 4000000 in
theorem bitsQ_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c₀) {i : ℕ}
    (hi : i ≤ 1) (hs : c.nreg sSide = i)
    (hL : ChainCtx P W c ztiw J.left) (hR : ChainCtx P W c zted J.right)
    (hqH : 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n)
    (h0 : i = 0 → ((Qof P).vtx ztbmn).2 ≤ J.left.top.2)
    (h1 : i = 1 → ((Qof P).vtx ztbmn).2 ≤ J.right.top.2)
    (hroom : c.nreg ALLOC + 16966 ≤ W) :
    IRS P W c₀ bitsQ c 16966 (fun c' => (c'.nreg bL ≤ 1 ∧
      (c'.nreg bL = 1 ↔ ((Qof P).vtx ztbmn).2 ≤ J.left.top.2)) ∧
      (c'.nreg bR ≤ 1 ∧ (c'.nreg bR = 1 ↔ ((Qof P).vtx ztbmn).2 ≤ J.right.top.2)) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ bL → r ≠ bR → ¬ ztdpp →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhx
  zucww
  zubwu
  -- one branch: set `b₁ := 1`, test `b₂`
  have br : ∀ (b₁ b₂ d : ℕ) (C₁ C₂ : Chain), (b₁ = bL ∧ b₂ = bR ∨ b₁ = bR ∧ b₂ = bL) →
      IFix d → ChainCtx P W c d C₂ →
      IRS P W c₀ (.seq (block [.copyN b₁ K1]) (bitT d b₂)) c 16963 (fun c' =>
        c'.nreg b₁ = 1 ∧ c'.nreg b₂ ≤ 1 ∧
        (c'.nreg b₂ = 1 ↔ ((Qof P).vtx ztbmn).2 ≤ C₂.top.2) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ b₁ → r ≠ b₂ → ¬ ztdpp →
          r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
    intro b₁ b₂ d C₁ C₂ hb hd hctx
    have hb1 : 243225 ≤ b₁ ∧ b₁ ≤ 243226 ∧ 243225 ≤ b₂ ∧ b₂ ≤ 243226 ∧ b₁ ≠ b₂ := by
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> zuoca
    refine IRS.seq (K₂ := 16962) (IRS.block [.copyN b₁ K1] hI ztpft) ?_
    zuer
    have v1 : ∀ r, r ≠ b₁ → regB c.nmem [.copyN b₁ K1] c.nreg r = c.nreg r := by
      zubxc
    have e1 : regB c.nmem [.copyN b₁ K1] c.nreg b₁ = 1 := by
      simp only [regB, regI, upd_same, k1]
    have hctx₁ : ChainCtx P W { c with nreg := regB c.nmem [.copyN b₁ K1] c.nreg } d C₂ :=
      hctx.transport (v1 d (by unfold IFix at hd; omega)) by_simp_all
        (by simp only; rw [v1 ALLOC ztu])
    have hA1 : regB c.nmem [.copyN b₁ K1] c.nreg ALLOC = c.nreg ALLOC := v1 _ ztu
    have hq1 : regB c.nmem [.copyN b₁ K1] c.nreg qH = c.nreg qH := v1 _ (by unfold qH sw; omega)
    refine (bitT_irs hI₁ hK hctx₁ hd by_omega
      by_simp_all
      by_grind).mono le_rfl ?_
    rintro c' ⟨q1, q2, q3, q4, q5⟩
    simp only [hq1, hA1] at q1 q2 q3 q4 q5
    refine ⟨?_, q1, q2, fun r r0 r1 r2 r3 r4 => ?_, q4, q5⟩
    · rw [q3 b₁ ztbet hb1.2.2.2.2
        (fun h => by unfold sw at h; omega) ztu, e1]
    grind
  zueve
  · zukgb
    refine (IRS.ifT ht (br bL bR _ J.left J.right by_omega
      by_trivial hR)).mono by_norm_num ?_
    grind
  · zukga
    refine (IRS.ifF ht (br bR bL _ J.right J.left by_omega
      by_trivial hL)).mono by_norm_num ?_
    grind

/-! ## The result store -/

/-- **Store four words** at `pR`. -/
def store4 (v0 v1 v2 v3 : ℕ) : Stmt :=
  .seq (.instr (.storeN pR v0)) (.seq (.instr (.addN tAq pR K1)) (.seq (.instr (.storeN tAq v1))
    (.seq (.instr (.addN tAq pR K2)) (.seq (.instr (.storeN tAq v2))
    (.seq (.instr (.addN tAq pR K3)) (.instr (.storeN tAq v3)))))))

/-- The memory after four stores. -/
def mem4' (m : ℕ → ℕ) (A v0 v1 v2 v3 : ℕ) : ℕ → ℕ :=
  upd ztyfu zttf v3
set_option maxHeartbeats 4000000 in
theorem store4_irs {v0 v1 v2 v3 : ℕ} (hI : IInv W c₀ c) (hK : Consts c₀)
    (h1 : v1 ≠ tAq) (h2 : v2 ≠ tAq) (h3 : v3 ≠ tAq)
    (hA : c₀.nreg ALLOC ≤ c.nreg pR) (hW : c.nreg pR + 3 ≤ W) :
    IRS P W c₀ (store4 v0 v1 v2 v3) c 7 (fun c' =>
      c'.nmem = mem4' c.nmem ztqix (c.nreg v0) (c.nreg v1) (c.nreg v2) (c.nreg v3) ∧
      (∀ r, r ≠ tAq → c'.nreg r = c.nreg r)) := by
  zuhx
  zucww
  zujad
  have k3 := hKc.2.2.2.2.2.2
  have stA : IScr tAq := iscr_sw by_decide by_decide
  have pRA : pR ≠ tAq := by_decide
  have K1A : K1 ≠ tAq := by_decide
  have K2A : K2 ≠ tAq := by_decide
  have K3A : K3 ≠ tAq := by_decide
  unfold store4
  refine (IRS.seq (K₂ := 6) ztnlr ?_).mono by_norm_num ztb
  zuer
  refine IRS.seq (K₂ := 5) (IRS.instr1 hI₁ ⟨stA, by
    grind⟩) ?_
  zubuo
  simp only [regI] at hI₂ ⊢
  refine IRS.seq (K₂ := 4) (IRS.store hI₂ (by dsimp only; rw [upd_same, k1]; omega)) ?_
  zudsv
  refine IRS.seq (K₂ := 3) (IRS.instr1 hI₃ ⟨stA, by
    dsimp only; rw [upd_other _ _ _ pRA, upd_other _ _ _ K2A, k2]; omega⟩) ?_
  zukoc
  simp only [regI] at hI₄ ⊢
  refine IRS.seq (K₂ := 2) (IRS.store hI₄ (by
    dsimp only; rw [upd_same, upd_other _ _ _ pRA, upd_other _ _ _ K2A, k2]; omega)) ?_
  zugbc
  refine IRS.seq (K₂ := 1) (IRS.instr1 hI₅ ⟨stA, by
    simp_all⟩) ?_
  rintro c₆ hI₆ - - rfl
  simp only [regI] at hI₆ ⊢
  refine (IRS.store hI₆ (by
    dsimp only; rw [upd_same, upd_other _ _ _ pRA, upd_other _ _ _ pRA, upd_other _ _ _ K3A,
      upd_other _ _ _ K3A, k3]; omega)).mono le_rfl ?_
  zuu
  zubvt
  refine ztolx
  · simp only [upd_same, upd_other _ _ _ pRA, upd_other _ _ _ K2A,
      upd_other _ _ _ K3A, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3, k1, k2, k3]
    rfl
  simp_all

/-! ## The per-query program -/

/-- The query position converted to the walk of `C`. -/
def convQ : Stmt := .ifLtN sSide K1 (convS ztbca ztna qE zE) (convS ztfg zthy qE zE)

/-- A pipeline register: the height code minus one. -/
def tH : ℕ := sw 3229

/-- **The per-query program** with the candidate steps `c0` (side `0`) and `c1` (side `1`). -/
def qryP (c0 c1 : Stmt) : Stmt :=
  .seq loadQ (.seq convQ (.seq flagS
    (.ifLtN zF K1 (store4 K0 K0 K0 K0)
      (.seq bitsQ (.seq (block [.constN accA 0]) (.seq ztprx
        (.seq winQ (.seq recS (.seq (block [.subN tH qH K1]) (store4 K1 tH rL rR))))))))))
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Chazelle.Chain (sidePt SideAttach)
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
theorem iniLogKey (P : Polygon) (J : Merge.Junction) (N : NF) {m : ℕ → ℕ} {AL : ℕ}
    {ls : List ztck} (hrec : LogRecsAt m AL ls) {j : ℕ}
    (hj : j < ls.length) :
    (chainModel J.whole).key zta ztzim =
      (((logOf J zta N ls).getD j ztfj).1 : ℝ) +
        ((logOf J zta N ls).getD j ztfj).2.1 := by
  obtain ⟨a1, a2, -⟩ := hrec j hj
  obtain ⟨l1, l2⟩ := logOf_getD J zta N hj
  rw [l1, l2, ← a1, ← a2]
  rfl
variable {P : Polygon} {J : Merge.Junction} {N : NF} {S₂ : Set (Set Point)} {m : ℕ → ℕ} (b : ℕ)
/-- **The search in the log**: `lsPr` is downward closed, and an answer of the search is the
index of a log record whose key is the target's. -/
theorem search_exact
 {AL G : ℕ} {ls : List ztck} (hG : G = gW J)
    (hrec : LogRecsAt m AL ls) (hLog : LogOK J S₂ ztxxp) (x : WPos) :
    (∀ a b, a ≤ b → b < ls.length → lsPr P J m AL G x b → lsPr P J m AL G x a) ∧
    ∀ i, i < ls.length → m ztbdu = x.edge →
      (chainModel J.whole).param zta ztbwa = (chainModel J.whole).param zta x →
      ∀ t, (∀ j, j < t → lsPr P J m AL G x j) →
        (∀ j, t ≤ j → j < ls.length → ¬ lsPr P J m AL G x j) → t = i := by
  obtain ⟨-, -, -, hsort, -⟩ := hLog
  set es := logOf J zta N ls with hes
  have hlen : es.length = ls.length := by zupau; unfold logOf; simp
  have hpr : ∀ j, j < ls.length → (lsPr P J m AL G x j ↔
      oW J ((es.getD j ztfj).1 + (es.getD j ztfj).2.1) <
        oW J ztwqc) := by
    zun
    zumtl
    rw [iniLogKey P J N hrec hj, hG]
    rfl
  have hlt : ∀ a b, a < b → b < ls.length →
      oW J ((es.getD a ztfj).1 + (es.getD a ztfj).2.1) <
        oW J ((es.getD b ztfj).1 + (es.getD b ztfj).2.1) := by
    intro a b hab hb
    have ha' : a < es.length := by_omega
    have hb' : b < es.length := by_omega
    rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb']
    exact List.pairwise_iff_getElem.1 hsort a b ha' hb' hab
  refine ⟨fun a b hab hb h => ?_, fun i hi he hp t h1 h2 => ?_⟩
  · rcases hab.lt_or_eq with hab | rfl
    · grind
    omega
  · have hki : (chainModel J.whole).key zta ztbwa =
        (chainModel J.whole).key zta x := by
      zuhqn
      zugvh
      tauto
    have hni : ¬ lsPr P J m AL G x i := by
      zumtl
      show ¬ off _ _ ((chainModel J.whole).key zta ztbwa) < _
      grind
    have hKi : oW J ztwpp =
        oW J ztwqc := by
      rw [← iniLogKey P J N hrec hi, ← hki]; rfl
    grind

/-- **An attachment at a stored position is a log record.** -/
theorem attach_idx
 {AL : ℕ} {ls : List ztck}
    (hrec : LogRecsAt m AL ls) (hLog : LogOK J S₂ ztxxp) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {x : WPos}
    (hA : SideAttach (chainModel J.whole).W e x.edge ((chainModel J.whole).param zta x))
    (hst : (Lst J : ℝ) ≤ oW J (x.edge + (chainModel J.whole).param zta x)) :
    ∃ i, i < ls.length ∧ m ztbdu = x.edge ∧
      (chainModel J.whole).param zta ztbwa =
        (chainModel J.whole).param zta x := by
  obtain ⟨i, hi, h1, h2⟩ := cut_key J hLog he hA hst
  have hlen : (logOf J zta N ls).length = ls.length := by unfold logOf; simp
  zucpx
  obtain ⟨l1, l2⟩ := logOf_getD J zta N hi
  obtain ⟨a1, a2, -⟩ := hrec i hi
  refine ⟨i, hi, by_omega, ?_⟩
  unfold logPos
  simp_all

/-! ## Slots -/

/-- **The content of a good flagged slot**: a proper position of the model of `C₂` whose point is
a candidate origin for `w` in the direction of the slot. -/
def SlotVal (P : Polygon) (J : Merge.Junction) (u : WPos) (s : ℕ) (w : Point) : Prop :=
  u.edge < (chainModel J.right).W.n ∧ ProperPos ztj zta P.n u ∧
    CandAt J ((chainModel J.right).pos zta u) ztmiq w

/-- The memory after writing the slot `(t, s)` with `(1, e, h)`. -/
def slotW (m : ℕ → ℕ) (B t s e h : ℕ) : ℕ → ℕ :=
  upd (upd (upd m ztltn 1) (slotA B t s + 1) e) (slotA B t s + 2) h
theorem slotW_other {B t s e h a : ℕ} (ha : a < slotA B t s ∨ slotA B t s + 2 < a) :
    slotW m B t s e h a = m a := by
  unfold slotW
  zucud
theorem slotW_flag {B t s e h : ℕ} : slotW m B t s e h ztltn = 1 := by
  unfold slotW
  simp

/-- Two different slots do not overlap. -/
theorem slot_sep {B i s t s' d : ℕ} (hs : s ≤ 1) (hs' : s' ≤ 1) (hd : d < 3)
    (hne : ¬ (i = t ∧ s = s')) :
    slotA B i s + d < slotA B t s' ∨ slotA B t s' + 2 < slotA B i s + d := by
  unfold slotA
  omega

/-- **Writing a slot with a candidate origin keeps the slots good.** -/
theorem slotOK_store {B AL E t s e h : ℕ}
    (hsep : AL + 7 * E ≤ B) (ht : t < E) (hs : s ≤ 1)
    (hok : ∀ i, i < E → ∀ s', s' ≤ 1 → SlotOK P J m B AL i s')
    (hv : SlotVal P J ztcq s ztfid) :
    ∀ i, i < E → ∀ s', s' ≤ 1 → SlotOK P J ztevq B AL i s' := by
  intro i hi s' hs'
  have hL : ∀ j, j < E → logPt P J ztevq AL j = logPt P J m AL j := by
    zun
    have h0 : slotW m B t s e h ztcst = m ztcst :=
      slotW_other ztmx
    have h1 : slotW m B t s e h ztbyd = m ztbyd :=
      slotW_other ztmx
    unfold logPt logPos
    simp_all
  zugjm
  · obtain ⟨rfl, rfl⟩ := hit
    have f0 : slotW m B i s' e h ztfuq = 1 := slotW_flag
    have f1 : slotW m B i s' e h (slotA B i s' + 1) = e := by
      zumuz
    have f2 : slotW m B i s' e h (slotA B i s' + 2) = h := by
      zumuz
    zumrl
    rw [f0, f1, f2, hL i hi]
    exact ⟨le_rfl, fun _ => hv⟩
  · have g : ∀ d, d < 3 → slotW m B t s e h ztpec = m ztpec :=
      fun d hd => slotW_other (slot_sep hs' hs hd hit)
    have g0 : slotW m B t s e h ztfuq = m ztfuq := by
      simpa using g 0 by_norm_num
    zumrl
    rw [g0, g 1 by_norm_num, g 2 by_norm_num, hL i hi]
    exact hok i hi s' hs'

/-! ## Origin positions -/

/-- **The normalised end position of a chord** of `N₂`: a proper position of the model of `C₂`
whose point is the endpoint origin `2 k + s`. -/
theorem endPos_facts
    (hN : IsNF ztj zta N) {k s : ℕ} (hk : k < N.nChords) (hs : s ≤ 1) :
    (endPos N k s).edge < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n
        ⟨(endPos N k s).edge, nhgt ztj zta ztcdc⟩ ∧
      (chainModel J.right).pos zta
        ⟨(endPos N k s).edge, nhgt ztj zta ztcdc⟩ =
        endOrigin J zta N ztci ∧
      (nhgt ztj zta ztcdc = 0 ↔
        (chainModel J.right).param zta
          ⟨(endPos N k s).edge, nhgt ztj zta ztcdc⟩ = 0) := by
  zuftf
  zucwi
  zuc
  have hpl : ProperPos ztj zta P.n (N.chord k).lpos :=
    ⟨hA.1.2.1, hA.1.2.2.1, by show (N.chord k).h + 1 ≤ P.n; omega⟩
  have hpr : ProperPos ztj zta P.n (N.chord k).rpos :=
    ⟨hA.2.2.1, hA.2.2.2.1, by show (N.chord k).h + 1 ≤ P.n; omega⟩
  have hp : ProperPos ztj zta P.n ztcdc := by
    unfold endPos; grind
  have he : (endPos N k s).edge < (chainModel J.right).W.n := by
    zuhan
    · exact hA.1.1
    · exact hA.2.1
  obtain ⟨n1, -, n3, n4⟩ := nhgt_facts hp
  have hj : 2 * k + s < 2 * N.nChords := by_omega
  obtain ⟨o1, -⟩ := endOrigin_eq J hN hj
  grind

/-- The origin position of a stop record `(kind, k, b)`. -/
noncomputable def stopPos (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) : WPos :=
  if kind = 0 then ⟨cstR J 1, 0⟩
  else if kind = 1 then
    ⟨(endPos N k ztmnm).edge, nhgt ztj zta (endPos N k ztmnm)⟩
  else ztbcw
theorem ini_dS_sOf : dS ztmnm = dirOf b := by
  unfold dS sOf dirOf
  simp
theorem ini_sOf_le : sOf b ≤ 1 := by unfold sOf; grind

/-- **The origin position of a stop record.** -/
theorem stopPos_facts (hP : J.P.Simple)
    (hN : IsNF ztj zta N) {kind k b : ℕ} (_hkind : kind ≤ 2)
    (hk : kind = 1 → k < N.nChords) :
    (stopPos P J N kind k b).edge < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztoin ∧
      (chainModel J.right).pos zta ztoin = stopOrig J zta N kind k b := by
  zudhu
  zukgc
  unfold stopPos stopOrig
  zufqu
  · simp only [ite_eq_left h0]
    have hlt : ztmuz := by
      zvmxq; show 6 + tpos J.right 0 < _; omega
    have hp0 := Cand1.param_hgt0 ztj zta zttim
    refine ztxzp
    exact (Cand1.shared_iffR hP zta hlt ztjqe by_simp).2
      ⟨hp0, Or.inl rfl⟩
  · simp only [ite_eq_right h0]
    zubsx
    · simp only [ite_eq_left h1]
      obtain ⟨a1, a2, a3, -⟩ := endPos_facts hN (hk h1) (ini_sOf_le b)
      refine ⟨a1, a2, ?_⟩
      rw [a3]
      zucr
      unfold sOf; by_cases hb : b = 1 <;> norm_num [hb, dirOf]
    · simp only [ite_eq_right h1]
      have hlt : (6 : ℕ) < (chainModel J.right).W.n := by_omega
      have hp0 := Cand1.param_hgt0 ztj zta 6
      refine ztxzp
      exact (Cand1.top_iffR hP zta hlt ztjqe by_simp).2
        ⟨hp0, Or.inl rfl⟩
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Chazelle.Chain (sidePt SideAttach)
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
structure OD (P : Polygon) (J : Merge.Junction) (N : NF) (m : ℕ → ℕ) (AS S AL E AT : ℕ)
    (rs : List ztcf) (ls : List ztck) : Prop where
  rl : rs.length = S
  rr : StopRecsAt m AS rs
  rok : StopsOK J ztwrl (stopsOf J zta N rs)
  rw : ∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      (r.2.2.1 = 1 → r.2.2.2.1 < N.nChords)
  ll : ls.length = E
  lr : LogRecsAt m AL ls
  lok : LogOK J ztwrl ztxxp
  lw : ∀ r ∈ ls, PosW P J r.1 r.2.1
  tok : TabOK J zta N (tabOf J zta m AT)
  tw : ∀ j, j < 2 * N.nChords → m ztcsu ≤ 1 ∧
      (m ztcsu = 1 → PosW P J ztbaib (m ztclb))

/-- `OD` from `SweepEv.Out`. -/
theorem OD.of_out {P : Polygon} {J : Merge.Junction} {N : NF} {c : Config}
    (h : SweepEv.Out P J N c) : ∃ rs ls, OD P J N c.nmem (rd c bSweep 200) (rd c bSweep 201)
      ztiad (rd c bSweep 301) ztlsn rs ls := by
  obtain ⟨rs, ls, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨rs, ls, h1, h2, h3, h4, h5, h6, h7, by_grind, h9, h10⟩
theorem stopRecs_congr {m m' : ℕ → ℕ} {A : ℕ} {rs : List ztcf}
    (h : StopRecsAt m A rs) (hm : ∀ a, a < A + 5 * rs.length → m' a = m a) :
    StopRecsAt m' A rs := by
  zug
  zudqs
  grind
theorem logRecs_congr {m m' : ℕ → ℕ} {A : ℕ} {ls : List ztck}
    (h : LogRecsAt m A ls) (hm : ∀ a, a < A + 7 * ls.length → m' a = m a) :
    LogRecsAt m' A ls := by
  zug
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h i hi
  grind

/-- **`OD` is local.** -/
theorem OD.congr {P : Polygon} {J : Merge.Junction} {N : NF} {m m' : ℕ → ℕ}
    {AS S AL E AT : ℕ} {rs : List ztcf} {ls : List ztck}
    (h : OD P J N m AS S AL E AT rs ls) {A₀ : ℕ} (hm : ∀ a, a < A₀ → m' a = m a)
    (hS : AS + 5 * S ≤ A₀) (hE : AL + 7 * E ≤ A₀) (hT : AT + 3 * (2 * N.nChords) ≤ A₀) :
    OD P J N m' AS S AL E AT rs ls := by
  have ht : ∀ j, j < 2 * N.nChords → tabOf J zta m' AT j = tabOf J zta m AT j := by
    zun
    unfold tabOf
    grind
  refine ⟨h.rl, stopRecs_congr h.rr (fun a ha => hm a (by rw [h.rl] at ha; omega)), h.rok, h.rw,
    h.ll, logRecs_congr h.lr (fun a ha => hm a (by rw [h.ll] at ha; omega)), h.lok, h.lw,
    fun j hj => ?_, fun j hj => ?_⟩
  · rw [ht j hj]; exact h.tok j hj
  · zueme
    exact h.tw j hj
section steps
variable {P : Polygon} {J : Merge.Junction} {N : NF} {m : ℕ → ℕ} {AS S AL E AT : ℕ}
  {rs : List ztcf} {ls : List ztck}
theorem OD.logW (h : OD P J N m AS S AL E AT rs ls) {j : ℕ} (hj : j < E) :
    PosW P J (m ztcst) (m ztbyd) := by
  have hj' : j < ls.length := by rw [h.ll]; exact hj
  obtain ⟨a1, a2, -⟩ := h.lr j hj'
  rw [a1, a2, List.getD_eq_getElem _ _ hj']
  exact h.lw _ ztdbx
theorem OD.stopR (h : OD P J N m AS S AL E AT rs ls) {x : ℕ} (hx : x < S) :
    PosW P J (m ztbbm) (m ztbdv) ∧ m ztdfe ≤ 2 ∧
      m ztnt ≤ 1 ∧ (m ztdfe = 1 → m ztelq < N.nChords) := by
  zudzs
  zudqt
  rw [a1, a2, a3, a4, a5, List.getD_eq_getElem _ _ hx']
  exact h.rw _ ztdbx
theorem OD.down (h : OD P J N m AS S AL E AT rs ls) {G : ℕ} (hG : G = gW J) (x : WPos) :
    ∀ a b, a ≤ b → b < E → lsPr P J m AL G x b → lsPr P J m AL G x a := by
  rw [← h.ll]; exact (search_exact hG h.lr h.lok x).1

/-- **A stop record**: the answer `t` of the search for its key is a log record with that key,
and its origin position is a good slot content for it. -/
theorem stop_step (h : OD P J N m AS S AL E AT rs ls) (hP : J.P.Simple)
    (hN : IsNF ztj zta N) {G : ℕ} (hG : G = gW J) {x : ℕ} (hx : x < S)
    {t : ℕ} (h1 : ∀ j, j < t → lsPr P J m AL G ztxhy j)
    (h2 : ∀ j, t ≤ j → j < E → ¬ lsPr P J m AL G ztxhy j) :
    t < E ∧ m ztdkq = m ztbbm ∧
      (chainModel J.whole).param zta ztrtq =
        (chainModel J.whole).param zta ztxhy ∧
      SlotVal P J (stopPos P J N (m ztdfe) (m ztelq) (m ztnt))
        ztxai ztfid := by
  zudzs
  set r := rs[x] with hr
  have hmem : r ∈ rs := List.getElem_mem _
  zudqt
  rw [List.getD_eq_getElem _ _ hx'] at a1 a2 a3 a4 a5
  obtain ⟨-, hkind, -, hk⟩ := h.rw r hmem
  obtain ⟨hc, hF, hA, hL⟩ := stop_cand J hN h.rok hmem hkind hk
  obtain ⟨i, hi, e1, e2⟩ := attach_idx (x := ztbhg) h.lr h.lok hF hA hL
  rw [← a1, ← a2] at e1 e2
  zubny

  rw [a3, a4, a5]
  obtain ⟨s1, s2, s3⟩ := stopPos_facts (b := r.2.2.2.2) hP hN hkind hk
  refine ⟨s1, s2, ?_⟩
  rw [s3, ini_dS_sOf]
  have hpt : logPt P J m AL t = sidePt (chainModel J.whole).W r.1
      ((chainModel J.whole).param zta ztbhg) := by
    unfold logPt
    rw [e2, ← a1, ← a2]
    show sidePt _ (m _) _ = _
    zukd
  simp_all

/-- **The regular endpoint queries** by an index test on the normalised end position. -/
theorem valid_test (hP : J.P.Simple) (hN : IsNF ztj zta N) {k s : ℕ}
    (hk : k < N.nChords) (hs : s ≤ 1) :
    ValidO J zta N ztci ↔
      (6 ≤ (endPos N k s).edge ∧ (endPos N k s).edge ≤ 2 * J.right.m + 5 ∧
        (nhgt ztj zta ztcdc ≠ 0 ∨
          ((endPos N k s).edge ≠ 6 ∧ (endPos N k s).edge ≠ cstR J 1 ∧
            (endPos N k s).edge ≠ 6 + midT J.right))) := by
  obtain ⟨f1, f2, f3, f4⟩ := endPos_facts hN hk hs
  have hv := valid_iff J hP _
    (x := ⟨(endPos N k s).edge, nhgt _ _ _⟩) f1 f2.1 f2.2.1 f4
  unfold ValidO
  rw [← f3]
  exact hv

/-- **A regular table entry with flag `1`**: the answer `t` of the search for its position is a
log record with that key, and the normalised end position is a good slot content for it. -/
theorem tab_step (h : OD P J N m AS S AL E AT rs ls) (hN : IsNF ztj zta N)
    {G : ℕ} (hG : G = gW J) {k s : ℕ} (hk : k < N.nChords) (hs : s ≤ 1)
    (hv : ValidO J zta N ztci) (hf : m ztxut = 1) {t : ℕ}
    (h1 : ∀ j, j < t → lsPr P J m AL G
      ⟨m ztwtm, m ztwzg⟩ j)
    (h2 : ∀ j, t ≤ j → j < E → ¬ lsPr P J m AL G
      ⟨m ztwtm, m ztwzg⟩ j) :
    t < E ∧ m ztdkq = m ztwtm ∧
      (chainModel J.whole).param zta ztrtq =
        (chainModel J.whole).param zta
          ⟨m ztwtm, m ztwzg⟩ ∧
      SlotVal P J ⟨(endPos N k s).edge, nhgt ztj zta ztcdc⟩ s
        ztfid := by
  set j := 2 * k + s with hjdef
  have hj : j < 2 * N.nChords := by_omega
  obtain ⟨hon, hsh, htop⟩ := hv
  have hTj : tabOf J zta m AT j =
      some (m ztbjf, (chainModel J.whole).param zta
        ⟨m ztbjf, m ztclb⟩) := by
    unfold tabOf; simp_all
  obtain ⟨hc, hF, hA, hL⟩ := tab_cand J h.tok hj hon hsh htop hTj
  obtain ⟨i, hi, e1, e2⟩ := attach_idx (x := ztxzq)
    h.lr h.lok hF hA hL
  zubny

  obtain ⟨f1, f2, f3, -⟩ := endPos_facts hN hk hs
  refine ⟨f1, f2, ?_⟩
  rw [f3]
  have hd : dS s = endDir j := by
    unfold dS endDir
    grind
  zumne
  have hpt : logPt P J m AL t = sidePt (chainModel J.whole).W ztbaib
      ((chainModel J.whole).param zta ztxzq) := by
    unfold logPt
    zucjj
    tauto
  simp_all
end steps

/-! ## The invariant of the slot table -/

/-- **The slot table after `x` stop records and the table entries of the first `kk` chords.** -/
def SInv (P : Polygon) (J : Merge.Junction) (N : NF) (AS AL E AT B : ℕ) (m : ℕ → ℕ)
    (x kk : ℕ) : Prop :=
  (∀ i, i < E → ∀ s, s ≤ 1 → SlotOK P J m B AL i s) ∧
  (∀ y, y < x → ∃ i, i < E ∧ m ztbdu = m ztpvq ∧
    (chainModel J.whole).param zta ztbwa =
      (chainModel J.whole).param zta ⟨m ztpvq, m (AS + 5 * y + 1)⟩ ∧
    m (slotA B i (sOf (m ztgzr))) = 1) ∧
  (∀ j, j < kk → ValidO J zta N j → m ztcsu = 1 →
    ∃ i, i < E ∧ m ztbdu = m ztbjf ∧
    (chainModel J.whole).param zta ztbwa =
      (chainModel J.whole).param zta ztxzq ∧
    m (slotA B i ztfsu) = 1)

/-- The invariant at the start: a zeroed slot table. -/
theorem SInv.zero {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ} {m : ℕ → ℕ}
    (hz : ∀ a, B ≤ a → a < B + 6 * E → m a = 0) : SInv P J N AS AL E AT B m 0 0 := by
  refine ⟨fun i hi s hs => ?_, by_omega,
    by omega⟩
  have h0 : m ztege = 0 := hz _ ztjre ztjre
  zumrl
  omega

/-- **The invariant is local** below the end of the slot table. -/
theorem SInv.congr {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m m' : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hm : ∀ a, a < B + 6 * E → m' a = m a) (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * kk ≤ B) : SInv P J N AS AL E AT B m' x kk := by
  zubpa
  have hL : ∀ i, i < E → logPos m' AL i = logPos m AL i := fun i hi => by
    zuhar
  have hL0 : ∀ i, i < E → m' _ = m ztbdu := fun i hi => hm _ by_omega
  have hB : ∀ i, i < E → ∀ s, s ≤ 1 → ∀ d, d < 3 → m' _ = m ztimf :=
    fun i hi s hs d hd => hm _ ztjre
  have hB0 : ∀ i, i < E → ∀ s, s ≤ 1 → m' _ = m _ :=
    fun i hi s hs => by simpa using hB i hi s hs 0 by_norm_num
  refine ⟨fun i hi s hs => ?_, fun y hy => ?_, fun j hj hv hf => ?_⟩
  · unfold SlotOK logPt
    rw [hB0 i hi s hs, hB i hi s hs 1 by_norm_num, hB i hi s hs 2 by_norm_num, hL i hi]
    exact h1 i hi s hs
  · zudeo

    · grind
    · grind
    · rw [hm ztgzr by_omega, hB0 i hi _ ztqrq, e3]
  · zukby
    obtain ⟨i, hi, e1, e2, e3⟩ := h3 j hj hv hf'
    zumkj
    · grind
    · rw [hL i hi, hm _ by_omega, hm _ by_omega, e2]
    grind

/-- **Writing a good slot keeps the invariant** (the records lie below the slot table). -/
theorem SInv.store {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk t s e h : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B) (hT : AT + 3 * kk ≤ B) (ht : t < E)
    (hs : s ≤ 1) (hv : SlotVal P J ztcq s ztfid) :
    SInv P J N AS AL E AT B ztevq x kk ∧ slotW m B t s e h ztltn = 1 := by
  zugpb
  have hlow : ∀ a, a < B → slotW m B t s e h a = m a :=
    fun a ha => slotW_other ztmx
  have hfl : ∀ i, i < E → ∀ s', s' ≤ 1 → m ztfuq = 1 →
      slotW m B t s e h ztfuq = 1 := by
    intro i hi s' hs' hf
    zugjm
    · obtain ⟨rfl, rfl⟩ := hit; exact slotW_flag
    · rw [slotW_other (by simpa using slot_sep (d := 0) hs' hs by_norm_num hit)]; exact hf
  have hL : ∀ i, i < E → logPos ztevq AL i = logPos m AL i := fun i hi => by
    zuhar
  have hL0 : ∀ i, i < E → slotW m B t s e h _ = m ztbdu :=
    fun i hi => hlow _ by_omega
  refine ⟨⟨slotOK_store hE ht hs h1 hv, fun y hy => ?_, fun j hj hv' hf => ?_⟩, slotW_flag⟩
  · zudeo

    · grind
    · grind
    · rw [hlow ztgzr by_omega]; exact hfl i hi _ ztqrq e3
  · zukby
    obtain ⟨i, hi, e1, e2, e3⟩ := h3 j hj hv' hf'
    zumkj
    · grind
    · rw [hL i hi, hlow _ by_omega, hlow _ by_omega, e2]
    grind

/-- One more stop record. -/
theorem SInv.extS {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hx : ∃ i, i < E ∧ m ztbdu = m ztbbm ∧
      (chainModel J.whole).param zta ztbwa =
        (chainModel J.whole).param zta ztxhy ∧
      m (slotA B i ztxai) = 1) :
    SInv P J N AS AL E AT B m zthf kk := by
  zubpa
  refine ⟨h1, fun y hy => ?_, h3⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
  · simp_all
  omega

/-- One more table entry. -/
theorem SInv.extT {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk : ℕ} (h : SInv P J N AS AL E AT B m x kk)
    (hx : ValidO J zta N kk → m ztpvr = 1 →
      ∃ i, i < E ∧ m ztbdu = m ztelr ∧
      (chainModel J.whole).param zta ztbwa =
        (chainModel J.whole).param zta ⟨m ztelr, m ztnja⟩ ∧
      m (slotA B i ztjzo) = 1) :
    SInv P J N AS AL E AT B m x zthij := by
  zubpa
  refine ⟨h1, h2, fun j hj => ?_⟩
  grind
theorem logPt_congr {P : Polygon} {J : Merge.Junction} {m m' : ℕ → ℕ} {AL t B : ℕ}
    (hm : ∀ a, a < B → m' a = m a) (ht : AL + 7 * t + 1 < B) :
    logPt P J m' AL t = logPt P J m AL t := by
  unfold logPt logPos; grind

/-- **The step of a stop record**: a good slot written at the answer of the search. -/
theorem SInv.stopStep {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m m₂ : ℕ → ℕ} {x kk t eV hV : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hm : ∀ a, a < B → m₂ a = m a) (hS : AS + 5 * zthf ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * kk ≤ B) (ht : t < E) (e1 : m₂ ztdkq = m₂ ztbbm)
    (e2 : (chainModel J.whole).param zta ztrtr =
      (chainModel J.whole).param zta ⟨m₂ ztbbm, m₂ ztbdv⟩)
    (hv : SlotVal P J ztugm (sOf (m₂ ztnt)) ztpcr) :
    SInv P J N AS AL E AT B ztbaob zthf kk := by
  zvmzz at hv
  zuilk
  obtain ⟨h1, h2⟩ := hI.store by_omega hE hT ht ztqrq hv
  refine h1.extS ⟨t, ht, ?_, ?_, ?_⟩
  · rw [slotW_other ztmx,
      slotW_other ztmx, ← hm _ by_omega, ← hm _ by_omega]
    exact e1
  · have hp : logPos ztbaob AL t = logPos m₂ AL t := by
      unfold logPos
      rw [slotW_other ztmx,
        slotW_other ztmx, hm _ by_omega, hm _ by_omega]
    rw [hp, e2, slotW_other ztmx,
      slotW_other ztmx, hm _ by_omega, hm _ by_omega]
  · have h4 : slotW m B t ztxai eV hV _ = m ztnt :=
      slotW_other ztmx
    simp_all

/-- **The step of a regular table entry with flag `1`.** -/
theorem SInv.tabStep {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m m₂ : ℕ → ℕ} {x kk t eV hV : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (hm : ∀ a, a < B → m₂ a = m a) (hS : AS + 5 * x ≤ B) (hE : AL + 7 * E ≤ B)
    (hT : AT + 3 * zthij ≤ B) (ht : t < E) (e1 : m₂ ztdkq = m₂ ztelr)
    (e2 : (chainModel J.whole).param zta ztrtr =
      (chainModel J.whole).param zta ⟨m₂ ztelr, m₂ ztnja⟩)
    (hv : SlotVal P J ztugm ztjzo ztpcr) :
    SInv P J N AS AL E AT B ztyrs x zthij := by
  zuilk
  obtain ⟨h1, h2⟩ := hI.store hS hE by_omega ht by_omega hv
  refine h1.extT (fun _ _ => ⟨t, ht, ?_, ?_, h2⟩)
  · rw [slotW_other ztmx,
      slotW_other ztmx, ← hm _ by_omega,
      ← hm _ by_omega]
    exact e1
  · have hp : logPos ztyrs AL t = logPos m₂ AL t := by
      unfold logPos
      rw [slotW_other ztmx,
        slotW_other ztmx, hm _ by_omega, hm _ by_omega]
    rw [hp, e2, slotW_other ztmx,
      slotW_other ztmx, hm _ by_omega,
      hm _ by_omega]

/-- **A table entry without a slot**: not regular, or flag `0`. -/
theorem SInv.tabSkip {P : Polygon} {J : Merge.Junction} {N : NF} {AS AL E AT B : ℕ}
    {m : ℕ → ℕ} {x kk : ℕ} (hI : SInv P J N AS AL E AT B m x kk)
    (h : ¬ (ValidO J zta N kk ∧ m ztpvr = 1)) :
    SInv P J N AS AL E AT B m x zthij :=
  hI.extT by_simp_all
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
def ipB : ℕ := sw 4100
def ipM6 : ℕ := sw 4101
def ipM5 : ℕ := sw 4102
def ipX : ℕ := sw 4103
def ipA : ℕ := sw 4104
def ipK : ℕ := sw 4105
def ipKk : ℕ := sw 4106
def ipBb : ℕ := sw 4107
def ipS : ℕ := sw 4108
def ipE : ℕ := sw 4109
def ipH : ℕ := sw 4110
def ipT : ℕ := sw 4111
def ipJ : ℕ := sw 4112
def ipF : ℕ := sw 4113
def ipV : ℕ := sw 4114
def ipKc : ℕ := sw 4115
def ipTa : ℕ := sw 4120
def ipTm : ℕ := sw 4121
def ipTt : ℕ := sw 4122
def ipTb : ℕ := sw 4123
def ipT2 : ℕ := sw 4124
def ipTM : ℕ := sw 4125

/-! ## The program -/

/-- The head: slot base and end, counters, `K₂`, `2 m₂ + 5`, the fields `m`, `T`, `β` of the
descriptor of `C₂`. -/
def hdrA : List Instr :=
  [.copyN ipB ALLOC, .copyN pT ALLOC, .addN pT pT ztex, .addN pT pT ztex,
    .addN pT pT ztex, .addN pT pT ztex, .addN pT pT ztex, .addN pT pT ztex,
    .constN ipX 0, .constN ipJ 0, .loadN ipKc ztbz, .subN ipM5 zthy K2,
    .addN ipTa zted K2, .loadN ipTm ipTa, .addN ipTa zted K3, .loadN ipTt ipTa,
    .addN ipTa zted K4, .loadN ipTb ipTa]

/-- `midT` without the bit. -/
def ipMidF : Stmt := .ifLtN ipTt ipTm (.instr (.addN ipTM ipTt ipTt)) (.instr (.constN ipTM 0))

/-- `midT` with the bit. -/
def ipMidB : List Instr := [.addN ipT2 ipTm ipTm, .subN ipTM ipT2 ipTt, .subN ipTM ipTM ipTt]

/-- `midT C₂` into `ipTM`. -/
def ipMidS : Stmt := .ifLtN ipTb K1 ipMidF (.ifLtN K1 ipTb ipMidF (block ipMidB))

/-- **The head.** -/
def hdr : Stmt := .seq ztvfc (.seq ipMidS (.instr ztrhy))

/-- Read stop record `x`: its key into the target of the search, kind, chord, direction bit, and
the slot `1 - b`. -/
def stLd : List Instr :=
  [.addN ipA ipX ipX, .addN ipA ipA ipA, .addN ipA ipA ipX, .addN ipA ipA ztcwm,
    .loadN lsxE ipA, .addN ipA ipA K1, .loadN lsxH ipA, .addN ipA ipA K1, .loadN ipK ipA,
    .addN ipA ipA K1, .loadN ipKk ipA, .addN ipA ipA K1, .loadN ipBb ipA, .subN ipS K1 ipBb]

/-- The origin position of a stop record by its kind. -/
def stOrg : Stmt :=
  .ifLtN ipK K1 (block [.copyN ipE ztbex, .constN ipH 0])
    (.ifLtN ipK K2
      (.seq (block [.copyN oK ipKk, .copyN oS ipS])
        (.seq orgHead (block [.copyN ipE oE, .copyN ipH oC])))
      (block [.copyN ipE K6, .constN ipH 0]))

/-- The slot address `B + 6 t + 3 s`. -/
def slotAd : List Instr :=
  [.addN ipT lsI lsI, .addN ipT ipT lsI, .addN ipT ipT ipT, .addN ipT ipT ipB,
    .addN ipT ipT ipS, .addN ipT ipT ipS, .addN ipT ipT ipS]

/-- **Write the slot** `(lsI, ipS)` with `(1, ipE, ipH)`. -/
def slotSt : Stmt :=
  .seq ztvfm (.seq (.instr (.storeN ipT K1)) (.seq ztnba
    (.seq (.instr (.storeN ipT ipE)) (.seq ztnba
      (.instr (.storeN ipT ipH))))))

/-- One stop record. -/
def stB (ls : Stmt) : Stmt :=
  .seq ztvfn (.seq stOrg (.seq ls (.seq slotSt (.instr (.addN ipX ipX K1)))))

/-- **The stop loop.** -/
def stLoop (ls : Stmt) : Stmt := .whileLtN ipX ztsn (stB ls)

/-- Read the table flag of entry `j = 2 k + s` (`s` the value of the register `sr`). -/
def tbLd (sr : ℕ) : List Instr :=
  [.copyN ipS sr, .addN ipA ipJ ipJ, .addN ipA ipA ipS, .addN ipT ipA ipA, .addN ipA ipT ipA,
    .addN ipA ipA ztps, .loadN ipF ipA]
def setV (v : ℕ) : Stmt := .instr (.constN ipV v)

/-- `if a = b then t else e`. -/
def ipEqT (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e ztjdg

/-- **The class test** of the normalised end position `(oE, oC)`: `ipV = 1` iff regular. -/
def cls : Stmt :=
  .ifLtN oE K6 ztkew
    (.ifLtN ipM5 oE ztkew
      (.ifLtN K0 oC ztwdr
        (ipEqT oE K6 ztkew (ipEqT oE ztbex ztkew (ipEqT oE ipM6 ztkew ztwdr)))))

/-- Read the target of a table entry and copy the origin. -/
def tbTg : List Instr :=
  [.copyN ipE oE, .copyN ipH oC, .addN ipA ipA K1, .loadN lsxE ipA, .addN ipA ipA K1,
    .loadN lsxH ipA]

/-- A table entry with flag `1`. -/
def tbHit (ls : Stmt) : Stmt :=
  .seq (block [.copyN oK ipJ, .copyN oS ipS]) (.seq orgHead (.seq cls
    (.ifLtN ipV K1 .skip (.seq ztvfp (.seq ls slotSt)))))

/-- The table entry `2 k + s`. -/
def tbOne (ls : Stmt) (sr : ℕ) : Stmt := .seq ztqec (.ifLtN ipF K1 .skip (tbHit ls))

/-- One chord. -/
def tbB (ls : Stmt) : Stmt := .seq (tbOne ls K0) (.seq (tbOne ls K1) (.instr (.addN ipJ ipJ K1)))

/-- **The table loop.** -/
def tbLoop (ls : Stmt) : Stmt := .whileLtN ipJ ipKc (tbB ls)

/-- **The initialisation.** -/
def initC (ls : Stmt) : Stmt :=
  .seq (.seq hdr (.seq zeroLoop (.seq (stLoop ls) (tbLoop ls)))) (.instr (.copyN sB ipB))
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The head block.** -/
theorem hdrA_irs (hI : IInv W c₀ c) (hK : Consts c) (hd : c.nreg zted + 5 ≤ W)
    (hroom : c.nreg ALLOC + 6 * c.nreg ztex ≤ W) :
    IRS P W c₀ ztvfc c 18 (fun c' =>
      c'.nreg ipB = c.nreg ALLOC ∧ c'.nreg pT = c.nreg ALLOC + 6 * c.nreg ztex ∧
      c'.nreg ipX = 0 ∧ c'.nreg ipJ = 0 ∧ c'.nreg ipKc = c.nmem ztwrb ∧
      c'.nreg ipM5 = c.nreg zthy - 2 ∧
      c'.nreg ipTm = c.nmem ztwpc ∧ c'.nreg ipTt = c.nmem ztwya ∧
      c'.nreg ipTb = c.nmem ztzku ∧
      ztybr ∧
      c'.nmem = c.nmem) := by
  obtain ⟨-, -, -, k4, -, k2, k3⟩ := hK
  simp only [K2, K3, K4, sw, ALLOC, Nat.reduceAdd] at k2 k3 k4 hd hroom
  have hfr : ∀ r, ztcff →
      regB c.nmem hdrA c.nreg r = c.nreg r := by
    zuz
    zunn
    simp only [hdrA, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold ipB pT ipX ipJ ipKc ipM5 ipTa ipTm ipTt ipTb sw ALLOC at *
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> omega
  refine (IRS.block hdrA hI ?_).mono by_rfl ?_
  · simp [hdrA, okB, okI, regI, upd, ipB, pT, ipX, ipJ, ipKc, ipM5, ipTa, ipTm, ipTt, ipTb, K2,
      K3, K4, sw, ALLOC, IScr, k2, k3, k4]
    omega
  · zuu
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr, rfl⟩
    all_goals (simp [hdrA, regB, regI, upd, ipB, pT, ipX, ipJ, ipKc, ipM5, ipTa, ipTm, ipTt,
      ipTb, K2, K3, K4, sw, ALLOC, k2, k3, k4]; try omega)

/-! ## `midT` -/
theorem midF_irs (hI : IInv W c₀ c) {m T : ℕ} (hm : c.nreg ipTm = m) (hT : c.nreg ipTt = T)
    (h2 : T + T ≤ W) :
    IRS P W c₀ ipMidF c 3 (fun c' => c'.nreg ipTM = (if T < m then 2 * T else 0) ∧
      (∀ r, r ≠ ipTM → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  unfold ipMidF
  by_cases h : T < m
  · refine (IRS.ifT by_omega (IRS.instr1 (i := .addN ipTM ipTt ipTt) hI
      ⟨iscr_sw by_decide by_decide, by_omega⟩)).mono
      by_norm_num ?_
    zuu
    zuflx
    · simp only [regI, upd_same, hT, ite_eq_left h]; ring
    · zuua
  · refine (IRS.ifF by_omega (IRS.instr1 (i := .constN ipTM 0) hI
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩)).mono
      by_norm_num ?_
    zuu
    zuflx
    · simp only [regI, upd_same, ite_eq_right h]
    · zuua
set_option maxHeartbeats 1000000 in
theorem midS_irs (hI : IInv W c₀ c) (hK : Consts c) {m T b : ℕ} (hm : c.nreg ipTm = m)
    (hT : c.nreg ipTt = T) (hb : c.nreg ipTb = b) (hTm : T ≤ m) (h2m : 2 * m ≤ W) :
    IRS P W c₀ ipMidS c 8 (fun c' =>
      c'.nreg ipTM = ztetn ∧
      ztgsp ∧ c'.nmem = c.nmem) := by
  zubof
  unfold ipMidS
  have hF : b ≠ 1 → IRS P W c₀ ipMidF c 4 (fun c' =>
      c'.nreg ipTM = ztetn ∧
      ztgsp ∧ c'.nmem = c.nmem) := fun hb1 =>
    (midF_irs hI hm hT by_omega).mono by_norm_num by_simp_all
  zufqs
  · exact (IRS.ifT by_omega (hF by_omega)).mono by_norm_num
      by_simp_all
  · refine (IRS.ifF by_omega ?_).mono le_rfl ztb
    by_cases h1 : 1 < b
    · exact IRS.ifT by_omega by_grind
    · zukbe
      refine (IRS.ifF by_omega ((IRS.block ipMidB hI ?_).mono by_decide ztb)).mono le_rfl ?_
      · simp [ipMidB, okB, okI, ipT2, ipTM, ipTm, ipTt, sw, IScr]
        simp only [ipTm, sw, Nat.reduceAdd] at hm
        omega
      · zuu
        refine ⟨?_, fun r h1 h2 => ?_, rfl⟩
        · simp only [ipTm, ipTt, sw, Nat.reduceAdd] at hm hT
          simp [ipMidB, regB, regI, upd, ipT2, ipTM, ipTm, ipTt, sw, hm, hT, hb1]
          omega
        · simp only [ipMidB, regB, regI]
          simp_all

/-! ## Reading a stop record -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stLd_irs (hI : IInv W c₀ c) (hK : Consts c) {AS x : ℕ} (hAS : c.nreg ztcwm = AS)
    (hx : c.nreg ipX = x) (hW : AS + 5 * x + 4 ≤ W) :
    IRS P W c₀ ztvfn c 14 (fun c' =>
      c'.nreg lsxE = c.nmem ztbbm ∧ c'.nreg lsxH = c.nmem ztbdv ∧
      c'.nreg ipK = c.nmem ztdfe ∧ c'.nreg ipKk = c.nmem ztelq ∧
      c'.nreg ipS = 1 - c.nmem ztnt ∧
      (∀ r, r ≠ lsxE → r ≠ lsxH → r ≠ ipA → r ≠ ipK → r ≠ ipKk → r ≠ ipBb → r ≠ ipS →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  zubof
  simp only [K1, ipX, sw, Nat.reduceAdd] at k1 hx hAS
  have hfr : ∀ r, r ≠ lsxE → r ≠ lsxH → r ≠ ipA → r ≠ ipK → r ≠ ipKk → r ≠ ipBb → r ≠ ipS →
      regB c.nmem stLd c.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4 h5 h6 h7
    zunn
    simp only [stLd, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold lsxE lsxH ipA ipK ipKk ipBb ipS sw at *
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> zvmwd <;> omega
  refine (IRS.block stLd hI ?_).mono by_rfl ?_
  · simp [stLd, okB, okI, regI, upd, lsxE, lsxH, ipA, ipK, ipKk, ipBb, ipS, ipX, K1, sw, IScr,
      k1, hx, hAS]
    omega
  · zuu
    refine ⟨?_, ?_, ?_, ?_, ?_, hfr, rfl⟩
    all_goals (simp [stLd, regB, regI, upd, lsxE, lsxH, ipA, ipK, ipKk, ipBb, ipS, ipX, K1, sw,
      k1, hx, hAS]; first | (congr 1; omega) | (congr 2; omega))

/-! ## Writing a slot -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem slotAd_irs (hI : IInv W c₀ c) {B t s : ℕ} (hB : c.nreg ipB = B) (ht : c.nreg lsI = t)
    (hs : c.nreg ipS = s) (hW : B + 6 * t + 3 * s ≤ W) :
    IRS P W c₀ ztvfm c 7 (fun c' => c'.nreg ipT = slotA B t s ∧
      ztivk ∧ c'.nmem = c.nmem) := by
  simp only [ipB, lsI, ipS, sw, Nat.reduceAdd] at hB ht hs
  refine (IRS.block slotAd hI ?_).mono by_rfl ?_
  · simp [slotAd, okB, okI, regI, upd, ipT, lsI, ipB, ipS, sw, IScr, hB, ht, hs]
    omega
  · zuu
    zuflx
    · simp [slotAd, regB, regI, upd, ipT, lsI, ipB, ipS, sw, hB, ht, hs, slotA]
      omega
    · zunn
      simp only [slotAd, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
        exact Ne.symm hr

/-- **Writing a slot.** -/
theorem slotSt_irs (hI : IInv W c₀ c) (hK : Consts c) {B t s : ℕ} (hB : c.nreg ipB = B)
    (ht : c.nreg lsI = t) (hs : c.nreg ipS = s) (hB0 : c₀.nreg ALLOC ≤ B)
    (hW : B + 6 * t + 3 * s + 2 ≤ W) :
    IRS P W c₀ slotSt c 12 (fun c' =>
      c'.nmem = slotW c.nmem B t s (c.nreg ipE) (c.nreg ipH) ∧
      ztivk) := by
  zubof
  have nT1 : K1 ≠ ipT := by_decide
  have nTE : ipE ≠ ipT := by_decide
  have nTH : ipH ≠ ipT := by_decide
  have iT : IScr ipT := iscr_sw by_decide by_decide
  unfold slotSt
  refine IRS.seq (K₂ := 5) (slotAd_irs hI hB ht hs by_omega) ?_ |>.mono le_rfl
    ztb
  zufmb
  have e1 : ztcpf := by_simp_all
  refine IRS.seq (K₂ := 4) (IRS.store hI₁ (by rw [a1]; unfold slotA; omega)) ?_
  zubuo
  refine IRS.seq (K₂ := 3) (IRS.instr1 hI₂
    ⟨iT, by simp only; rw [a1, e1]; unfold slotA; omega⟩) ?_
  zudsv
  refine IRS.seq (K₂ := 2) (IRS.store hI₃ (by
    zuneg; rw [a1]; unfold slotA; omega)) ?_
  zukoc
  refine IRS.seq (K₂ := 1) (IRS.instr1 hI₄
    ⟨iT, by zuneg; rw [upd_other _ _ _ nT1, a1, e1]
            tauto⟩) ?_
  zugbc
  refine (IRS.store hI₅ (by
    zuneg; rw [upd_other _ _ _ nT1, a1]
    unfold slotA; omega)).mono le_rfl ?_
  zuu
  refine ztolx
  · simp only [regI, upd_same, upd_other _ _ _ nT1,
      upd_other _ _ _ nTE, upd_other _ _ _ nTH]
    rw [a1, e1, a2 _ nTE, a2 _ nTH, a3]
    rfl
  · zuwc
    simp_all

/-! ## The head -/
set_option maxHeartbeats 2000000 in
/-- **The head.** -/
theorem hdr_irs (hI : IInv W c₀ c) (hK : Consts c) (hd : c.nreg zted + 5 ≤ W)
    (hroom : c.nreg ALLOC + 6 * c.nreg ztex ≤ W)
    (hTm : c.nmem ztwya ≤ c.nmem ztwpc)
    (h2m : 2 * c.nmem ztwpc + 6 ≤ W) :
    IRS P W c₀ hdr c 27 (fun c' =>
      c'.nreg ipB = c.nreg ALLOC ∧ c'.nreg pT = c.nreg ALLOC + 6 * c.nreg ztex ∧
      c'.nreg ipX = 0 ∧ c'.nreg ipJ = 0 ∧ c'.nreg ipKc = c.nmem ztwrb ∧
      c'.nreg ipM5 = c.nreg zthy - 2 ∧
      c'.nreg ipM6 = (if c.nmem ztzku = 1 then
          2 * c.nmem ztwpc - 2 * c.nmem ztwya
        else if c.nmem ztwya < c.nmem ztwpc then
          2 * c.nmem ztwya else 0) + 6 ∧
      ztybr ∧
      c'.nmem = c.nmem) := by
  unfold hdr
  refine IRS.seq (K₂ := 9) (hdrA_irs hI hK hd hroom) ?_
  rintro c₁ hI₁ - - ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  have hK₁ : ztukh := by
    zuch
    have f : ∀ q, 610 ≤ q → q ≤ 616 → c₁.nreg _ = c.nreg (sw q) := fun q h1 h2 =>
      a10 _ ztbaes
    exact ⟨(f 610 le_rfl by_norm_num).trans k0, (f 611 by_norm_num by_norm_num).trans k1,
      (f 612 by_norm_num by_norm_num).trans k6, (f 613 by_norm_num by_norm_num).trans k4,
      (f 614 by_norm_num by_norm_num).trans k5, (f 615 by_norm_num by_norm_num).trans k2,
      (f 616 by_norm_num le_rfl).trans k3⟩
  refine IRS.seq (K₂ := 1) (midS_irs hI₁ hK₁ a7 a8 a9 hTm by_omega) ?_
  rintro c₂ hI₂ - - ⟨b1, b2, b3⟩
  have k6 : zturp := by
    rw [b2 K6 by_decide by_decide,
      a10 K6 ztbuo]
    exact hK.2.2.1
  have hv : c₂.nreg ipTM ≤ 2 * c.nmem ztwpc := by
    grind
  refine (IRS.instr1 (i := .addN ipM6 ipTM K6) hI₂ ⟨iscr_sw by_decide
    by_decide, by_omega⟩).mono le_rfl ?_
  zuu
  have o : ∀ r, r ≠ ipM6 → r ≠ ipTM → r ≠ ipT2 → (regI c₂.nmem ztrhy c₂.nreg) r =
      c₁.nreg r := fun r h1 h2 h3 => by
    simp only [regI]; rw [upd_other _ _ _ h1, b2 r h2 h3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by_grind⟩
  · exact (o _ by_decide by_decide
      by_decide).trans a1
  · exact (o _ by_decide by_decide
      by_decide).trans a2
  · exact (o _ by_decide by_decide
      by_decide).trans a3
  · exact (o _ by_decide by_decide
      by_decide).trans a4
  · exact (o _ by_decide by_decide
      by_decide).trans a5
  · exact (o _ by_decide by_decide
      by_decide).trans a6
  · zubiv
    omega
  · exact (o r (by unfold ipM6 sw at *; omega) (by unfold ipTM sw at *; omega)
      (by unfold ipT2 sw at *; omega)).trans by_grind

/-! ## Reading a table entry -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem tbLd_irs (hI : IInv W c₀ c) {sr AT k s : ℕ} (hsr : sr < sw 4100 ∨ sw 4129 < sr)
    (hAT : c.nreg ztps = AT) (hk : c.nreg ipJ = k) (hs : c.nreg sr = s)
    (hW : AT + 3 * ztci ≤ W) :
    IRS P W c₀ ztqec c 7 (fun c' =>
      c'.nreg ipS = s ∧ c'.nreg ipA = AT + 3 * ztci ∧
      c'.nreg ipF = c.nmem ztxut ∧
      (∀ r, r ≠ ipS → r ≠ ipA → r ≠ ipT → r ≠ ipF → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  simp only [ipJ, sw, Nat.reduceAdd] at hAT hk
  have hfr : ∀ r, r ≠ ipS → r ≠ ipA → r ≠ ipT → r ≠ ipF →
      regB c.nmem (tbLd sr) c.nreg r = c.nreg r := by
    zufxp
    zunn
    simp only [tbLd, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4
  have hsr' : sr ≠ 244108 ∧ sr ≠ 244104 ∧ sr ≠ 244111 := by unfold sw at hsr; omega
  refine (IRS.block _ hI ?_).mono by_rfl ?_
  · simp [tbLd, okB, okI, regI, upd, ipS, ipA, ipT, ipF, ipJ, sw, IScr, hAT, hk, hs]
    omega
  · zuu
    refine ⟨?_, ?_, ?_, hfr, rfl⟩
    all_goals (try simp [tbLd, regB, regI, upd, ipS, ipA, ipT, ipF, ipJ, sw, hAT, hk, hs])
    all_goals first | omega | (congr 1; omega)
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem tbTg_irs (hI : IInv W c₀ c) (hK : Consts c) {a : ℕ} (ha : c.nreg ipA = a)
    (hW : a + 2 ≤ W) :
    IRS P W c₀ ztvfp c 6 (fun c' =>
      c'.nreg ipE = c.nreg oE ∧ c'.nreg ipH = c.nreg oC ∧ c'.nreg lsxE = c.nmem ztdf ∧
      c'.nreg lsxH = c.nmem ztvj ∧
      (∀ r, r ≠ ipE → r ≠ ipH → r ≠ ipA → r ≠ lsxE → r ≠ lsxH → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  zubof
  simp only [K1, ipA, sw, Nat.reduceAdd] at k1 ha
  have hfr : ∀ r, r ≠ ipE → r ≠ ipH → r ≠ ipA → r ≠ lsxE → r ≠ lsxH →
      regB c.nmem tbTg c.nreg r = c.nreg r := by
    zuetf
    zunn
    simp only [tbTg, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4 |
        exact Ne.symm h5
  refine (IRS.block tbTg hI ?_).mono by_rfl ?_
  · simp [tbTg, okB, okI, regI, upd, ipE, ipH, ipA, lsxE, lsxH, oE, oC, K1, sw, IScr, k1, ha]
    omega
  · zuu
    refine ⟨?_, ?_, ?_, ?_, hfr, rfl⟩
    all_goals (try simp [tbTg, regB, regI, upd, ipE, ipH, ipA, lsxE, lsxH, oE, oC, K1, sw, k1, ha])

/-! ## The class test -/
theorem setV_irs (hI : IInv W c₀ c) (hK : Consts c) {v : ℕ} (hv : v ≤ 1) :
    IRS P W c₀ (setV v) c 1 (fun c' => c'.nreg ipV = v ∧ ztedi ∧
      c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .constN ipV v) hI ⟨iscr_sw by_decide
    by_decide, by have := hI.hw.1 K1; rw [hK.2.1] at this; omega⟩).mono le_rfl ?_
  · zuu
    exact ⟨by_rfl, fun r hr => by simp only [regI]; simp_all, rfl⟩
theorem eqT_irs {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
    (ht : c.nreg a = c.nreg b → IRS P W c₀ t c K Q)
    (he : c.nreg a ≠ c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ (ipEqT a b t e) c ztfns Q := by
  unfold ipEqT
  zubai
  · zuhcm
  · refine (IRS.ifF (K := K + 2) h1 ?_).mono by_omega ztb
    zubjz
    · zulxd
    · zulxc
set_option maxHeartbeats 2000000 in
/-- **The class test.** -/
theorem cls_irs (hI : IInv W c₀ c) (hK : Consts c) :
    IRS P W c₀ cls c 19 (fun c' =>
      (c'.nreg ipV = 1 ↔ (6 ≤ c.nreg oE ∧ c.nreg oE ≤ c.nreg ipM5 ∧
        (c.nreg oC ≠ 0 ∨ (c.nreg oE ≠ 6 ∧ c.nreg oE ≠ c.nreg ztbex ∧
          c.nreg oE ≠ c.nreg ipM6)))) ∧ c'.nreg ipV ≤ 1 ∧
      ztedi ∧ c'.nmem = c.nmem) := by
  zumbv
  obtain ⟨k0, -, k6, -⟩ := hK
  have sv : ∀ v, v ≤ 1 → (v = 1 ↔ (6 ≤ c.nreg oE ∧ c.nreg oE ≤ c.nreg ipM5 ∧
        (c.nreg oC ≠ 0 ∨ (c.nreg oE ≠ 6 ∧ c.nreg oE ≠ c.nreg ztbex ∧
          c.nreg oE ≠ c.nreg ipM6)))) → ∀ K, 1 ≤ K → IRS P W c₀ _ c K (fun c' =>
      (c'.nreg ipV = 1 ↔ (6 ≤ c.nreg oE ∧ c.nreg oE ≤ c.nreg ipM5 ∧
        (c.nreg oC ≠ 0 ∨ (c.nreg oE ≠ 6 ∧ c.nreg oE ≠ c.nreg ztbex ∧
          c.nreg oE ≠ c.nreg ipM6)))) ∧ c'.nreg ipV ≤ 1 ∧
      ztedi ∧ c'.nmem = c.nmem) :=
    fun v hv hiff K hK => (setV_irs hI hK' hv).mono hK by_simp_all
  unfold cls
  by_cases a1 : c.nreg oE < c.nreg K6
  · exact (IRS.ifT a1 ztpeh).mono by_norm_num
      by_grind
  refine (IRS.ifF (K := 17) a1 ?_).mono by_norm_num ztb
  rw [k6] at a1
  by_cases a2 : c.nreg ipM5 < c.nreg oE
  · exact (IRS.ifT a2 ztpeh).mono by_norm_num by_grind
  refine IRS.ifF a2 ?_
  by_cases a3 : c.nreg K0 < c.nreg oC
  · exact (IRS.ifT a3 (sv 1 le_rfl by_omega 1 le_rfl)).mono by_norm_num
      by_grind
  refine IRS.ifF a3 ?_
  zvnib at a3
  refine eqT_irs ztep ztep
  · grind
  rw [k6] at h
  refine eqT_irs ztrpy ztrpy
  · grind
  refine eqT_irs ztrpz ztrpz
  · grind
  grind
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
def LSBody (lsearch : Stmt) (κ : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c ztjl J.whole →
    ztug →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg ztex < 2 ^ c.nreg TLR →
    c.nreg ztfx + 7 * c.nreg ztex ≤ c.nreg ALLOC →
    c.nreg ztfg < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg ztex → SweepEv.PosW P J ztwun
      ztwrr) →
    SweepEv.PosW P J ztmgx ztmgy →
    (∀ i j, i ≤ j → j < c.nreg ztex →
      lsPr P J c.nmem ztwml ztwmp ztbih j →
      lsPr P J c.nmem ztwml ztwmp ztbih i) →
    c.nreg ALLOC + κ * ztuc ≤ W →
    IRS P W c₀ lsearch c ztxzd (fun c' =>
      c'.nreg lsI ≤ c.nreg ztex ∧
      (∀ j, j < c'.nreg lsI →
        lsPr P J c.nmem ztwml ztwmp ztbih j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c.nreg ztex →
        ¬ lsPr P J c.nmem ztwml ztwmp ztbih j) ∧
      ztrn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth)

/-- **The environment of the initialisation.** -/
structure IE (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (Eb : ℕ) (c₀ : Config)
    (rs : List ztcf) (ls : List ztck) : Prop where
  hA : AEnv P W X Ok J H N₁ N₂ Eb c₀
  od : OD P J N₂ c₀.nmem ztdpi ztrwf ztjt
    ztiah ztdaf rs ls
section env
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c₀ c : Config} {rs : List ztcf}
  {ls : List ztck}
theorem IE.fix (_e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c) {k : ℕ}
    (hk : k < 700) : c.nreg ztcbe = c₀.nreg ztcbe :=
  hI.hin _ ztze

/-- The outputs of stages 2 and 3 at a run configuration. -/
theorem IE.odc (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) {m : ℕ → ℕ}
    (hm : ∀ a, a < c₀.nreg ALLOC → m a = c₀.nmem a) :
    OD P J N₂ m ztdpi ztrwf ztjt
      ztiah ztdaf rs ls :=
  e.od.congr hm e.hA.hstops e.hA.hlog e.hA.htabw
theorem IE.st0 (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) :
    c₀.nreg ztfg = gW J ∧ c₀.nreg ztbex = cstR J 1 ∧
      c₀.nreg zthy = 2 * J.right.m + 7 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -⟩ := e.hA.hst
  exact ⟨h40 0 by_norm_num, h40 1 by_norm_num, h34⟩
theorem IE.nw (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c) :
    NFWithin c.nmem ztwrb ztm N₂ := by
  rw [e.fix hI (k := 4) by_norm_num]
  have hE := e.hA.hE
  exact (e.hA.hN₂.transport zthgt).mono (hE.trans hI.hA)
theorem ini_gW_lt_nat (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  exact_mod_cast gW_lt J

/-- **The binary search** for the key `(lsxE, lsxH)` at a run configuration. -/
theorem IE.search {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hx : PosW P J ztmgx ztmgy)
    (hroom : c.nreg ALLOC + κL * ztgf ≤ W) :
    IRS P W c₀ lsS c (κL * ztgf) (fun c' =>
      (∀ j, j < c'.nreg lsI → lsPr P J c.nmem ztwov ztead
        ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c₀.nreg ztex → ¬ lsPr P J c.nmem ztwov ztead
        ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      ztrn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have hA := e.hA
  have f300 := e.fix hI (k := 300) by_norm_num
  have f301 := e.fix hI (k := 301) by_norm_num
  have f40 := e.fix hI (k := 40) by_norm_num
  have fTB : ztgug := e.fix hI (k := 600) by_norm_num
  have fTL : ztguh := e.fix hI (k := 601) by_norm_num
  have g40 := e.st0.1
  have od := e.odc (m := c.nmem) zttj
  have hbig := hA.hbigE
  simp only [rd_sw] at hbig od
  zuerf
  simp only [rd_sw] at hlog
  have hTW := hA.hTW
  have h := hls P W J c₀ c hI hA.hK (hA.ctxW hI)
    (fun j hj => by
      rw [fTB, hI.hm _ by_omega]
      rw [fTL] at hj; exact hA.htab j hj)
    (by rw [fTB, fTL]; exact hTW.trans hI.hA)
    by_grind
    (by rw [f300, f301]; exact hlog.trans hI.hA)
    (by rw [f40, g40]; exact ini_gW_lt_nat J)
    (fun j hj => by rw [f300]; rw [f301] at hj; exact od.logW hj)
    hx
    (by rw [f300, f301, f40, g40]; exact od.down rfl _)
    by_simp_all
  rw [fTL, f300, f301, f40, g40] at h
  exact h.mono le_rfl (fun c' h' => h'.2)
set_option maxHeartbeats 4000000 in
/-- **The origin position of a stop record** by its kind. -/
theorem stOrg_irs (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c) {kind k b : ℕ}
    (hk1 : c.nreg ipK = kind) (hk2 : c.nreg ipKk = k) (hb : c.nreg ipS = sOf b)
    (hkind : kind ≤ 2) (hkk : kind = 1 → k < N₂.nChords) (hroom : c.nreg ALLOC + 11110 ≤ W) :
    IRS P W c₀ stOrg c 11110 (fun c' =>
      c'.nreg ipE = (stopPos P J N₂ kind k b).edge ∧ c'.nreg ipH = (stopPos P J N₂ kind k b).hgt ∧
      (∀ r, bandOf r ∉ oracleBands → ztftx → r ≠ ipE → r ≠ ipH →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhww
  obtain ⟨k0, k1, k6, -, -, k2, -⟩ := hK
  have h41 : c.nreg ztbex = cstR J 1 := (e.fix hI (k := 41) by_norm_num).trans e.st0.2.1
  have nE : ipH ≠ ipE := by_decide
  unfold stOrg
  by_cases c0 : kind = 0
  · refine (IRS.ifT (K := 2) by_omega ztleu).mono
      by_norm_num ?_
    · zubss
    · zuu
      refine ztfda
      · zueer
        rw [h41]; unfold stopPos; simp_all
      · zudlp
        zumvc
      · zudj
        simp_all
  refine (IRS.ifF (K := 11108) by_omega ?_).mono by_norm_num ztb
  by_cases c1 : kind = 1
  · subst c1
    refine (IRS.ifT (K := 11104) by_omega ?_).mono by_norm_num ztb
    have hko := hkk rfl
    refine IRS.seq (K₁ := 2) (K₂ := 11102) (IRS.block [.copyN oK ipKk, .copyN oS ipS] hI ?_) ?_
    · zunje
    zufg
    have v1 : ∀ r, r ≠ oK → r ≠ oS → regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg r =
        c.nreg r := fun r h1 h2 => by
      zuie
    have vK : regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg oK = k := by
      tauto
    have vS : regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg oS = sOf b := by
      tauto
    refine IRS.seq (K₁ := 11100) (K₂ := 2) (orgHead_irs hI₁ e.hA.hK ztvpl
      e.hA.hNF₂ ztvpq le_rfl by_simp_all
      (by simp only; rw [vS]; exact ini_sOf_le b) by_omega) ?_
    zubpv
    simp only at vE vC fr₂ hAl₂ hm₂
    zuhnq
    have eA : regB c.nmem [.copyN oK ipKk, .copyN oS ipS] c.nreg ALLOC = c.nreg ALLOC :=
      v1 _ by_decide by_decide
    rw [eA] at hAl₂ hm₂
    refine (IRS.block [.copyN ipE oE, .copyN ipH oC] hI₂ ?_).mono le_rfl ?_
    · zubss
    zuu
    refine ⟨?_, ?_, fun r hr h1 h2 h3 h4 => ?_, ?_, fun a ha => ?_⟩
    · tauto
    · tauto
    · zudj
      rw [upd_other _ _ _ h3, upd_other _ _ _ h2, fr₂ r hr zteo h4,
        v1 r ztmev ztmex]
    · tauto
    simp_all
  · have c2 : kind = 2 := by_omega
    refine (IRS.ifF (K := 2) by_omega ztleu).mono
      by_norm_num ?_
    · zubss
    · zuu
      refine ztfda
      · zueer
        rw [k6]; unfold stopPos; simp_all
      · zudlp
        zumvc
      · zudj
        simp_all
end env
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv
@[expose] public section
def kSt (κL TL : ℕ) : ℕ := 11137 + κL * zttdm
theorem sOf_eq {b : ℕ} (hb : b ≤ 1) : 1 - b = sOf b := by unfold sOf; grind

/-- A run step also gives the invariant at its end. -/
theorem IRS.withInv {P : Polygon} {W : ℕ} {c₀ c : Config} {s : Stmt} {K : ℕ}
    {Q : Config → Prop} (h : IRS P W c₀ s c K Q) :
    IRS P W c₀ s c K (fun c' => Q c' ∧ IInv W c₀ c') := by
  zums
  exact ⟨c', k, ex, hk, hI, hfr, hq, hI⟩

/-- The persistent registers of the loops. -/
def PReg (r : ℕ) : Prop := r = ipB ∨ r = ipM6 ∨ r = ipM5 ∨ r = ipJ ∨ r = ipKc
section stop
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c₀ c : Config} {rs : List ztcf}
  {ls : List ztck}
variable {lsS : Stmt} {κL : ℕ}
set_option maxHeartbeats 8000000 in
/-- **One stop record.** -/
theorem stB_irs (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg ztex ≤ c.nreg ALLOC)
    (hx : c.nreg ipX < c₀.nreg ztsn)
    (hS : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c.nmem (c.nreg ipX) 0)
    (hroom : c.nreg ALLOC + kSt κL ztdg ≤ W) :
    IRS P W c₀ (stB lsS) c ztzwp (fun c' =>
      c'.nreg ipX = c.nreg ipX + 1 ∧ ztcxl ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ ztzh ztwov ztwpq
        ztwpr ztdq c'.nmem (c.nreg ipX + 1) 0) := by
  zuuj

  set x := c.nreg ipX with hxd
  zuhww
  zubje

  have od := e.odc (m := c.nmem) hI.hm
  zufbz
  obtain ⟨pw, hkind, hb1, hkk⟩ := od.stopR hx
  have mc : ztezh :=
    fun d hd a ha => (hd.hm a ha).trans (hI.hm a ha).symm
  unfold stB
  -- read the record
  refine IRS.seq (K₁ := 14) (K₂ := kSt κL ztdg - 14)
    (stLd_irs hI hK (e.fix hI (k := 200) by_norm_num) rfl by_omega) ?_ |>.mono
    ztqgn ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨l1, l2, l3, l4, l5, lfr, lm⟩
  -- the origin
  refine IRS.seq (K₁ := 11110) (K₂ := kSt κL ztdg - 14 - 11110)
    (stOrg_irs e hI₁ l3 l4 (by rw [l5]; exact sOf_eq hb1) hkind hkk
      ztnvv) ?_ |>.mono (by unfold kSt; omega) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨o1, o2, ofr, oA, om⟩
  have k21 : ∀ r, bandOf r ∉ oracleBands → sw 2217 < r → r ≠ ipE → r ≠ ipH → r ≠ ALLOC →
      c₂.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 => ofr r h1 ztffu h3 h4 h5
  have q1 : c₂.nreg lsxE = c.nmem ztbbm :=
    (k21 _ ztmr
      by_decide by_decide by_decide
      by_decide).trans l1
  have q2 : c₂.nreg lsxH = c.nmem ztbdv :=
    (k21 _ ztmr
      by_decide by_decide by_decide
      by_decide).trans l2
  -- the search
  refine IRS.seq (K₁ := κL * ztgf) (K₂ := 13)
    (e.search hls hI₂ by_grind ztnvv) ?_ |>.mono
    ztqgn ztb
  rintro c₃ hI₃ hA₃ hA₃' ⟨s1, s2, sfr, sA, sm⟩
  have hq : (⟨c₂.nreg lsxE, c₂.nreg lsxH⟩ : WPos) =
      ⟨c₂.nmem ztbbm, c₂.nmem ztbdv⟩ := by
    rw [q1, q2, mc c₂ hI₂ _ by_omega, mc c₂ hI₂ ztbdv by_omega]
  zujju
  have od₂ := e.odc (m := c₂.nmem) hI₂.hm
  simp only [rd_sw] at od₂
  obtain ⟨ht, e1, e2, hv⟩ := stop_step od₂ e.hA.hP e.hA.hNF₂ rfl hx s1 s2
  rw [mc c₂ hI₂ ztdfe by_omega, mc c₂ hI₂ ztelq by_omega,
    mc c₂ hI₂ ztnt by_omega] at hv
  -- registers after the search
  have keep : ∀ r, 244100 ≤ r → r ≤ 244129 → r ≠ ipA → r ≠ ipK → r ≠ ipKk → r ≠ ipBb →
      r ≠ ipS → r ≠ ipE → r ≠ ipH → c₃.nreg r = c.nreg r := by
    intro r h1 h2 n1 n2 n3 n4 n5 n6 n7
    rw [sfr r ztbet ztbpz
      ztu, k21 r ztbet ztce
      n6 n7 ztu]
    exact lfr r (by unfold lsxE; unfold sw; omega) (by unfold lsxH; unfold sw; omega) n1 n2 n3 n4 n5
  have k3S : c₃.nreg ipS = sOf ztbagg := by
    rw [sfr _ ztmr
      (by unfold LSet ipS sw; omega) by_decide,
      k21 _ ztmr
      by_decide by_decide by_decide
      by_decide, l5, sOf_eq hb1]
  have k3E : c₃.nreg ipE = c₂.nreg ipE := sfr _ (not_oracle_sw by_decide
    by_decide) (by unfold LSet ipE sw; omega) by_decide
  have k3H : c₃.nreg ipH = c₂.nreg ipH := sfr _ (not_oracle_sw by_decide
    by_decide) (by unfold LSet ipH sw; omega) by_decide
  have k3B : c₃.nreg ipB = B := (keep ipB by_rfl by_decide
    by_decide by_decide by_decide
    by_decide by_decide by_decide
    by_decide).trans hB
  have hK₃ : Consts c₃ := e.hA.hK.fix hI₃
  -- the slot
  refine IRS.seq (K₁ := 12) (K₂ := 1) (slotSt_irs hI₃ hK₃ k3B rfl k3S le_rfl (by
    have := hI₃.hw.1 ALLOC
    have : c₀.nreg ztex = E := rfl
    have hs1 := ini_sOf_le ztbagg
    omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨w1, w2⟩
  have k1 : c₄.nreg K1 = 1 := (e.hA.hK.fix hI₄).2.1
  have k4X : c₄.nreg ipX = x := by
    zukzb
    exact keep ipX by_decide by_decide
      by_decide by_decide by_decide
      by_decide by_decide by_decide
      by_decide
  refine (IRS.instr1 (i := .addN ipX ipX K1) hI₄ ⟨iscr_sw by_decide
    by_decide, by_omega⟩).mono le_rfl ?_
  zuu
  refine ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · zubzz
  · have hx' : r ≠ ipX := by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipX, ipB, ipM6, ipM5, ipJ, ipKc, sw]
    have hT : r ≠ ipT := by
      zublk
    zuwc
    rw [upd_other _ _ _ hx', w2 r hT]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact keep _ by_decide
        by_decide
        by_decide
        by_decide
        by_decide
        by_decide
        by_decide
        by_decide
        by_decide
  · zuwc
    zunbw
    omega
  · zubi
    zumpe
    -- the invariant at the memory before the write
    have m3 : ∀ a, a < B + 6 * E → c₃.nmem a = c.nmem a := fun a ha => by
      rw [sm a by_omega, om a by_omega, lm]
    have hS₃ := hS.congr m3 by_omega by_omega by_omega
    have hv' : SlotVal P J ⟨c₃.nreg ipE, c₃.nreg ipH⟩ (sOf (c₂.nmem ztnt))
        (logPt P J c₂.nmem AL (c₃.nreg lsI)) := by
      rw [k3E, k3H, o1, o2, mc c₂ hI₂ ztnt by_omega]
      exact hv
    have r4 : c₃.nmem ztnt = c.nmem ztnt := mc c₃ hI₃ _ by_omega
    have h := hS₃.stopStep (m₂ := c₂.nmem) (fun a ha => (mc c₂ hI₂ a ha).trans
      (mc c₃ hI₃ a ha).symm) by_omega by_omega by_omega ht e1 e2 hv'
    grind

/-- **The stop loop.** -/
theorem stLoop_irs (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg ztex ≤ c.nreg ALLOC) (hx : c.nreg ipX = 0)
    (hS : SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq c.nmem 0 0)
    (hroom : c.nreg ALLOC + ztzgh * c₀.nreg ztsn ≤ W) :
    IRS P W c₀ ztwfb c (ztzgh * c₀.nreg ztsn + 2) (fun c' =>
      ztcxl ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ ztzh ztwov ztwpq
        ztwpr ztdq c'.nmem ztwuq 0) := by
  have f201 : ∀ d : Config, IInv W c₀ d → d.nreg ztsn = c₀.nreg ztsn :=
    fun d hd => e.fix hd (k := 201) by_norm_num
  let I : Config → Prop := fun d => (∀ r, PReg r → d.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ d.nreg ALLOC ∧ d.nreg ipX ≤ c₀.nreg ztsn ∧
    SInv P J N₂ ztzh ztwov ztwpq
      ztwpr ztdq d.nmem (d.nreg ipX) 0 ∧ d.nreg ztsn = c₀.nreg ztsn
  have hpB : PReg ipB := Or.inl rfl
  have h := IRS.while (P := P) (c₀ := c₀) (a := ipX) (b := sw 201) (body := stB lsS) I
    (fun d => c₀.nreg ztsn - d.nreg ipX) ztzwp
    (fun d hd hlt => by_omega)
    (fun d hId hd hlt hr => by
      obtain ⟨d1, d2, d3, d4, -⟩ := hd
      rw [f201 d hId] at hlt
      refine (IRS.withInv (stB_irs hls e hId ((d1 ipB hpB).trans hB) by_omega hlt d4 hr)).mono le_rfl ?_
      grind)
    hI ⟨fun _ _ => rfl, le_rfl, by_omega, by_simp_all, f201 c hI⟩ by_simp_all
  zvnly at h
  zujnu
  zuevu
  grind
