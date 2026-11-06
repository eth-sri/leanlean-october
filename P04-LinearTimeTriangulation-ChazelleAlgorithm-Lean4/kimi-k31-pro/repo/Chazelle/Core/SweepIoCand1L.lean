module

public import Chazelle.Core.SweepIoCand1G
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, local hits

`lhs md nf nr e t sh`: the inputs of the local hit (`setL`: the model descriptor in `md`, its
chain descriptor at the next address, the normal form in `nf`, the position `(e, qH)`, the
direction `qD`, the walk length in `nr`, the tag `t`), then the local hit.  `lhsR_irs`,
`lhsL_irs`: its run step in the models of `C₂` (`sw 31, 4, 34`) and `C₁` (`sw 30, 3, 33`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The inputs of the local hit. -/
def setL (md nf nr e t : ℕ) : List Instr :=
  [.copyN lMD md, .addN lCD lMD K1, .copyN lNF nf, .copyN lE e, .copyN lH qH, .copyN lD qD,
    .copyN lN nr, .constN lT t]

/-- A register outside the inputs of the local hit. -/
def OutL (r : ℕ) : Prop := r < sw 1100 ∨ sw 1107 < r

theorem setL_val (m f : ℕ → ℕ) {md nf nr e t : ℕ} (hmd : OutL md) (hnf : OutL nf) (hnr : OutL nr)
    (he : OutL e) :
    regB m (setL md nf nr e t) f lMD = f md ∧ regB m (setL md nf nr e t) f lCD = f md + f K1 ∧
    regB m (setL md nf nr e t) f lNF = f nf ∧ regB m (setL md nf nr e t) f lE = f e ∧
    regB m (setL md nf nr e t) f lH = f qH ∧ regB m (setL md nf nr e t) f lD = f qD ∧
    regB m (setL md nf nr e t) f lN = f nr ∧ regB m (setL md nf nr e t) f lT = t ∧
    (∀ q, OutL q → regB m (setL md nf nr e t) f q = f q) := by
  have ne : ∀ r, OutL r → r ≠ 241100 ∧ r ≠ 241101 ∧ r ≠ 241102 ∧ r ≠ 241103 ∧ r ≠ 241104 ∧
      r ≠ 241105 ∧ r ≠ 241106 ∧ r ≠ 241107 := fun r h => by ufo OutL sw at h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := ne _ hmd
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := ne _ hnf
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := ne _ hnr
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := ne _ he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩ <;>
    simp [setL, regB, regI, upd, lMD, lCD, lNF, lE, lH, lD, lN, lT, sw, K1, qH, qD, *]

theorem setL_ok (m f : ℕ → ℕ) {md nf nr e t : ℕ} (_hmd : OutL md) (hW : f md + 1 ≤ W)
    (hk : f K1 = 1) (ht : t ≤ W) : okB W m (setL md nf nr e t) f := by
  have s : ∀ j, 1100 ≤ j → j ≤ 1107 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by ufo sw) (by ufo sw)
  unfold OutL at _hmd
  simp only [setL, okB, okI, regI]
  refine ⟨s 1100 le_rfl (by norm_num), ⟨s 1101 (by norm_num) (by norm_num), ?_⟩,
    s 1102 (by norm_num) (by norm_num), s 1103 (by norm_num) (by norm_num),
    s 1104 (by norm_num) (by norm_num), s 1105 (by norm_num) (by norm_num),
    s 1106 (by norm_num) (by norm_num), ⟨s 1107 (by norm_num) le_rfl, ht⟩, trivial⟩
  have e1 : upd f lMD (f md) lMD = f md := upd_same _ _ _
  have e2 : upd f lMD (f md) K1 = f K1 := upd_other _ _ _ (by ufo K1 lMD sw)
  rwx [e1, e2, hk]

/-- **A local hit with its inputs.** -/
def lhs (md nf nr e t : ℕ) (sh : Stmt) : Stmt := .seq (block (setL md nf nr e t)) (localHit sh)

/-- The cost of `lhs`. -/
def lhsK (T Fg D : ℕ) : ℕ := 8 + localK T Fg (D + 1) D

/-- The post-condition of a local hit with its inputs at the position `(e, qH)`. -/
def LhPost (P : Polygon) (C : Chain) (Mod : ℕ → Chain) (R₀ : ℝ) (z : Point) (L : Set ℝ)
    (e : ℕ) (c c' : Config) : Prop :=
  (∃ L', AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
      (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt z (dirOf (c.nreg qD)) τ))) ∧
      (LHGeo P C ⟨c.nreg e, c.nreg qH⟩ (c.nreg qD) → C.hitParam z (dirOf (c.nreg qD)) ∈ L')) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

section Run

variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

/-- **The local hit with its inputs** (generic: the local-hit context from the inputs). -/
theorem lhs_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {C : Chain} {N : NF} {md nf nr e t : ℕ}
    (hfix : IFix md ∧ IFix nf ∧ IFix nr) (heo : OutL e) (hI : IInv W c₀ c)
    (hctx : ∀ c₁ : Config, IInv W c₀ c₁ → c₁.nreg lMD = c₀.nreg md →
      c₁.nreg lCD = c₀.nreg md + 1 → c₁.nreg lNF = c₀.nreg nf → LCtx P W C N E c₁)
    (hmdA : c₀.nreg md + 1 ≤ c₀.nreg ALLOC)
    (hOk : Ok P (chainModel C))
    (hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 5)))
    (hdeg : (chainModel C).DegLe (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 6)))
    (hnr : c₀.nreg nr = 2 * C.m + 7)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg e, c.nreg qH⟩)
    (hz : (chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg qH⟩ = z)
    (hy : |z.2| < C.radius)
    (hloc : (c.nreg e = 1 ∨ c.nreg e = 3) ∨ (6 ≤ c.nreg e ∧ z ∈ C.set))
    (hacc : AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L c) (ht : t ≤ 2) (hMod : Mod t = C)
    (hR : C.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (lhs md nf nr e t sh) c
      (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
      (LhPost P C Mod R₀ z L e c) := by
  obtain ⟨hfm, hfn, hfr⟩ := hfix
  have hK := hA.hK.fix hI
  have om : ∀ r, IFix r → OutL r := fun r h => by unfold IFix at h; ufo OutL sw
  have h8 : 8 ≤ lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) := by ufo lhsK
  have hmdW : c.nreg md + 1 ≤ W := by
    rw [hI.hin _ hfm]
    have := hI.hA; have := hI.hw.1 ALLOC; omega
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, vo⟩ :=
    setL_val c.nmem c.nreg (t := t) (om _ hfm) (om _ hfn) (om _ hfr) heo
  unfold lhs
  refine IRS.seq (K₁ := 8) (K₂ := localK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6) + 1)
      (c₀.nreg (sw 6)))
    ((IRS.block (setL md nf nr e t) hI (setL_ok c.nmem c.nreg (om _ hfm) hmdW hK.2.1
      (by have := hI.hw.1 ALLOC; omega))).mono (by simp [setL]) (fun _ => id)) ?_
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  subst hc₁
  simp only at *
  set c₁ : Config := { c with nreg := regB c.nmem (setL md nf nr e t) c.nreg } with hc₁d
  have r1 : ∀ r, OutL r → c₁.nreg r = c.nreg r := vo
  have hL : LCtx P W C N E c₁ := hctx c₁ hI₁
    (by show regB _ _ _ lMD = _; rw [v1, hI.hin _ hfm])
    (by show regB _ _ _ lCD = _; rw [v2, hI.hin _ hfm, hK.2.1])
    (by show regB _ _ _ lNF = _; rw [v3, hI.hin _ hfn])
  obtain ⟨hAr, hCh⟩ := SweepEv.region_bounds hL.hP hL.hNF hdeg
  have eTL : c₁.nreg TLR = c₀.nreg TLR := hI₁.hin _ (by ufo IFix TLR sw)
  have a1 : c₁.nreg lE = c.nreg e := v4
  have a2 : c₁.nreg lH = c.nreg qH := v5
  have a3 : c₁.nreg lD = c.nreg qD := v6
  have hacc₁ : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c₁.nreg lE, c₁.nreg lH⟩)
      (dirOf (c₁.nreg lD)) L c₁ := by
    rw [a1, a2, a3, hz]
    exact hacc.transport (fun j hj => r1 _ (by ufo OutL accA sw))
  have h := localHit_irs (x := ⟨c₁.nreg lE, c₁.nreg lH⟩) (d := c₁.nreg lD)
    (Da := c₀.nreg (sw 6) + 1) (Dc := c₀.nreg (sw 6)) hsh hBs hXl hI₁ hA.hK hL hA.hX hA.hcap
    hOk hsg hAr hCh rfl rfl rfl
    (by show c₁.nreg lE < _; rwx [a1])
    (by show ProperPos _ _ _ ⟨c₁.nreg lE, c₁.nreg lH⟩; rwx [a1, a2])
    (by rwx [a1, a2, hz])
    (by rwx [a1, a2, hz])
    hacc₁ (by rwx [show c₁.nreg lT = t from v8])
    (by rwx [show c₁.nreg lT = t from v8]) hR
    (by rwx [show c₁.nreg lN = c.nreg nr from v7, hI.hin _ hfr])
    (by
      have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := r1 _ (by ufo OutL ALLOC sw)
      ruo [eTL, hA1] lhsK at hroom)
  rw [eTL] at h
  refine h.mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
  rw [a1, a2, a3, hz] at a' g' geo'
  refine ⟨⟨L', a', s', g', fun hg => (geo' hg).2⟩, fun r h1 h2 h3 => ?_, hA', fun a ha => ?_⟩
  · rw [fr r h1 h2 h3]
    exact r1 r (by unfold LHW sw at h2; ufo OutL sw)
  · exact hm' a ha

/-- **The local hit in the model of `C₂`** (model descriptor `sw 31`, normal form `sw 4`). -/
theorem lhsR_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {e t : ℕ} (heo : OutL e) (hI : IInv W c₀ c)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg e, c.nreg qH⟩)
    (hz : (chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg qH⟩ = z)
    (hy : |z.2| < J.right.radius)
    (hloc : (c.nreg e = 1 ∨ c.nreg e = 3) ∨ (6 ≤ c.nreg e ∧ z ∈ J.right.set))
    (hacc : AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L c) (ht : t ≤ 2) (hMod : Mod t = J.right)
    (hR : J.right.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (lhs (sw 31) (sw 4) (sw 34) e t sh) c
      (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
      (LhPost P J.right Mod R₀ z L e c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h34, -, -, -, -, w31⟩ := hA.hst
  exact lhs_irs hsh hBs hXl hA
    ⟨by ufo IFix sw, by ufo IFix sw, by ufo IFix sw⟩ heo hI
    (fun c₁ hI₁ a b d => AEnv.lctxR hA hI₁ a b d) (by have := w31.1; omega) hA.hOk₂ hA.hsg₂
    hA.hdeg₂ h34 he hpp hz hy hloc hacc ht hMod hR hroom

/-- **The local hit in the model of `C₁`** (model descriptor `sw 30`, normal form `sw 3`). -/
theorem lhsL_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {e t : ℕ} (heo : OutL e) (hI : IInv W c₀ c)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel J.left).W.n)
    (hpp : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg e, c.nreg qH⟩)
    (hz : (chainModel J.left).pos (Qof P) ⟨c.nreg e, c.nreg qH⟩ = z)
    (hy : |z.2| < J.left.radius)
    (hloc : (c.nreg e = 1 ∨ c.nreg e = 3) ∨ (6 ≤ c.nreg e ∧ z ∈ J.left.set))
    (hacc : AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L c) (ht : t ≤ 2) (hMod : Mod t = J.left)
    (hR : J.left.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (lhs (sw 30) (sw 3) (sw 33) e t sh) c
      (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
      (LhPost P J.left Mod R₀ z L e c) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h33, -, -, -, w30, -, -⟩ := hA.hst
  exact lhs_irs hsh hBs hXl hA
    ⟨by ufo IFix sw, by ufo IFix sw, by ufo IFix sw⟩ heo hI
    (fun c₁ hI₁ a b d => AEnv.lctxL hA hI₁ a b d) (by have := w30.1; omega) hA.hOk₁ hA.hsg₁
    hA.hdeg₁ h33 he hpp hz hy hloc hacc ht hMod hR hroom

end Run

end Cand1

end

end SweepIo

end Chazelle.Core
