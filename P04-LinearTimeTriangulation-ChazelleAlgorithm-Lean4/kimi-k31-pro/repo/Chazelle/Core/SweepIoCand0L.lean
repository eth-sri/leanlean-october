module

public import Chazelle.Core.SweepIoCand0M
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `0`, local hits

`lhs md nf nr e t sh`: the inputs of the local hit (`setL`: the model descriptor in `md`, its
chain descriptor at the next address, the normal form in `nf`, the position `(e, qH)`, the
direction `qD`, the walk length in `nr`, the tag `t`), then the local hit.

* `SideD`: the facts of `c₀` about one side (chain, model descriptor and its chain descriptor
  copy (`AEnv.hmd₁`, `hmd₂`), normal form); `sideD₁` (`C₁`: `sw 30, 20, 3, 33`), `sideD₂` (`C₂`:
  `sw 31, 21, 4, 34`);
* `lctx_of`: the local-hit context from `SideD`;
* `lhs_irs`: the run step of `lhs`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open ShotList (chainDescAt_copy chainWF_copy)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The facts of one side -/

/-- **The facts of `c₀` about one side** (chain `C`, normal form `N` with bound `E`): the chain
descriptor in `cd`, the model descriptor in `md` holding a copy of it, the normal form in `nf`,
the walk length in `nr`. -/
structure SideD (P : Polygon) (W : ℕ) (Ok : Polygon → Model → Prop) (c₀ : Config) (C : Chain)
    (N : NF) (E md cd nf nr : ℕ) : Prop where
  hctx : ChainCtx P W c₀ cd C
  hmd : ModelDescAt c₀.nmem (c₀.nreg md) (Qof P) (chainModel C)
  hmwf : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg md)
  hcopy : ∀ j, j < 5 → c₀.nmem (c₀.nreg md + 1 + j) = c₀.nmem (c₀.nreg cd + j)
  hNW : NFWithin c₀.nmem (c₀.nreg nf) E N
  hE : E ≤ c₀.nreg ALLOC
  hNF : IsNF (chainModel C) (Qof P) N
  hOk : Ok P (chainModel C)
  hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 5))
  hdeg : (chainModel C).DegLe (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 6))
  hbig : N.arcs.length < 2 ^ c₀.nreg TLR
  hnr : c₀.nreg nr = 2 * C.m + 7

theorem chainModel_ne_int (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  intro h
  have := congrArg (fun M : Model => M.counted 0) h
  simp [chainModel, interiorModel] at this

section AEnv

variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

/-- The chain context of a chain descriptor of the stage-0 state. -/
theorem ctx_of_aenv (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {C : Chain} {cd : ℕ}
    (hC : ChainDescAt c₀.nmem (c₀.nreg cd) (Qof P) H C)
    (hw : ChainWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg cd)) (hP : C.P.Simple)
    (hm : C.m ≤ J.whole.m) : ChainCtx P W c₀ cd C := by
  obtain ⟨-, -, -, -, hJ, hJW, -⟩ := hA.hst
  refine ⟨hA.hG, hA.hWh, hw, ⟨H, hC, hJW.2.2.2 H hJ.2.2.1⟩, hP, ?_⟩
  have := hA.hWm; omega

/-- **The side of `C₁`.** -/
theorem sideD₁ (hA : AEnv P W X Ok J H N₁ N₂ E c₀) :
    SideD P W Ok c₀ J.left N₁ E (sw 30) (sw 20) (sw 3) (sw 33) := by
  obtain ⟨-, -, -, -, -, -, d20, w20, -, -, -, -, -, -, h33, -, -, d30, w30, -, -⟩ := hA.hst
  exact ⟨ctx_of_aenv hA d20 w20 hA.hP (by show J.m₁ ≤ J.m₁ + J.m₂; omega), d30, w30, hA.hmd₁,
    hA.hN₁, hA.hE, hA.hNF₁, hA.hOk₁, hA.hsg₁, hA.hdeg₁, hA.hbig₁, h33⟩

/-- **The side of `C₂`.** -/
theorem sideD₂ (hA : AEnv P W X Ok J H N₁ N₂ E c₀) :
    SideD P W Ok c₀ J.right N₂ E (sw 31) (sw 21) (sw 4) (sw 34) := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -, -, -, -, -, h34, -, -, -, d31, w31⟩ := hA.hst
  exact ⟨ctx_of_aenv hA d21 w21 hA.hP (by show J.m₂ ≤ J.m₁ + J.m₂; omega), d31, w31, hA.hmd₂,
    hA.hN₂, hA.hE, hA.hNF₂, hA.hOk₂, hA.hsg₂, hA.hdeg₂, hA.hbig₂, h34⟩

end AEnv

/-- **The local-hit context** at a configuration whose `lMD`, `lCD`, `lNF` hold the model
descriptor, its chain descriptor and the normal form of a side. -/
theorem lctx_of {Ok : Polygon → Model → Prop} {C : Chain} {N : NF} {E md cd nf nr : ℕ}
    (hS : SideD P W Ok c₀ C N E md cd nf nr) (hI : IInv W c₀ c)
    (htab : ∀ j, j < c₀.nreg TLR → c₀.nmem (c₀.nreg TBR + j) = 2 ^ j)
    (hTB : E ≤ c₀.nreg TBR) (hTW : c₀.nreg TBR + c₀.nreg TLR ≤ c₀.nreg ALLOC)
    (hmd : c.nreg lMD = c₀.nreg md) (hcd : c.nreg lCD = c₀.nreg md + 1)
    (hnf : c.nreg lNF = c₀.nreg nf) : LCtx P W C N E c := by
  obtain ⟨hG, hWh, hwf, ⟨H, hC, hreg⟩, hP, hWm⟩ := hS.hctx
  have hmw := hS.hmwf
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hC
  have hm0 : c₀.nmem (c₀.nreg md) = 0 := by
    rcases hS.hmd with ⟨h0, -⟩ | ⟨-, -, hI'⟩
    · exact h0
    · exact absurd hI' (chainModel_ne_int C _)
  have he : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  have hc : ∀ j, j < 5 → c.nmem (c₀.nreg md + 1 + j) = c₀.nmem (c₀.nreg cd + j) := fun j hj => by
    rw [he _ (by have := hmw.1; omega)]; exact hS.hcopy j hj
  have hC'  := chainDescAt_copy hC hEb he hc
  have hw' : ChainWF P (c.nreg ALLOC) c.nmem (c₀.nreg md + 1) :=
    chainWF_copy hwf hC he hc (by have := hmw.1; have := hI.hA; omega) hI.hA
  have hm0' : c.nmem (c₀.nreg md) = 0 := by rwx [he _ (by have := hmw.1; omega)]
  have eTB : c.nreg TBR = c₀.nreg TBR := hI.hin _ (by ufo IFix TBR sw)
  have eTL : c.nreg TLR = c₀.nreg TLR := hI.hin _ (by ufo IFix TLR sw)
  refine ⟨hG, hWh, ⟨hG, hWh, by rwx [hcd], ⟨H, by rwx [hcd], hreg⟩, hP, hWm⟩,
    by rw [hcd, hmd], by rw [hmd]; exact Or.inl ⟨hm0', H, C, hC', rfl⟩,
    by rw [hmd]; exact ⟨by have := hmw.1; have := hI.hA; omega, fun _ => hw'⟩,
    by rwx [hmd], hP, by rw [hnf]; exact hS.hNW.transport (fun a ha => he a
      (by have := hS.hE; omega)), by have := hS.hE; have := hI.hA; omega, hS.hNF,
    fun j hj => ?_, by rw [eTL]; exact hS.hbig, by rwx [eTB],
    by rw [eTB, eTL]; have := hI.hA; omega⟩
  rw [eTL] at hj
  rw [eTB, he _ (by omega)]
  exact htab j hj

/-! ## The inputs of the local hit -/

/-- The inputs of the local hit: model descriptor `md` (its chain descriptor at the next
address), normal form `nf`, walk length `nr`, the position `(e, qH)`, the direction `qD`, the
tag `t`. -/
def setL (md nf nr e t : ℕ) : List Instr :=
  [.copyN lMD md, .addN lCD lMD K1, .copyN lNF nf, .copyN lE e, .copyN lH qH, .copyN lD qD,
    .copyN lN nr, .constN lT t]

/-- A register outside the inputs of the local hit. -/
def OutL (r : ℕ) : Prop := r < sw 1100 ∨ sw 1107 < r

theorem setL_val (m f : ℕ → ℕ) {md nf nr e t : ℕ} (hnf : OutL nf) (hnr : OutL nr)
    (he : OutL e) :
    regB m (setL md nf nr e t) f lMD = f md ∧ regB m (setL md nf nr e t) f lCD = f md + f K1 ∧
    regB m (setL md nf nr e t) f lNF = f nf ∧ regB m (setL md nf nr e t) f lE = f e ∧
    regB m (setL md nf nr e t) f lH = f qH ∧ regB m (setL md nf nr e t) f lD = f qD ∧
    regB m (setL md nf nr e t) f lN = f nr ∧ regB m (setL md nf nr e t) f lT = t ∧
    (∀ q, OutL q → regB m (setL md nf nr e t) f q = f q) := by
  unfold OutL sw at hnf hnr he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩ <;>
  · try unfold OutL sw at hq
    simp (disch := omega) only [setL, regB, regI, lMD, lCD, lNF, lE, lH, lD, lN, lT, K1, qH, qD,
      sw, Nat.reduceAdd, upd_same, upd_other]

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

/-! ## Region bounds -/

/-- **Arcs and exit chords of the regions** of a normal form of degree `≤ D`. -/
theorem region_bounds' {C : Chain} {Q : Polygon} {N : NF} {D : ℕ} (hP : C.P.Simple)
    (hNF : IsNF (chainModel C) Q N) (hdeg : (chainModel C).DegLe (N.F (chainModel C) Q) D) :
    (∀ r, r < N.nRegions → (N.region r).arcs.length ≤ D + 1) ∧
      (∀ r, r < N.nRegions → (N.region r).chords.length ≤ D) := by
  have hNF' := hNF
  obtain ⟨-, -, -, reg, hRC, hCS, hAO, hRO, -⟩ := hNF'
  have hregs : Restore.NFRegs (chainModel C) Q N reg := ⟨hRC, hCS, hAO, hRO⟩
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have := Restore.arcs_le_deg hGM hNF hregs hr
    have := hdeg (reg r) (hRC.1 r hr)
    omega
  · have := Restore.chords_le_deg hNF hregs hr
    have := hdeg (reg r) (hRC.1 r hr)
    omega

/-! ## The run step -/

section Run

variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

/-- **The local hit with its inputs**: from `AEnv` and the facts `SideD` of a side, at the
position `x = (e, qH)` of its chain model. -/
theorem lhs_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {C : Chain} {N : NF} {md cd nf nr e t : ℕ} (hS : SideD P W Ok c₀ C N E md cd nf nr)
    (hfix : IFix md ∧ IFix nf ∧ IFix nr) (heo : OutL e) (hI : IInv W c₀ c)
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
      (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) (fun c' =>
      (∃ L', AccOK P accA Mod R₀ z (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
        (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt z (dirOf (c.nreg qD)) τ))) ∧
        (LHGeo P C ⟨c.nreg e, c.nreg qH⟩ (c.nreg qD) → C.hitParam z (dirOf (c.nreg qD)) ∈ L')) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  obtain ⟨hfm, hfn, hfr⟩ := hfix
  have hK := hA.hK.fix hI
  have om : ∀ r, IFix r → OutL r := fun r h => by unfold IFix at h; ufo OutL sw
  have hmdW : c.nreg md + 1 ≤ W := by
    rw [hI.hin _ hfm]
    have := hS.hmwf.1; have := hI.hA; have := hI.hw.1 ALLOC; omega
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, vo⟩ :=
    setL_val c.nmem c.nreg (md := md) (t := t) (om _ hfn) (om _ hfr) heo
  unfold lhs
  refine IRS.seq (K₁ := 8) (K₂ := localK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6) + 1)
      (c₀.nreg (sw 6)))
    ((IRS.block (setL md nf nr e t) hI (setL_ok c.nmem c.nreg (om _ hfm) hmdW hK.2.1
      (by ufo lhsK at hroom))).mono (by simp [setL]) (fun _ => id)) ?_
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  have hm₁ : c₁.nmem = c.nmem := by rw [hc₁]
  have hreg₁ : c₁.nreg = regB c.nmem (setL md nf nr e t) c.nreg := by rw [hc₁]
  rw [← hreg₁] at v1 v2 v3 v4 v5 v6 v7 v8 vo
  have r1 : ∀ r, OutL r → c₁.nreg r = c.nreg r := vo
  have hL  := lctx_of hS hI₁ hA.htab hA.hTB hA.hTW
    (by rw [v1, hI.hin _ hfm])
    (by rw [v2, hI.hin _ hfm, hK.2.1])
    (by rw [v3, hI.hin _ hfn])
  obtain ⟨hAr, hCh⟩ := region_bounds' hL.hP hS.hNF hS.hdeg
  have eTL : c₁.nreg TLR = c₀.nreg TLR := hI₁.hin _ (by ufo IFix TLR sw)
  have hacc₁ : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c₁.nreg lE, c₁.nreg lH⟩)
      (dirOf (c₁.nreg lD)) L c₁ := by
    rw [v4, v5, v6, hz]
    exact hacc.transport (fun j hj => r1 _ (by ufo OutL accA sw))
  have h := localHit_irs (x := ⟨c₁.nreg lE, c₁.nreg lH⟩) (d := c₁.nreg lD) (Da := c₀.nreg (sw 6) + 1)
    (Dc := c₀.nreg (sw 6)) hsh hBs hXl hI₁ hA.hK hL hA.hX hA.hcap hS.hOk hS.hsg hAr hCh rfl rfl rfl
    (by rwx [v4]) (by rwx [v4, v5]) (by rwx [v4, v5, hz])
    (by rwx [v4, v5, hz])
    hacc₁ (by rwx [v8]) (by rwx [v8]) hR
    (by rw [v7, hI.hin _ hfr]; exact hS.hnr)
    (by ruo [eTL] lhsK at hroom)
  rw [eTL] at h
  refine h.mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
  rw [v4, v5, v6, hz] at a' g'
  rw [v4, v5, v6] at geo'
  rw [hz] at geo'
  have hAA : c₁.nreg ALLOC = c.nreg ALLOC := r1 ALLOC (by ufo OutL ALLOC sw)
  refine ⟨⟨L', a', s', g', fun hg => (geo' hg).2⟩, fun r h1 h2 h3 => ?_, by omega,
    fun a ha => ?_⟩
  · rw [fr r h1 h2 h3]
    exact r1 r (by unfold LHW sw at h2; ufo OutL sw)
  · rw [hm' a (by omega), hm₁]

end Run

end

end SweepIo

end Chazelle.Core
