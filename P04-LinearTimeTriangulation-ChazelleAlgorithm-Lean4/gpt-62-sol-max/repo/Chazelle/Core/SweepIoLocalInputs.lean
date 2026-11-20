module

meta import Chazelle.Programs.RegisterGuard

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.SweepEvGenM
public import Chazelle.Core.SweepIoSpec

/-! The shared setup and run specification for local hits on either side of a junction. -/

namespace Chazelle.Core.SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

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

theorem setL_ok (m f : ℕ → ℕ) {md nf nr e t : ℕ} (hW : f md + 1 ≤ W)
    (hk : f K1 = 1) (ht : t ≤ W) : okB W m (setL md nf nr e t) f := by
  register_block normalized [setL]

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
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem)

section Run

variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The local hit with its inputs** (generic: the local-hit context from the inputs). -/
theorem lhsWithContext_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
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
  have om : ∀ r, IFix r → OutL r := fun r h => by unfold IFix at h; unfold OutL sw; omega
  have hmdW : c.nreg md + 1 ≤ W := by
    rw [hI.hin _ hfm]
    have := hI.hA; have := hI.hw.1 ALLOC; omega
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, vo⟩ :=
    setL_val c.nmem c.nreg (md := md) (t := t) (om _ hfn) (om _ hfr) heo
  unfold lhs
  refine IRS.seq (K₁ := 8) (K₂ := localK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6) + 1)
      (c₀.nreg (sw 6)))
    ((IRS.block (setL md nf nr e t) hI (setL_ok c.nmem c.nreg hmdW hK.2.1
      (by unfold lhsK at hroom; omega))).mono (by simp [setL]) (fun _ h => h)) ?_
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  have hm₁ : c₁.nmem = c.nmem := by rw [hc₁]
  have hreg₁ : c₁.nreg = regB c.nmem (setL md nf nr e t) c.nreg := by rw [hc₁]
  rw [← hreg₁] at v1 v2 v3 v4 v5 v6 v7 v8 vo
  have hL := hctx c₁ hI₁
    (by rw [v1, hI.hin _ hfm]) (by rw [v2, hI.hin _ hfm, hK.2.1]) (by rw [v3, hI.hin _ hfn])
  obtain ⟨hAr, hCh⟩ := SweepEv.region_bounds hL.hP hL.hNF hdeg
  have eTL := hI₁.hin TLR (by register_guard)
  have hAA := vo ALLOC (by register_guard)
  have hacc₁ : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c₁.nreg lE, c₁.nreg lH⟩)
      (dirOf (c₁.nreg lD)) L c₁ := by
    rw [v4, v5, v6, hz]
    exact hacc.transport (fun j hj => vo _ (by register_guard))
  have h := localHit_irs (x := ⟨c₁.nreg lE, c₁.nreg lH⟩) (d := c₁.nreg lD)
    (Da := c₀.nreg (sw 6) + 1) (Dc := c₀.nreg (sw 6)) hsh hBs hXl hI₁ hA.hK hL hA.hX hA.hcap
    hOk hsg hAr hCh rfl rfl rfl
    (by rwa [v4])
    (by rwa [v4, v5])
    (by rw [v4, v5, hz]; exact hy)
    (by rw [v4, v5, hz]; exact hloc)
    hacc₁ (by rwa [v8])
    (by rwa [v8]) hR
    (by rwa [v7, hI.hin _ hfr])
    (by
      rw [eTL, hAA]; unfold lhsK at hroom; omega)
  rw [eTL] at h
  refine h.mono le_rfl ?_
  rintro c' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
  rw [v4, v5, v6, hz] at a' g' geo'
  refine ⟨⟨L', a', s', g', fun hg => (geo' hg).2⟩, fun r h1 h2 h3 => ?_, by omega, fun a ha => ?_⟩
  · rw [fr r h1 h2 h3]
    exact vo r (by unfold LHW sw at h2; unfold OutL sw; omega)
  · rw [hm' a (by omega), hm₁]

end Run

end

end Chazelle.Core.SweepIo
