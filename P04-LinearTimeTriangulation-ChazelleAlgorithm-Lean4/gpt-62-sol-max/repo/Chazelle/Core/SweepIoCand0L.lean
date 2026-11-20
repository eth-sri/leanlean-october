module

public import Chazelle.Core.SweepIoCand0M
public import Chazelle.Core.SweepIoLocalInputs

/-!
# The sweep RAM (WP-D), answers: local hits on either side

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
  hfix : IFix md ∧ IFix nf ∧ IFix nr

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
    hA.hN₁, hA.hE, hA.hNF₁, hA.hOk₁, hA.hsg₁, hA.hdeg₁, hA.hbig₁, h33, by and_intros <;> reg_omega⟩

/-- **The side of `C₂`.** -/
theorem sideD₂ (hA : AEnv P W X Ok J H N₁ N₂ E c₀) :
    SideD P W Ok c₀ J.right N₂ E (sw 31) (sw 21) (sw 4) (sw 34) := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -, -, -, -, -, h34, -, -, -, d31, w31⟩ := hA.hst
  exact ⟨ctx_of_aenv hA d21 w21 hA.hP (by show J.m₂ ≤ J.m₁ + J.m₂; omega), d31, w31, hA.hmd₂,
    hA.hN₂, hA.hE, hA.hNF₂, hA.hOk₂, hA.hsg₂, hA.hdeg₂, hA.hbig₂, h34, by and_intros <;> reg_omega⟩

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
    · exact absurd hI' (Restore.chainModel_ne_interior C _)
  have he : MemEqBelow (c₀.nreg ALLOC) c.nmem c₀.nmem := fun a ha => hI.hm a ha
  have hc : ∀ j, j < 5 → c.nmem (c₀.nreg md + 1 + j) = c₀.nmem (c₀.nreg cd + j) := fun j hj => by
    rw [he _ (by have := hmw.1; omega)]; exact hS.hcopy j hj
  have hC' : ChainDescAt c.nmem (c₀.nreg md + 1) (Qof P) H C := chainDescAt_copy hC hEb he hc
  have hw' : ChainWF P (c.nreg ALLOC) c.nmem (c₀.nreg md + 1) :=
    chainWF_copy hwf hC he hc (by have := hmw.1; have := hI.hA; omega) hI.hA
  have hm0' : c.nmem (c₀.nreg md) = 0 := by rw [he _ (by have := hmw.1; omega)]; exact hm0
  have eTB : c.nreg TBR = c₀.nreg TBR := hI.hin _ (by reg_omega)
  have eTL : c.nreg TLR = c₀.nreg TLR := hI.hin _ (by reg_omega)
  refine ⟨hG, hWh, ⟨hG, hWh, by rw [hcd]; exact hw', ⟨H, by rw [hcd]; exact hC', hreg⟩, hP, hWm⟩,
    by rw [hcd, hmd], by rw [hmd]; exact Or.inl ⟨hm0', H, C, hC', rfl⟩,
    by rw [hmd]; exact ⟨by have := hmw.1; have := hI.hA; omega, fun _ => hw'⟩,
    by rw [hmd]; exact hm0', hP, by rw [hnf]; exact hS.hNW.transport (fun a ha => he a
      (by have := hS.hE; omega)), by have := hS.hE; have := hI.hA; omega, hS.hNF,
    fun j hj => ?_, by rw [eTL]; exact hS.hbig, by rw [eTB]; exact hTB,
    by rw [eTB, eTL]; have := hI.hA; omega⟩
  rw [eTL] at hj
  rw [eTB, he _ (by omega)]
  exact htab j hj

section Run

variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The local hit with its inputs**: from `AEnv` and the facts `SideD` of a side, at the
position `x = (e, qH)` of its chain model. -/
theorem lhs_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {C : Chain} {N : NF} {md cd nf nr e t : ℕ} (hS : SideD P W Ok c₀ C N E md cd nf nr)
    (heo : OutL e) (hI : IInv W c₀ c)
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
      (LhPost P C Mod R₀ z L e c) :=
  lhsWithContext_irs hsh hBs hXl hA hS.hfix heo hI
    (fun _ hI₁ => lctx_of hS hI₁ hA.htab hA.hTB hA.hTW) (by have := hS.hmwf.1; omega)
    hS.hOk hS.hsg hS.hdeg hS.hnr he hpp hz hy hloc hacc ht hMod hR hroom

end Run

end

end SweepIo

end Chazelle.Core
