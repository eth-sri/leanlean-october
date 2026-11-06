module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvStopRB

/-!
# The sweep (WP-D), stage 2: a local hit saved as a candidate (RAM)

`lhSave sh md cd nf nr F`: the local hit (`lhRun`) and the save of its result into `F … F + 6`
(`lhSave_irs`, post `ResOK`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **A local hit, saved** into `F … F + 6`. -/
def lhSave (sh : Stmt) (md cd nf nr F : ℕ) : Stmt :=
  .seq (lhRun sh md cd nf nr) (block (saveL F))

/-- The registers of `lhSave` (besides the oracle bands). -/
def LHSW (F : ℕ) (r : ℕ) : Prop := LHR r ∨ (F ≤ r ∧ r ≤ F + 6)

theorem lhSave_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {md cd nf nr Fo : ℕ}
    (hd : DR md) (hc : DR cd) (hn : DR nf) (hr : DR nr) (hFo : 244000 ≤ Fo ∧ Fo + 6 < 250000)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hM : MCtx P W C N E md cd nf c) (hPs : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC))
    (hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10)))
    (hOk : Ok P (chainModel C))
    (hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 5)))
    (hdeg : (chainModel C).DegLe (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 6)))
    (hnr : c.nreg nr = 2 * C.m + 7) {x : WPos} (hxE : c.nreg lE = x.edge)
    (hxH : c.nreg lH = x.hgt) (hxD : c.nreg lD ≤ 1) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n x) (hcl : PosClass C (Qof P) x)
    (hy : |((chainModel C).pos (Qof P) x).2| < C.radius)
    (hon : (chainModel C).pos (Qof P) x ∈ C.set ∨
      |((chainModel C).pos (Qof P) x).1| = C.radius)
    {Gd : Prop}
    (hGd : Gd → sideLeft (chainModel C).W x.edge ((chainModel C).param (Qof P) x)
        (rayPt ((chainModel C).pos (Qof P) x) (dirOf (c.nreg lD)) 1) ∧
      ((chainModel C).pos (Qof P) x).2 ≤ C.top.2)
    (hroom : c.nreg ALLOC + (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7) ≤ W) :
    IRS P W c₀ (lhSave sh md cd nf nr Fo) c
      (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7) (fun c' =>
      ResOK P C ((chainModel C).pos (Qof P) x) (dirOf (c.nreg lD)) Gd Fo c' ∧
      EFr (LHSW Fo) c c') := by
  unfold lhSave
  refine IRS.seq (lhRun_irs hsh hBs hXl hd hc hn hr hI hK hG hWh hM hPs hNF hX hcap hOk hsg
    hdeg hnr hxE hxH hxD he hpp hcl hy hon (⋄)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨L', hacc, hL, hgeo, hfr⟩
  refine (save_irs hI₁ hFo hacc hL (fun g => hgeo (hGd g)) (fun g => (hGd g).2)
    (SweepStop.dirOf_cases' _)).mono le_rfl ?_
  rintro c' ⟨hres, hk, hm⟩
  have hAl : c'.nreg ALLOC = c₁.nreg ALLOC := hk ALLOC (by unfold ALLOC; omega)
  refine ⟨hres, fun r h1 h2 h3 => ?_, hAl ▸ hfr.2.1, fun a ha => ?_⟩
  · have h2' : ¬ (LHR r ∨ (Fo ≤ r ∧ r ≤ Fo + 6)) := h2
    rw [hk r (⋄)]
    exact hfr.1 r h1 (fun h => h2' (Or.inl h)) h3
  · rw [hm]; exact hfr.2.2 a ha

end

end SweepEv

end Chazelle.Core
