module

public import Chazelle.Core.SweepIoCand1M
public import Chazelle.Core.SweepRamInit
public import Chazelle.Core.RestoreTKey
public import Chazelle.Core.MergeAsmDesc
public import Chazelle.Core.SweepIoBruteMath

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the environment

From `AEnv` at the base `c₀` and `IInv`: the chain contexts of `C₂` (`sw 21`), `C₁` (`sw 20`) and
`C` (`sw 2`). `q1_facts`: the facts of a side-1 query.
-/

namespace Chazelle.Core

namespace SweepIo

open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}

namespace AEnv
variable (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c)
omit hA in
include hI in
theorem fixr {r : ℕ} (hr : IFix r) : c.nreg r = c₀.nreg r := hI.hin r hr

include hA in
abbrev hreg := @Chazelle.Core.SweepIo.AEnv.hostReg



include hA hI in
theorem ctxW : ChainCtx P W c (sw 2) J.whole := by
  obtain ⟨-, -, -, -, hJ, hJWF, -⟩ := hA.hst
  obtain ⟨hC, hw⟩ := chainDesc_keep hJWF.2.2.1 hJ.2.2 (fun a ha => hI.hm a ha) hI.hA
  rw [← fixr hI (show IFix (sw 2) by unfold IFix sw; omega)] at hC hw
  exact ⟨hA.hG, hA.hWh, hw, ⟨H, hC, hA.hreg⟩, hA.hP, hA.hWm⟩

end AEnv

/-- **The facts of a side-1 query** at the candidate step. -/
theorem q1_facts {z : Point} (hq : QState P J 1 z c) :
    J.rightModel.pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = z ∧
      c.nreg qE < J.rightModel.W.n ∧
      ProperPos J.rightModel (Qof P) P.n ⟨c.nreg qE, c.nreg qH⟩ ∧
      |z.2| < J.right.radius ∧ z.2 ≤ J.right.top.2 ∧
      PosClass J.right (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ∧
      LHGeo P J.right ⟨c.nreg qE, c.nreg qH⟩ (c.nreg qD) ∧
      (dirOf (c.nreg qD) = 1 ∨ dirOf (c.nreg qD) = -1) ∧ 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n ∧
      ((Qof P).vtx (c.nreg qH - 1)).2 = z.2 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq.hq
  have hz := hq.hz
  have hht := hq.hht
  simp only [sideChain_one] at h1 h4 h5 h6 h7 hz hht
  simp only at h2 h3
  have hσ : dirOf (c.nreg qD) = 1 ∨ dirOf (c.nreg qD) = -1 := SweepPrim.dirOf_cases _
  have hsec : sideLeft J.rightModel.W (c.nreg qE)
      (J.rightModel.param (Qof P) ⟨c.nreg qE, c.nreg qH⟩)
      (rayPt (J.rightModel.pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩) (dirOf (c.nreg qD)) 1) := by
    have e : rayPt (J.rightModel.pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩) (dirOf (c.nreg qD)) 1 =
        ((J.rightModel.pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩).1 + dirOf (c.nreg qD),
          (J.rightModel.pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩).2) := by
      simp [Chazelle.Visibility.rayPt]
    rwa [e]
  have habs : |(J.rightModel.pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩).2| < J.right.radius :=
    query_abs h1 h4 h5 h6 hσ hsec
  have hpc := posClass_of h1 h4 h5 habs (Or.inl h6)
  rw [hz] at habs h6 hht
  refine ⟨hz, h1, ⟨h4, h5, by rwa [← hQn]⟩, habs, h6, hpc,
    ⟨c.nreg qH - 1, by show c.nreg qH = _; omega, by omega, by rw [hz, hht], hsec, by rwa [hz]⟩,
    hσ, h2, by omega, hht.symm⟩

end

end SweepIo

end Chazelle.Core
