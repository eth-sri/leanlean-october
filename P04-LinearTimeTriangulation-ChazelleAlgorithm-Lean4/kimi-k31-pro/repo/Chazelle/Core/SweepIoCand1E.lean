module

public import Chazelle.Core.SweepIoCand1M
public import Chazelle.Core.SweepRamInit
public import Chazelle.Core.RestoreTKey
public import Chazelle.Core.MergeAsmDesc
public import Chazelle.Core.SweepIoBruteMath
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the environment

From `AEnv` at the base `c₀` and `IInv`: the chain contexts of `C₂` (`sw 21`), `C₁` (`sw 20`) and
`C` (`sw 2`), and the local-hit contexts of the models of `C₂` and `C₁` with the model descriptors
`sw 31`, `sw 30` (`lctxR`, `lctxL`; the chain descriptors at `sw 31 + 1`, `sw 30 + 1` are copies of
those at `sw 21`, `sw 20`, `AEnv.hmd₂`, `AEnv.hmd₁`).  `q1_facts`: the facts of a side-1 query.
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
theorem hreg : HostRegular P.n H := by
  obtain ⟨-, -, -, -, hJ, hJWF, -⟩ := hA.hst
  exact hJWF.2.2.2 H hJ.2.2.1



include hA hI in
theorem ctxW : ChainCtx P W c (sw 2) J.whole := by
  obtain ⟨-, -, -, -, hJ, hJWF, -⟩ := hA.hst
  obtain ⟨hC, hw⟩ := chainDesc_keep hJWF.2.2.1 hJ.2.2 (hI.hm) hI.hA
  rw [← fixr hI (show IFix (sw 2) by ufo IFix sw)] at hC hw
  exact ⟨hA.hG, hA.hWh, hw, ⟨H, hC, hA.hreg⟩, hA.hP, hA.hWm⟩

include hA hI in
/-- The local-hit context of the model of `C₂`. -/
theorem lctxR (h1 : c.nreg lMD = c₀.nreg (sw 31)) (h2 : c.nreg lCD = c₀.nreg (sw 31) + 1)
    (h3 : c.nreg lNF = c₀.nreg (sw 4)) : LCtx P W J.right N₂ E c := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -, -, -, -, -, -, -, -, -, d31, w31⟩ := hA.hst
  have h0 : c₀.nmem (c₀.nreg (sw 31)) = 0 := by
    rcases d31 with ⟨h, -⟩ | ⟨-, -, hM⟩
    · exact h
    · exact absurd hM (Restore.chainModel_ne_interior _ _)
  obtain ⟨-, -, hEb, -⟩ := w21.2 H J.right d21
  have hcd : ChainDescAt c₀.nmem (c₀.nreg (sw 31) + 1) (Qof P) H J.right :=
    MergeAsm.chainDescAt_copy d21 hEb (fun a _ => rfl) (hA.hmd₂)
  have hwf' : ChainWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg (sw 31) + 1) :=
    MergeAsm.chainWF_copy w21 d21 (fun a _ => rfl) (hA.hmd₂)
      (by have := w31.1; omega) le_rfl
  have hmwf : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg (sw 31)) := ⟨w31.1, fun _ => hwf'⟩
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  obtain ⟨hC, hw⟩ := chainDesc_keep hwf' hcd hm hI.hA
  obtain ⟨mwfc, m0c, mdc⟩ := ShotList.modelDesc_keep hmwf h0 hcd hm hI.hA
  have hTB := fixr hI (show IFix TBR by ufo IFix TBR sw)
  have hTL := fixr hI (show IFix TLR by ufo IFix TLR sw)
  refine
    { hG := hA.hG
      hWh := hA.hWh
      hctx := ⟨hA.hG, hA.hWh, by rwx [h2], ⟨H, by rwx [h2], hA.hreg⟩,
        hA.hP, by have := hA.hWm; have : J.right.m ≤ J.whole.m := by
                    show J.m₂ ≤ J.m₁ + J.m₂; omega
                  omega⟩
      hcd := by rw [h1, h2]
      hmd := by rw [h1]; exact Or.inl ⟨m0c, H, J.right, mdc, rfl⟩
      hmwf := by rw [h1]; exact mwfc
      hm0 := by rw [h1]; exact m0c
      hP := hA.hP
      hNW := by rw [h3]; exact hA.hN₂.transport (fun a ha => hm a (by have := hA.hE; omega))
      hE := by have := hA.hE; have := hI.hA; omega
      hNF := hA.hNF₂
      htab := fun j hj => by
        rw [hTL] at hj; rw [hTB, hm _ (by have := hA.hTW; omega)]; exact hA.htab j hj
      hbig := by rw [hTL]; exact hA.hbig₂
      hTB := by rw [hTB]; exact hA.hTB
      hTW := by rw [hTB, hTL]; have := hA.hTW; have := hI.hA; omega }

include hA hI in
/-- The local-hit context of the model of `C₁`. -/
theorem lctxL (h1 : c.nreg lMD = c₀.nreg (sw 30)) (h2 : c.nreg lCD = c₀.nreg (sw 30) + 1)
    (h3 : c.nreg lNF = c₀.nreg (sw 3)) : LCtx P W J.left N₁ E c := by
  obtain ⟨-, -, -, -, -, -, d20, w20, -, -, -, -, -, -, -, -, -, d30, w30, -, -⟩ := hA.hst
  have h0 : c₀.nmem (c₀.nreg (sw 30)) = 0 := by
    rcases d30 with ⟨h, -⟩ | ⟨-, -, hM⟩
    · exact h
    · exact absurd hM (Restore.chainModel_ne_interior _ _)
  obtain ⟨-, -, hEb, -⟩ := w20.2 H J.left d20
  have hcd : ChainDescAt c₀.nmem (c₀.nreg (sw 30) + 1) (Qof P) H J.left :=
    MergeAsm.chainDescAt_copy d20 hEb (fun a _ => rfl) (hA.hmd₁)
  have hwf' : ChainWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg (sw 30) + 1) :=
    MergeAsm.chainWF_copy w20 d20 (fun a _ => rfl) (hA.hmd₁)
      (by have := w30.1; omega) le_rfl
  have hmwf : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg (sw 30)) := ⟨w30.1, fun _ => hwf'⟩
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  obtain ⟨hC, hw⟩ := chainDesc_keep hwf' hcd hm hI.hA
  obtain ⟨mwfc, m0c, mdc⟩ := ShotList.modelDesc_keep hmwf h0 hcd hm hI.hA
  have hTB := fixr hI (show IFix TBR by ufo IFix TBR sw)
  have hTL := fixr hI (show IFix TLR by ufo IFix TLR sw)
  refine
    { hG := hA.hG
      hWh := hA.hWh
      hctx := ⟨hA.hG, hA.hWh, by rwx [h2], ⟨H, by rwx [h2], hA.hreg⟩,
        hA.hP, by have := hA.hWm; have : J.left.m ≤ J.whole.m := by
                    show J.m₁ ≤ J.m₁ + J.m₂; omega
                  omega⟩
      hcd := by rw [h1, h2]
      hmd := by rw [h1]; exact Or.inl ⟨m0c, H, J.left, mdc, rfl⟩
      hmwf := by rw [h1]; exact mwfc
      hm0 := by rw [h1]; exact m0c
      hP := hA.hP
      hNW := by rw [h3]; exact hA.hN₁.transport (fun a ha => hm a (by have := hA.hE; omega))
      hE := by have := hA.hE; have := hI.hA; omega
      hNF := hA.hNF₁
      htab := fun j hj => by
        rw [hTL] at hj; rw [hTB, hm _ (by have := hA.hTW; omega)]; exact hA.htab j hj
      hbig := by rw [hTL]; exact hA.hbig₁
      hTB := by rw [hTB]; exact hA.hTB
      hTW := by rw [hTB, hTL]; have := hA.hTW; have := hI.hA; omega }

end AEnv

/-- **The facts of a side-1 query** at the candidate step. -/
theorem q1_facts {z : Point} (hq : QState P J 1 z c) :
    (chainModel J.right).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = z ∧
      c.nreg qE < (chainModel J.right).W.n ∧
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg qE, c.nreg qH⟩ ∧
      |z.2| < J.right.radius ∧ z.2 ≤ J.right.top.2 ∧
      PosClass J.right (Qof P) ⟨c.nreg qE, c.nreg qH⟩ ∧
      LHGeo P J.right ⟨c.nreg qE, c.nreg qH⟩ (c.nreg qD) ∧
      (dirOf (c.nreg qD) = 1 ∨ dirOf (c.nreg qD) = -1) ∧ 1 ≤ c.nreg qH ∧ c.nreg qH ≤ P.n ∧
      ((Qof P).vtx (c.nreg qH - 1)).2 = z.2 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq.hq
  have hz := hq.hz
  have hht := hq.hht
  simp [sideChain_one] at h1 h4 h5 h6 h7 hz hht
  simp at h2 h3
  have hσ : dirOf (c.nreg qD) = 1 ∨ dirOf (c.nreg qD) = -1 := SweepPrim.dirOf_cases _
  have hsec : sideLeft (chainModel J.right).W (c.nreg qE)
      ((chainModel J.right).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩)
      (rayPt ((chainModel J.right).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩) (dirOf (c.nreg qD)) 1) := by
    have e : rayPt ((chainModel J.right).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩) (dirOf (c.nreg qD)) 1 =
        (((chainModel J.right).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩).1 + dirOf (c.nreg qD),
          ((chainModel J.right).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩).2) := by
      simp [Chazelle.Visibility.rayPt]
    rwx [e]
  have habs  := query_abs h1 h4 h5 h6 hσ hsec
  have hpc := posClass_of h1 h4 h5 habs (Or.inl h6)
  rw [hz] at habs h6 hht
  refine ⟨hz, h1, ⟨h4, h5, by rwx [← hQn]⟩, habs, h6, hpc,
    ⟨c.nreg qH - 1, by show c.nreg qH = _; omega, by omega, by rw [hz, hht], hsec, by rwx [hz]⟩,
    hσ, h2, by omega, hht.symm⟩

end

end SweepIo

end Chazelle.Core
