module

public import Chazelle.Core.SweepEvStopM2C

/-!
# The sweep (WP-D), stage 2: the candidate of `C₂` of a stop origin (task M2, part 2)

`m2c_lh_irs`: the local hit in the model of `C₂` from a position `(e, h)` (setting `lE, lH, lD`,
then `lhSave` into `r2F`).
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
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

theorem m2c_M2R_lh {r : ℕ} (h : LHSW r2F r) : M2R r := by
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by unfold sw at *; omega, by unfold sw at *; omega⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by unfold r2F at h; omega,
      by unfold r2F at h; unfold sw at *; omega⟩)))

theorem m2c_M2R_set {r : ℕ} (h : r = lE ∨ r = lH ∨ r = lD) : M2R r := by
  left; rcases h with rfl | rfl | rfl <;> simp [lE, lH, lD, sw]

theorem m2c_nr (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg (sw 34) = 2 * J.right.m + 7 := by
  rw [hI.hin _ (by unfold IFix sw; omega)]
  obtain ⟨H, -, hst⟩ := E.hst
  exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The local hit of `C₂` from a position** `(e, h)`, saved at `r2F`. -/
theorem m2c_lh_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c) {e h : ℕ}
    (he : e ≠ lE ∧ e ≠ lH) (hh : h ≠ lE) (hb : c.nreg oB ≤ 1)
    (hxe : c.nreg e < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hcl : PosClass J.right (Qof P) ⟨c.nreg e, c.nreg h⟩)
    (hy : |((chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).2| < J.right.radius)
    (hon : (chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩ ∈ J.right.set ∨
      |((chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).1| = J.right.radius)
    {Gd : Prop}
    (hGd : Gd → sideLeft (chainModel J.right).W (c.nreg e)
        ((chainModel J.right).param (Qof P) ⟨c.nreg e, c.nreg h⟩)
        (rayPt ((chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩) (dirOf (c.nreg oB)) 1) ∧
      ((chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).2 ≤ J.right.top.2)
    (hroom : c.nreg ALLOC +
      (3 + (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7)) ≤ W) :
    IRS P W c₀ (.seq (block (m2cSet e h)) (lhSave sh gMD2 gCD2 (sw 4) (sw 34) r2F)) c
      (3 + (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7)) (fun c' =>
      ResOK P J.right ((chainModel J.right).pos (Qof P) ⟨c.nreg e, c.nreg h⟩)
        (dirOf (c.nreg oB)) Gd r2F c' ∧
      EFr (fun r => (r = lE ∨ r = lH ∨ r = lD) ∨ LHSW r2F r) c c') := by
  refine IRS.seq (IRS.block (m2cSet e h) hI (m2cSet_ok _ _ e h)) ?_
  rintro c₁ hI₁ - - hc1
  obtain ⟨vE, vH, vD, vo⟩ := m2cSet_val c.nmem c.nreg he hh
  have v1E : c₁.nreg lE = c.nreg e := by rwa [hc1]
  have v1H : c₁.nreg lH = c.nreg h := by rwa [hc1]
  have v1D : c₁.nreg lD = c.nreg oB := by rwa [hc1]
  have k1 : ∀ q, q ≠ lE → q ≠ lH → q ≠ lD → c₁.nreg q = c.nreg q := fun q a b d => by
    rw [hc1]; exact vo q a b d
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold lE ALLOC sw; omega)
    (by unfold lH ALLOC sw; omega) (by unfold lD ALLOC sw; omega)
  have hM₁ : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c₁ :=
    MCtx.transport hM (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact k1 _ (by simp [gMD2, gCD2, TBR, TLR, lE, sw]) (by simp [gMD2, gCD2, TBR, TLR, lH, sw])
          (by simp [gMD2, gCD2, TBR, TLR, lD, sw]))
      (fun a _ => by rw [hm1]) (by rw [hA1])
  have hnr : c₁.nreg (sw 34) = 2 * J.right.m + 7 := m2c_nr E hI₁
  refine (lhSave_irs E.hsh E.hBs E.hXl (Or.inr ⟨by simp [gMD2, sw], by simp [gMD2, sw]⟩)
    (Or.inr ⟨by simp [gCD2, sw], by simp [gCD2, sw]⟩) (Or.inl ⟨by simp [sw], by simp [sw]⟩)
    (Or.inl ⟨by simp [sw], by simp [sw]⟩) ⟨by simp [r2F, sw], by simp [r2F, sw]⟩ hI₁ E.hK E.hG
    E.hWh hM₁ E.hP E.hNF₂ E.hX E.hcap E.hOk₂ E.hsg₂ E.hdeg₂ hnr (x := ⟨c.nreg e, c.nreg h⟩) v1E v1H
    (by rwa [v1D]) hxe hpp hcl hy hon (Gd := Gd) (by rwa [v1D])
    (by rw [hA1]; omega)).mono le_rfl ?_
  rintro c' ⟨hres, hfr⟩
  rw [v1D] at hres
  refine ⟨hres, EFr.trans ⟨fun r h1 h2 h3 => k1 r ?_ ?_ ?_, by rw [hA1], fun a _ => by rw [hm1]⟩
    (hfr.mono fun r hr => Or.inr hr)⟩
  · intro hq; exact h2 (Or.inl (Or.inl hq))
  · intro hq; exact h2 (Or.inl (Or.inr (Or.inl hq)))
  · intro hq; exact h2 (Or.inl (Or.inr (Or.inr hq)))

theorem m2c_M2R_lh' {r : ℕ} (h : (r = lE ∨ r = lH ∨ r = lD) ∨ LHSW r2F r) : M2R r := by
  rcases h with h | h
  · exact m2c_M2R_set h
  · exact m2c_M2R_lh h

end

end SweepEv

end Chazelle.Core
