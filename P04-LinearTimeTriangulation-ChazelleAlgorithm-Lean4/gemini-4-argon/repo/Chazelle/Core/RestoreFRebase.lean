module

public import Chazelle.Core.RestoreFTest

/-!
# WP-E, the search on the RAM (`FindOK`), part 24: rebasing

After a call of the cutter, its output lies above the base allocator of the search.  The run
facts `FGood` hold again from any later configuration `c₀'` of the search (`FGood.rebase`, with
the base memory and allocator of `c₀'`), and a run step from `c₀'` is a run step from `c₀`
(`FRS.restrict`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs

/-- The environment rebased at `c₀'`. -/
def FEnv.re (E : FEnv) (c₀' : Config) : FEnv := { E with A₀ := c₀'.nreg ALLOC, m₀ := c₀'.nmem }

variable {E : FEnv} {c₀ c₀' : Config}

/-- **Rebasing the run facts.** -/
theorem FGood.rebase (hE : FGood E c₀) (hI : FInv E.W c₀ c₀') : FGood (E.re c₀') c₀' := by
  have hag : ∀ a, a < E.A₀ → c₀'.nmem a = E.m₀ a := hI.agree hE
  have hA : E.A₀ ≤ c₀'.nreg ALLOC := hI.allocA hE
  have hag' : ∀ a, a < E.A₀ → E.m₀ a = c₀'.nmem a := fun a ha => (hag a ha).symm
  obtain ⟨hMD', hwf'⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
  have hfx : ∀ q, FFix q → c₀'.nreg q = c₀.nreg q := hI.hin
  have hMD0 : c₀'.nmem E.MD = E.m₀ E.MD := hag _ (by have := hE.hwf.1; omega)
  have hback : c₀'.nmem E.MD = 0 → ∀ H C, ChainDescAt c₀'.nmem (E.MD + 1) (Qof E.P) H C →
      ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C := fun h0 H C hC => by
    have hW := (hwf'.2 h0).2 H C hC
    exact ShotList.chainDescAt_copy hC hW.2.2.1 hag' (fun j hj => hag' _ (by have := hE.hwf.1; omega))
  exact {
    hT := hE.hT, hcu := hE.hcu, hBc := hE.hBc, hBo := hE.hBo, hB8 := hE.hB8, hloc := hE.hloc,
    hhalf := hE.hhalf, hOkM := hE.hOkM, hG := hE.hG, hWh := hE.hWh,
    hX := E.X.mono _ _ _ _ _ hA (E.X.local_ _ _ _ _ _ hag' hE.hX),
    hcap := by
      show E.γ ≤ E.X.cap E.P c₀'.nmem E.g
      rw [hE.hloc _ _ _ _ _ hag hE.hX]; exact hE.hcap
    hwf := hwf'.mono hA
    hreg := fun h0 H C hC => hE.hreg (by rwa [← hMD0]) H C (hback h0 H C hC)
    hsimp := fun h0 H C hC => hE.hsimp (by rwa [← hMD0]) H C (hback h0 H C hC)
    hMD := hMD', hGM := hE.hGM, hOk := hE.hOk,
    hNW := (Robust.transport hE.hNW hag).mono hA
    hNF := hE.hNF, hdeg := hE.hdeg, hsg := hE.hsg, hr := hE.hr, a0 := rfl, m0 := rfl,
    i0 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i0
    i1 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i1
    i2 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i2
    i3 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i3
    i4 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i4
    i5 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i5
    i6 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.i6
    k0 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k0
    k1 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k1
    k2 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k2
    k3 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k3
    k5 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k5
    k7 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k7
    pn := by rw [hfx _ (by unfold FFix; omega)]; exact hE.pn
    nE := by rw [hfx _ (by unfold FFix; omega)]; exact hE.nE
    hE2 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.hE2
    wn := by rw [hfx _ (by unfold FFix; omega)]; exact hE.wn
    k10 := by rw [hfx _ (by unfold FFix; omega)]; exact hE.k10
    hvr := by
      rw [hfx 81021 (by unfold FFix; omega), hfx 81019 (by unfold FFix; omega)]; exact hE.hvr
    hvc := by
      rw [hfx 81021 (by unfold FFix; omega), hfx 81019 (by unfold FFix; omega)]; exact hE.hvc
    vlo6 := by rw [hfx 81021 (by unfold FFix; omega)]; exact hE.vlo6
    ehr := by
      rw [hfx 81021 (by unfold FFix; omega), hfx 81025 (by unfold FFix; omega)]; exact hE.ehr
    ehc := by
      rw [hfx 81021 (by unfold FFix; omega), hfx 81025 (by unfold FFix; omega)]; exact hE.ehc }

/-- **A run step from a later base** is a run step from the earlier one. -/
theorem FRS.restrict {B : Finset ℕ} {P : Polygon} {W : ℕ} {s : Stmt} {c : Config} {K : ℕ}
    {Q : Config → Prop} (hI : FInv W c₀ c₀') (h : FRS B P W c₀' s c K Q)
    (hc : c₀.nreg ALLOC ≤ c₀'.nreg ALLOC) : FRS B P W c₀ s c K Q := by
  obtain ⟨c', k, ex, hk, hI', hrf, hq⟩ := h
  refine ⟨c', k, ex, hk, ⟨hI'.hw, fun q hq => (hI'.hin q hq).trans (hI.hin q hq), le_trans hI.hA hI'.hA,
    fun a ha => (hI'.hm a (by omega)).trans (hI.hm a ha)⟩, ?_, hq⟩
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := hrf
  exact ⟨r₁, rr₁, fun a ha => m₁ a (by omega), fun a ha => rm₁ a (by omega), o₁, a₁, b₁⟩

end

end Restore

end Chazelle.Core
