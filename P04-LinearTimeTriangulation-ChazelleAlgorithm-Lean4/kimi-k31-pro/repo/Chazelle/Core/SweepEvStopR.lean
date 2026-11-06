module

public import Chazelle.Core.SweepEvStopLH
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ConfigTactics
set_option maxHeartbeats 4000000

/-!
# The sweep (WP-D), stage 2: registers, the model contexts, the model descriptor of `C₂` (RAM)

Registers of stage 2 (all in `S2R`): globals `sw 4000 …`, the origin `sw 4010 …`, the label
procedure and the parent scan `sw 4070 …`.

* `mctx1`: the context of the model of `C₁` (`MD₁`, `CD₁`, `sw 3`) for the local hit;
* `md2Init`: a model descriptor of `C₂` in fresh memory (`gMD2`, `gCD2`), `md2Init_irs`, giving
  `MCtx` for `C₂` (`sw 4`);
* `MCtx.transport`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers -/

def gRB : ℕ := sw 4000
def gRC : ℕ := sw 4001
def gMD2 : ℕ := sw 4002
def gCD2 : ℕ := sw 4003
def gTP : ℕ := sw 4005
def gTV : ℕ := sw 4006

/-! ## The model contexts -/

theorem MCtx.transport {C : Chain} {N : NF} {E md cd nf : ℕ} {c c' : Config}
    (h : MCtx P W C N E md cd nf c)
    (hr : ∀ r, r = md ∨ r = cd ∨ r = nf ∨ r = TBR ∨ r = TLR → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    MCtx P W C N E md cd nf c' := by
  obtain ⟨hctx, hcd, hmd, hmwf, hm0, hNW, hE, htab, hbig, hTB, hTW⟩ := h
  have rMD := hr md (Or.inl rfl)
  have rCD := hr cd (Or.inr (Or.inl rfl))
  have rNF := hr nf (Or.inr (Or.inr (Or.inl rfl)))
  have rTB := hr TBR (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have rTL := hr TLR (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rcases hmd with ⟨-, H, C', hC', hMC⟩ | ⟨h1, -⟩
  swap
  · rwo [hm0] at h1
  obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hmwf hm0 hC' hm hA
  refine ⟨hctx.transport rCD hm hA, by rwx [rCD, rMD],
    by rw [rMD]; exact Or.inl ⟨w2, H, C', w3, hMC⟩, by rwx [rMD], by rwx [rMD],
    by rw [rNF]; exact hNW.transport fun b hb => hm b (by omega), le_trans hE hA,
    fun j hj => by
      rw [rTL] at hj; rw [rTB, hm _ (by omega)]; exact htab j hj,
    by rwx [rTL], by rwx [rTB], by rwo [rTB, rTL]⟩

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The context of the model of `C₁`.** -/
theorem mctx1 (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    MCtx P W J.left N₁ (c₀.nreg TBR) MD₁ CD₁ (sw 3) c := by
  have hTBR : c.nreg TBR = c₀.nreg TBR := hI.hin _ (by ufo IFix TBR sw)
  have hTLR : c.nreg TLR = c₀.nreg TLR := hI.hin _ (by ufo IFix TLR sw)
  have h3 : c.nreg (sw 3) = c₀.nreg (sw 3) := hI.hin _ (by ufo IFix sw)
  obtain ⟨md1, md2, md3, md4⟩ := E.md hI
  have hTA := E.hTBR
  refine ⟨E.ctx1' hI, md4, md1, md2, md3, ?_, by have := hI.hA; omega, fun j hj => ?_,
    by rw [hTLR]; exact E.hbig₁, by rw [hTBR], by rw [hTBR, hTLR]; have := hI.hA; omega⟩
  · rw [h3]; exact E.hNT₁.transport fun b hb => hI.hm b (by omega)
  · rw [hTLR] at hj; rw [hTBR, hI.hm _ (by omega)]; exact E.htab j hj

/-! ## The model descriptor of `C₂` -/

/-- **A model descriptor of `C₂`** in fresh memory: `0` and a copy of the chain descriptor of
`C₂` (`sw 21`). -/
def md2Init : Stmt :=
  block [.copyN 244002 9999, .storeN 9999 240610, .addN 9999 9999 240611,
    .copyN 244005 240021,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .addN 244003 244002 240611]

/-- The registers `md2Init` writes. -/
def MD2W (r : ℕ) : Prop := r = gMD2 ∨ r = gCD2 ∨ r = gTP ∨ r = gTV

theorem md2Init_exec (c : Config) (hw : WordsBounded W c) (k0 : c.nreg 240610 = 0)
    (k1 : c.nreg 240611 = 1) (hroom : c.nreg 9999 + 6 ≤ W) (hB : c.nreg 240021 + 5 ≤ c.nreg 9999) :
    ∃ c' k, Exec P W md2Init c c' k ∧ k = 25 ∧
      c'.nreg 9999 = c.nreg 9999 + 6 ∧ c'.nreg 244002 = c.nreg 9999 ∧
      c'.nreg 244003 = c.nreg 9999 + 1 ∧
      (∀ r, r ≠ 9999 → r ≠ 244002 → r ≠ 244003 → r ≠ 244005 → r ≠ 244006 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem (c.nreg 9999) = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg 9999 + 1 + j) = c.nmem (c.nreg 240021 + j)) ∧
      (∀ a, a < c.nreg 9999 → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold md2Init
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, by cso, by config_simp, by cso, fun r h1 h2 h3 h4 h5 => ?_,
    ?_, fun j hj => ?_, fun a ha => ?_, rfl, rfl, rfl⟩
  · config_simp; simp [upd, h1, h2, h3, h4, h5]
  · config_simp; simp [upd]; split_ifs <;> first | omega
  · config_simp
    simp [upd]
    interval_cases j <;> split_ifs <;> first | omega | (· simp_all)
  · config_simp; simp [upd]; split_ifs <;> first | omega

/-- **The model descriptor of `C₂`** as a run step: the context of the model of `C₂` at
`gMD2, gCD2, sw 4`. -/
theorem md2Init_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hroom : c.nreg ALLOC + 25 ≤ W) :
    IRS P W c₀ md2Init c 25 (fun c' => MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c' ∧
      (∀ r, ¬ MD2W r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hK := E.hK.fix hI
  have k0 : c.nreg 240610 = 0 := hK.1
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have hctx := E.ctx2' hI
  obtain ⟨hG, hWh, hwf, ⟨H, hC, hreg⟩, hPs, hWm⟩ := hctx
  have hB : c.nreg 240021 + 5 ≤ c.nreg 9999 := hwf.1
  obtain ⟨c', k, ex, hk, a1, a2, a3, hreg', m0, mc, mlo, rr, rm, ro⟩ :=
    md2Init_exec (P := P) c hI.hw k0 k1 (by ufo ALLOC at hroom) hB
  have a1' : c'.nreg ALLOC = c.nreg ALLOC + 6 := a1
  have a2' : c'.nreg gMD2 = c.nreg ALLOC := a2
  have a3' : c'.nreg gCD2 = c.nreg ALLOC + 1 := a3
  have m0' : c'.nmem (c.nreg ALLOC) = 0 := m0
  have mc' : ∀ j, j < 5 → c'.nmem (c.nreg ALLOC + 1 + j) = c.nmem (c.nreg (sw 21) + j) := mc
  have mlo' : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a := mlo
  have hwf' : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 21)) := hwf
  have hC' : ChainDescAt c.nmem (c.nreg (sw 21)) (Qof P) H J.right := hC
  obtain ⟨hMD, hMWF, hCD⟩ := SweepRam.modelDesc_of_copy (E' := c'.nreg ALLOC) hwf' hC'
    le_rfl mlo' m0' mc' (by rw [a1'])
  have hTBR : c'.nreg TBR = c₀.nreg TBR := by
    rw [hreg' _ (by ufo TBR sw) (by ufo TBR sw) (by ufo TBR sw)
      (by ufo TBR sw) (by ufo TBR sw)]
    exact hI.hin _ (by ufo IFix TBR sw)
  have hTLR : c'.nreg TLR = c₀.nreg TLR := by
    rw [hreg' _ (by ufo TLR sw) (by ufo TLR sw) (by ufo TLR sw)
      (by ufo TLR sw) (by ufo TLR sw)]
    exact hI.hin _ (by ufo IFix TLR sw)
  have h4 : c'.nreg (sw 4) = c₀.nreg (sw 4) := by
    rw [hreg' _ (by ufo sw) (by ufo sw) (by ufo sw)
      (by ufo sw) (by ufo sw)]
    exact hI.hin _ (by ufo IFix sw)
  have hA : c.nreg ALLOC ≤ c'.nreg ALLOC := by show c.nreg 9999 ≤ c'.nreg 9999; omega
  have hTA := E.hTBR
  have hmem : ∀ a, a < c₀.nreg ALLOC → c'.nmem a = c₀.nmem a := fun a ha => by
    rw [mlo a (by have := hI.hA; show a < c.nreg 9999; ufo ALLOC at *)]; exact hI.hm a ha
  have hI' : IInv W c₀ c' := by
    refine ⟨ex.wb_right, fun q hq => ?_, le_trans hI.hA hA, hmem, fun a ha => by rw [rm]; exact hI.hrm a ha⟩
    unfold IFix at hq
    rw [hreg' q (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hI.hin q (by ufo IFix)
  refine ⟨c', k, ex, by omega, hI', ⟨fun r hr hra => ?_, fun r _ => by rw [rr], ro, hA,
    by show c'.nreg 9999 ≤ c.nreg 9999 + k; omega⟩, ?_, fun r hr hra => ?_, hA, mlo'⟩
  · have : ¬ (240000 ≤ r ∧ r < 250000) := fun h => hr (scr_band (iscr_sw (by
      by_contra h'; exact hr (by
        unfold ioBands sweepBands; rwd [band_sw h.1 h.2])) h.2))
    exact hreg' r hra (by omega) (by omega) (by omega) (by omega)
  · refine ⟨⟨hG, hWh, ?_, ⟨H, ?_, hreg⟩, hPs, hWm⟩, by rw [a3', a2'], by rwx [a2'],
      by rwx [a2'], by rwx [a2'], by rw [h4]; exact E.hNT₂.transport (fun b hb =>
        hmem b (by omega)), by have := hI.hA; omega, fun j hj => ?_, by rw [hTLR]; exact E.hbig₂,
      by rw [hTBR], by rw [hTBR, hTLR]; have := hI.hA; omega⟩
    · rw [a3']; exact hMWF.2 m0'
    · rwx [a3']
    · rw [hTLR] at hj; rw [hTBR, hmem _ (by omega)]; exact E.htab j hj
  · unfold MD2W gMD2 gCD2 gTP gTV sw at hr
    exact hreg' r hra (by omega) (by omega) (by omega) (by omega)

end

end SweepEv

end Chazelle.Core
