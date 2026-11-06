module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopRA

/-!
# The sweep (WP-D), stage 2: the first hits of the models of `C₁` and `C₂` (RAM, part 1)

`ResOK`: a saved candidate (flag `F`, position `F + 1, F + 2`, abscissa record `F + 3 … F + 6`)
of the first hit of a chain on the ray from `a`: a point of the chain or of the box at a positive
parameter, which (under the condition `Good`) is the first hit.  `save F`: save the accumulator
`accA` of a local hit (`save_irs`).
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

/-- **A saved candidate of the first hit** of `C` on the ray from `a` in the direction `σ`. -/
def ResOK (P : Polygon) (C : Chain) (a : Point) (σ : ℝ) (Good : Prop) (F : ℕ) (c : Config) :
    Prop :=
  c.nreg F ≤ 1 ∧
    (c.nreg F = 1 → ∃ τ, 0 < τ ∧ OnCB C (rayPt a σ τ) ∧ c.nreg (F + 1) < (chainModel C).W.n ∧
      ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg (F + 1), c.nreg (F + 2)⟩ ∧
      (chainModel C).pos (Qof P) ⟨c.nreg (F + 1), c.nreg (F + 2)⟩ = rayPt a σ τ ∧
      AbsRec P c (F + 3) (rayPt a σ τ).1 C.radius ∧ (Good → τ = C.hitParam a σ)) ∧
    (Good → c.nreg F = 1)

/-- A saved candidate survives a step keeping its registers. -/
theorem ResOK.transport {C : Chain} {a : Point} {σ : ℝ} {G : Prop} {F : ℕ} {c c' : Config}
    (h : ResOK P C a σ G F c) (hr : ∀ i, i < 7 → c'.nreg (F + i) = c.nreg (F + i)) :
    ResOK P C a σ G F c' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e0 : c'.nreg F = c.nreg F := hr 0 (by norm_num)
  refine ⟨by omega, fun hf => ?_, fun hg => by simp_all⟩
  rw [e0] at hf
  obtain ⟨τ, a1, a2, a3, a4, a5, a6, a7⟩ := h2 hf
  rw [hr 1 (by norm_num), hr 2 (by norm_num)]
  exact ⟨τ, a1, a2, a3, a4, a5, absRec_transport a6 (hr 3 (by norm_num)) (hr 4 (by norm_num))
    (hr 5 (by norm_num)) (hr 6 (by norm_num)), a7⟩

/-- The empty result. -/
def noRes (F : ℕ) : Stmt := .instr (.constN F 0)

/-- **Save the accumulator** into `F … F + 6`. -/
def saveL (F : ℕ) : List Instr :=
  [.copyN F accA, .copyN (F + 1) (accA + 1), .copyN (F + 2) (accA + 2), .copyN (F + 3) (accA + 4),
    .copyN (F + 4) (accA + 5), .copyN (F + 5) (accA + 6), .copyN (F + 6) (accA + 7)]

theorem save_val (m f : ℕ → ℕ) {F : ℕ} (hF : 244000 ≤ F ∧ F + 6 < 250000) :
    regB m (saveL F) f F = f accA ∧ regB m (saveL F) f (F + 1) = f (accA + 1) ∧
    regB m (saveL F) f (F + 2) = f (accA + 2) ∧ regB m (saveL F) f (F + 3) = f (accA + 4) ∧
    regB m (saveL F) f (F + 4) = f (accA + 5) ∧ regB m (saveL F) f (F + 5) = f (accA + 6) ∧
    regB m (saveL F) f (F + 6) = f (accA + 7) ∧
    (∀ q, (q < F ∨ F + 6 < q) → regB m (saveL F) f q = f q) := by
  have eA : accA = 242000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩ <;>
    simp only [saveL, regB, regI, upd, eA] <;>
    grind

/-- **Saving a local hit**: a candidate of the first hit. -/
theorem save_irs (hI : IInv W c₀ c) {F : ℕ} (hF : 244000 ≤ F ∧ F + 6 < 250000) {C : Chain}
    {a : Point} {σ : ℝ} {G : Prop} {L : Set ℝ}
    (hacc : AccOK P accA (fun _ => C) C.radius a σ L c)
    (hL : ∀ τ ∈ L, 0 < τ ∧ OnCB C (rayPt a σ τ))
    (hG : G → FreeAt C a σ ∧ C.hitParam a σ ∈ L) (ha : G → a.2 ≤ C.top.2)
    (hσ : σ = 1 ∨ σ = -1) :
    IRS P W c₀ (block (saveL F)) c 7 (fun c' => ResOK P C a σ G F c' ∧
      (∀ q, (q < F ∨ F + 6 < q) → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hok : okB W c.nmem (saveL F) c.nreg := by
    simp only [saveL, okB, okI]
    ram_grind
  refine (IRS.block _ hI hok).mono (by simp [saveL]) ?_
  rintro c' hc'
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, vo⟩ := save_val c.nmem c.nreg hF
  have e : ∀ q v, regB c.nmem (saveL F) c.nreg q = v → c'.nreg q = v := fun q v h => by
    rw [hc']; exact h
  have hm : c'.nmem = c.nmem := by rw [hc']
  refine ⟨?_, fun q hq => e q _ (vo q hq), hm⟩
  obtain ⟨hf1, hf0, hf⟩ := hacc
  refine ⟨by ram_grind, fun h1 => ?_, fun hg => ?_⟩
  · rw [e _ _ v0] at h1
    obtain ⟨τ, hτ, hmin, -, hpp, hen, hpos, hrec⟩ := hf h1
    obtain ⟨hτ0, hon⟩ := hL τ hτ
    refine ⟨τ, hτ0, hon, by ram_grind, by ram_grind,
      by ram_grind, ?_, fun hg => ?_⟩
    · refine absRec_transport (c := c) hrec (e _ _ v3) ?_ ?_ ?_
      · ram_grind
      all_goals grind
    · obtain ⟨hfree, hmem⟩ := hG hg
      exact lh_min hσ (ha hg) hL hfree hmem hτ hmin
  ram_grind

end

end SweepEv

end Chazelle.Core
