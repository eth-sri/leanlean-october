module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoS0CandQ1

/-!
# The sweep RAM (WP-D), answers: the side-0 stop and table candidates of a query, part 2

The blocks of `candQ` (`cIn`, `cAddr`, `cSlot`, `cRead`), the direction step `cDir`, and the
slot part `cHit` (`hit_irs`): read the slot of the log record found in the query direction and,
if it is flagged, offer its origin (`offerF`, tag `1`, the model of `C₂`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The registers written by the per-query procedure (outside the oracle bands, besides the
allocator). -/
def QSet (r : ℕ) : Prop := (sw 2000 ≤ r ∧ r ≤ sw 2012) ∨ (sw 4000 ≤ r ∧ r ≤ sw 4111)

/-- The frame of the per-query procedure and of its parts. -/
def FrQ (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ QSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

theorem FrQ.trans {c₁ c₂ c₃ : Config} (h₁ : FrQ c₁ c₂) (h₂ : FrQ c₂ c₃) : FrQ c₁ c₃ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans (h₁.1 r a b d), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans (h₁.2.2 a ha)⟩

theorem nob {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r ∉ oracleBands :=
  not_oracle_sw h1 h2

/-! ## The blocks -/

theorem cIn_val (m f : ℕ → ℕ) :
    regB m cIn f lsxE = f zP ∧ regB m cIn f lsxH = f zPh ∧
      ∀ q, q ≠ lsxE → q ≠ lsxH → regB m cIn f q = f q := by
  refine ⟨?_, ?_, fun q h1 h2 => ?_⟩
  · Θ cIn, regB, regI, upd, lsxE, lsxH, zP, zPh, sw
  · Θ cIn, regB, regI, upd, lsxE, lsxH, zP, zPh, sw
  · ϴ cIn, regB, regI
    Ξ upd_other _ _ _ h2, upd_other _ _ _ h1

theorem cIn_ok (m f : ℕ → ℕ) : okB W m cIn f := by
  ϴ cIn, okB, okI
  exact ⟨iscr_sw (⊚ lsxE, sw) (⊚ lsxE, sw),
    iscr_sw (⊚ lsxH, sw) (⊚ lsxH, sw), trivial⟩

theorem cAddr_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) :
    regB m cAddr f kE = m (f (sw 300) + 7 * f lsI) ∧
      regB m cAddr f kH = m (f (sw 300) + 7 * f lsI + 1) ∧
      ∀ q, q ≠ kA → q ≠ kE → q ≠ kH → regB m cAddr f q = f q := by
  have e1 : f 240611 = 1 := hk1
  refine ⟨?_, ?_, fun q h1 h2 h3 => ?_⟩
  · ϴ cAddr, regB, regI, upd, kA, kE, kH, lsI, K1, sw
    ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
    exact congrArg m (⋆)
  · ϴ cAddr, regB, regI, upd, kA, kE, kH, lsI, K1, sw
    ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
    exact congrArg m (⋆)
  · refine regB_other m cAddr f (fun i hi => ?_)
    simp only [cAddr, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro he <;> subst he <;> simp_all

theorem cAddr_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hb : f (sw 300) + 7 * f lsI + 1 ≤ W) :
    okB W m cAddr f := by
  have e1 : f 240611 = 1 := hk1
  have s : IScr kA := iscr_sw (⊚ kA, sw) (⊚ kA, sw)
  have sE : IScr kE := iscr_sw (⊚ kE, sw) (⊚ kE, sw)
  have sH : IScr kH := iscr_sw (⊚ kH, sw) (⊚ kH, sw)
  simp only [kA, kE, kH, sw] at s sE sH
  have hb' : f 240300 + 7 * f 244000 + 1 ≤ W := hb
  ϴ cAddr, okB, okI, regI, upd, kA, kE, kH, lsI, K1, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  refine ⟨s, ⟨s, ⋄⟩, ⟨s, ⋄⟩, ⟨s, ⋄⟩, ⟨s, ⋄⟩, ⟨s, ⋄⟩,
    ⟨s, ⋄⟩, ⟨s, ⋄⟩, sE, ⟨s, ⋄⟩, sH, trivial⟩

theorem cSlot_val (m f : ℕ → ℕ) :
    regB m cSlot f kS = f sB + 6 * f lsI ∧ ∀ q, q ≠ kS → regB m cSlot f q = f q := by
  refine ⟨?_, fun q h1 => ?_⟩
  · ϴ cSlot, regB, regI, upd, kS, sB, lsI, sw
    ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false
    try ring
  · refine regB_other m cSlot f (fun i hi => ?_)
    simp only [cSlot, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro he <;> subst he <;> simp_all

theorem cSlot_ok (m f : ℕ → ℕ) (hb : f sB + 6 * f lsI ≤ W) : okB W m cSlot f := by
  have s : IScr kS := iscr_sw (⊚ kS, sw) (⊚ kS, sw)
  simp only [kS, sw] at s
  have hb' : f 240620 + 6 * f 244000 ≤ W := hb
  ϴ cSlot, okB, okI, regI, upd, kS, sB, lsI, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false
  refine ⟨s, ⟨s, ⋄⟩, ⟨s, ⋄⟩, ⟨s, ⋄⟩, ⟨s, ⋄⟩, ⟨s, ⋄⟩,
    ⟨s, ⋄⟩, trivial⟩

theorem cRead_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) :
    regB m cRead f kF = m (f kS) ∧ regB m cRead f kPe = m (f kS + 1) ∧
      regB m cRead f kPh = m (f kS + 2) ∧
      ∀ q, q ≠ kS → q ≠ kF → q ≠ kPe → q ≠ kPh → regB m cRead f q = f q := by
  have e1 : f 240611 = 1 := hk1
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 => ?_⟩
  · ϴ cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw
    ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  · ϴ cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw
    ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  · ϴ cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw
    ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  · refine regB_other m cRead f (fun i hi => ?_)
    simp only [cRead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro he <;> subst he <;> simp_all

theorem cRead_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hb : f kS + 2 ≤ W) : okB W m cRead f := by
  have e1 : f 240611 = 1 := hk1
  have s : IScr kS := iscr_sw (⊚ kS, sw) (⊚ kS, sw)
  have sF : IScr kF := iscr_sw (⊚ kF, sw) (⊚ kF, sw)
  have sE : IScr kPe := iscr_sw (⊚ kPe, sw) (⊚ kPe, sw)
  have sH : IScr kPh := iscr_sw (⊚ kPh, sw) (⊚ kPh, sw)
  simp only [kS, kF, kPe, kPh, sw] at s sF sE sH
  have hb' : f 244106 + 2 ≤ W := hb
  ϴ cRead, okB, okI, regI, upd, kS, kF, kPe, kPh, K1, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  exact ⟨sF, ⟨s, ⋄⟩, sE, ⟨s, ⋄⟩, sH, trivial⟩

/-! ## The direction -/

theorem cDir_irs (hI : IInv W c₀ c) (hK : Consts c) (hb : c.nreg kS + 3 ≤ W) :
    IRS P W c₀ cDir c 5 (fun c' => c'.nreg kS = c.nreg kS + 3 * qS (c.nreg qD) ∧
      (∀ q, q ≠ kS → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have k1 := hK.2.1
  have k3 := hK.2.2.2.2.2.2
  unfold cDir
  by_cases h0 : c.nreg qD < c.nreg K1
  · refine (IRS.ifT h0 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩)).mono (⊛)
      (fun _ h => h)
    rw [k1] at h0; unfold qS; rw [ite_eq_right (⋄)]; ring
  · refine (IRS.ifF h0 ?_).mono (K := 3 + 2) (⊛) (fun _ h => h)
    by_cases h1 : c.nreg K1 < c.nreg qD
    · refine (IRS.ifT h1 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩)).mono (⊛)
        (fun _ h => h)
      rw [k1] at h1; unfold qS; rw [ite_eq_right (⋄)]; ring
    · refine (IRS.ifF h1 (IRS.instr1 (i := .addN kS kS K3) hI
        ⟨iscr_sw (⊚ kS, sw) (⊚ kS, sw), by rw [k3]; exact hb⟩)).mono
        (⊛) ?_
      rintro c' rfl
      rw [k1] at h0 h1
      refine ⟨?_, fun q hq => ?_, rfl⟩
      · ϴ regI, upd_same, k3
        unfold qS; rw [ite_eq_left (⋄)]
      · simp only [regI]; exact upd_other _ _ _ hq

end

end S0C

end SweepIo

end Chazelle.Core
