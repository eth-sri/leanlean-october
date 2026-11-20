module

meta import Chazelle.Programs.RamEval

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
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem)

theorem FrQ.trans {c₁ c₂ c₃ : Config} (h₁ : FrQ c₁ c₂) (h₂ : FrQ c₂ c₃) : FrQ c₁ c₃ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans (h₁.1 r a b d), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans (h₁.2.2 a ha)⟩

abbrev nob := @Chazelle.Core.SweepIo.not_oracle_sw

/-! ## The blocks -/

theorem cIn_val (m f : ℕ → ℕ) :
    regB m cIn f lsxE = f zP ∧ regB m cIn f lsxH = f zPh ∧
      ∀ q, q ≠ lsxE → q ≠ lsxH → regB m cIn f q = f q := by
  refine ⟨?_, ?_, fun q h1 h2 => ?_⟩
  · rfl
  · rfl
  ram_finish [cIn, regB, regI]

theorem cIn_ok (m f : ℕ → ℕ) : okB W m cIn f := by
  simp only [cIn, reg_check]
  tauto

section

variable (m f : ℕ → ℕ) (hk1 : f K1 = 1)

include m hk1 in
theorem cAddr_val :
    regB m cAddr f kE = m (f (sw 300) + 7 * f lsI) ∧
      regB m cAddr f kH = m (f (sw 300) + 7 * f lsI + 1) ∧
      ∀ q, q ≠ kA → q ≠ kE → q ≠ kH → regB m cAddr f q = f q := by
  have e1 : f 240611 = 1 := hk1
  refine ⟨?_, ?_, fun q h1 h2 h3 => ?_⟩
  · simp only [cAddr, regB, regI, upd, kA, kE, kH, lsI, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1]
    exact congrArg m (by ring)
  · simp only [cAddr, regB, regI, upd, kA, kE, kH, lsI, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1]
    exact congrArg m (by ring)
  · register_keep [cAddr]

include m hk1 in
theorem cAddr_ok (hb : f (sw 300) + 7 * f lsI + 1 ≤ W) :
    okB W m cAddr f := by
  register_block normalized [cAddr]

theorem cSlot_val (m f : ℕ → ℕ) :
    regB m cSlot f kS = f sB + 6 * f lsI ∧ ∀ q, q ≠ kS → regB m cSlot f q = f q := by
  refine ⟨?_, fun q h1 => ?_⟩
  · simp only [cSlot, regB, regI, upd, kS, sB, lsI, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
    try ring
  · register_keep [cSlot]

theorem cSlot_ok (m f : ℕ → ℕ) (hb : f sB + 6 * f lsI ≤ W) : okB W m cSlot f := by
  register_block normalized [cSlot]

include m hk1 in
theorem cRead_val :
    regB m cRead f kF = m (f kS) ∧ regB m cRead f kPe = m (f kS + 1) ∧
      regB m cRead f kPh = m (f kS + 2) ∧
      ∀ q, q ≠ kS → q ≠ kF → q ≠ kPe → q ≠ kPh → regB m cRead f q = f q := by
  have e1 : f 240611 = 1 := hk1
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 => ?_⟩
  · simp only [cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1]
  · simp only [cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1]
  · simp only [cRead, regB, regI, upd, kS, kF, kPe, kPh, K1, sw]
    simp_all
  ram_finish [cRead, List.mem_cons, List.not_mem_nil, or_false, dstI]

include m hk1 in
theorem cRead_ok (hb : f kS + 2 ≤ W) : okB W m cRead f := by
  register_block normalized [cRead]

end

/-! ## The direction -/

theorem cDir_irs (hI : IInv W c₀ c) (hK : Consts c) (hb : c.nreg kS + 3 ≤ W) :
    IRS P W c₀ cDir c 5 (fun c' => c'.nreg kS = c.nreg kS + 3 * qS (c.nreg qD) ∧
      (∀ q, q ≠ kS → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have k1 := hK.2.1
  have k3 := hK.2.2.2.2.2.2
  unfold cDir
  by_cases h0 : c.nreg qD < c.nreg K1
  · refine (IRS.ifT h0 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩)).mono (by norm_num)
      (fun _ h => h)
    simp_all [qS] 
  · refine (IRS.ifF h0 ?_).mono (K := 3 + 2) (by norm_num) (fun _ h => h)
    by_cases h1 : c.nreg K1 < c.nreg qD
    · refine (IRS.ifT h1 (IRS.skip (K := 0) hI ⟨?_, fun _ _ => rfl, rfl⟩)).mono (by norm_num)
        (fun _ h => h)
      simp_all [qS] <;> omega
    · refine (IRS.ifF h1 (IRS.instr1 (i := .addN kS kS K3) hI
        ⟨iscr_sw (by decide) (by decide), by rwa [k3]⟩)).mono
        (by norm_num) ?_
      rintro c' rfl
      rw [k1] at h0 h1
      refine ⟨?_, fun q hq => ?_, rfl⟩
      · ram_finish [regI, k3, qS, ite_eq_left]
      ram_finish

end

end S0C

end SweepIo

end Chazelle.Core
