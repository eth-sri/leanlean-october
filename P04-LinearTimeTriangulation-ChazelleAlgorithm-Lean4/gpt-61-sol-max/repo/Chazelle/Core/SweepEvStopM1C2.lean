module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopM1C

/-!
# The sweep (WP-D), stage 2: the candidate of `C₁` of a stop origin, the program

`m1cP br sh`: by the kind of the code,
* shared (`0`): `callArr` in the walk of `C₁` (`CD₁`) from the vertex position `(sw 46, K0)` of the
  shared vertex, then (if an arrival exists) the local hit `lhSave` from it, else no result;
* wall (`1`): the local hit `lhSave` from `(oPE, oPH)` (the box twin in the walk of `C₁`);
* top (`2`): `callSym` of the top of `C₂` (`(6, 0)` in the walk of `C₂`) into `brOS`; if it is
  above the top of `C₁` (`callKb` against `cT1`), no result; else the brute-force shot
  (`BruteTask`, direction `oB`) and the copy of its result into `r1F`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## Registers and programs -/

/-- The scratch of the candidate of `C₁` (`callArr` output, `callKb` output). -/
def m1o : ℕ := sw 4027

/-- The output register of `callSym` (the symbolic point at `brOS = m1s + 1`). -/
def m1s : ℕ := sw 4079

def m1cL0 : List Instr := [.copyN lE (m1o + 1), .copyN lH (m1o + 2), .copyN lD oB]
def m1cL1 : List Instr := [.copyN lE oPE, .copyN lH oPH, .copyN lD oB]
def m1cCp : List Instr :=
  [.copyN r1F brF, .copyN (r1F + 1) (brF + 1), .copyN (r1F + 2) (brF + 2),
    .copyN (r1F + 3) (brF + 3), .copyN (r1F + 4) (brF + 4), .copyN (r1F + 5) (brF + 5),
    .copyN (r1F + 6) (brF + 6)]

/-- The shared code. -/
def m1cK0 (sh : Stmt) : Stmt :=
  .seq (callArr CD₁ (sw 46) K0 oB m1o)
    (.ifLtN K0 m1o (.seq (block m1cL0) (lhSave sh MD₁ CD₁ (sw 3) (sw 33) r1F)) (noRes r1F))

/-- The wall code. -/
def m1cK1 (sh : Stmt) : Stmt := .seq (block m1cL1) (lhSave sh MD₁ CD₁ (sw 3) (sw 33) r1F)

section
variable (br : Stmt → Stmt)
include br
/-- The top code. -/
def m1cK2 (sh : Stmt) : Stmt :=
  .seq (SweepIo.callSym (sw 21) K6 K0 m1s)
    (.seq (callKb cT1 brOS 1 m1o)
      (.ifLtN K0 m1o (noRes r1F) (.seq (block [.copyN brOD oB]) (.seq (br sh) (block m1cCp)))))

/-- **The candidate of `C₁`.** -/
def m1cP (sh : Stmt) : Stmt :=
  .ifLtN oKd K1 (m1cK0 sh) (.ifLtN oKd K2 (m1cK1 sh) (m1cK2 br sh))

/-- The body of `BruteTask`. -/
def StbBody (κ : ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      ∀ s : SymPt, SymPtIn c brOS s → s.Lt P.n → s.eval (Qof P) ∉ J.left.set →
      |(s.eval (Qof P)).1| < J.whole.radius → |(s.eval (Qof P)).2| < J.whole.radius →
      (s.eval (Qof P)).2 ≤ J.left.top.2 → c.nreg brOD ≤ 1 →
      c.nreg ALLOC + κ * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ W →
      IRS P W c₀ (br sh) c (κ * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1))
        (BruteOut P J (s.eval (Qof P)) (dirOf (c.nreg brOD)) c)


end

theorem stbBody_of (h : BruteTask) : ∃ br κ, StbBody br κ := h

/-! ## Small run steps -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **No result.** -/
theorem m1c_noRes {C : Chain} {a : Point} {σ : ℝ} {G : Prop} (hI : IInv W c₀ c) (hng : ¬ G) :
    IRS P W c₀ (noRes r1F) c 1 (fun c' => ResOK P C a σ G r1F c' ∧
      (∀ r, r ≠ r1F → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  refine (IRS.instr1 (i := .constN r1F 0) hI ⟨iscr_sw (by omega_nf)
    (by omega_nf), Nat.zero_le _⟩).mono le_rfl ?_
  rintro c' rfl
  
  have e0 : regI c.nmem (.constN r1F 0) c.nreg r1F = 0 := upd_same _ _ _
  refine ⟨⟨by simp_all,
    fun h => by
      simp_all,
    fun g => absurd g hng⟩, fun r hr => upd_other _ _ _ hr, rfl⟩

section
variable (m f : ℕ → ℕ)
theorem m1cL0_val :
    regB m m1cL0 f lE = f (m1o + 1) ∧ regB m m1cL0 f lH = f (m1o + 2) ∧
      regB m m1cL0 f lD = f oB ∧
      (∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB m m1cL0 f q = f q) := by
  simp_all [m1cL0, regB, regI, upd, lE, lH, lD, m1o, oB, sw] <;> omega_nf

theorem m1cL1_val :
    regB m m1cL1 f lE = f oPE ∧ regB m m1cL1 f lH = f oPH ∧ regB m m1cL1 f lD = f oB ∧
      (∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB m m1cL1 f q = f q) := by
  simp_all [m1cL1, regB, regI, upd, lE, lH, lD, oPE, oPH, oB, sw] <;> omega_nf


end

theorem m1cL_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m m1cL0 f ∧ okB W m m1cL1 f := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by omega_nf) (by omega_nf)
  simp only [m1cL0, m1cL1, okB, okI]
  ram_grind

theorem m1cCp_val (m f : ℕ → ℕ) :
    (∀ i, i < 7 → regB m m1cCp f (r1F + i) = f (brF + i)) ∧
      (∀ q, (q < r1F ∨ r1F + 6 < q) → regB m m1cCp f q = f q) := by
  refine ⟨fun i hi => ?_, fun q hq => ?_⟩
  · interval_cases i <;> aesop
  · refine regB_other _ _ _ (fun i hi => ?_)
    simp only [m1cCp, List.mem_cons, List.not_mem_nil, or_false] at hi
    core_grind

theorem m1cCp_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m m1cCp f := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by omega_nf) (by omega_nf)
  simp only [m1cCp, okB, okI]
  ram_grind

section
variable (J : Merge.Junction) (Q : Polygon) (N : NF) (k b : ℕ)
theorem stOrig_zero :
    stOrig J Q N 0 k b = J.shared := by aesop

theorem stOrig_two :
    stOrig J Q N 2 k b = J.right.top := by aesop


end

end

end SweepEv

end Chazelle.Core
