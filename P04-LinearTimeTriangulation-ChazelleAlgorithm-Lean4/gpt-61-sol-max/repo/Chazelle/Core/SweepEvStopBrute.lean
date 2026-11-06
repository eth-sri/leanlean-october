module

public import Chazelle.Core.SweepEvStopTasks
public import Chazelle.Core.SweepIoBrute
public import Chazelle.Core.SweepEvWinArcs
public import Chazelle.Core.SweepEvInit4

/-!
# The sweep (WP-D), stage 2: the brute-force shot at `N₁` (`BruteTask`)

`stbProg sh`: save `sw 4001 … 4005` (written by `bLoop`) to `sw 3990 … 3994`, copy the symbolic
point `brOS` to `sO` and the direction `brOD` to `qD`, clear the accumulator `accA`; copy the
normalised arcs of `N₁` to fresh memory (`bLoop`); shoot from the symbolic point at all of them in
the model of `C₁` (model descriptor `MD₁`, chain descriptor `CD₁`) and offer the hit to the
accumulator (`symShot`); restore `sw 4001 … 4005` and copy the accumulator (flag, position,
abscissa record) to `brF … brF + 6`.

**`bruteTask : BruteTask`**, cost `κ (K₁ + 1) (F γ + 1)` with `κ = 3 bruteK + 100` (the number of
arcs is at most `3 K₁ + 1`, `arcsTask`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The save area of `sw 4001 … 4005`. -/
def stbSv : ℕ := sw 3990

/-- Save, inputs, clear the accumulator. -/
def stbPre : List Instr :=
  [.copyN stbSv (sw 4001), .copyN (stbSv + 1) (sw 4002), .copyN (stbSv + 2) (sw 4003),
    .copyN (stbSv + 3) (sw 4004), .copyN (stbSv + 4) (sw 4005),
    .copyN sO brOS, .copyN (sO + 1) (brOS + 1), .copyN (sO + 2) (brOS + 2), .copyN qD brOD,
    .constN accA 0]

/-- Restore, outputs. -/
def stbPost : List Instr :=
  [.copyN (sw 4001) stbSv, .copyN (sw 4002) (stbSv + 1), .copyN (sw 4003) (stbSv + 2),
    .copyN (sw 4004) (stbSv + 3), .copyN (sw 4005) (stbSv + 4),
    .copyN brF accA, .copyN (brF + 1) (accA + 1), .copyN (brF + 2) (accA + 2),
    .copyN (brF + 3) (accA + 4), .copyN (brF + 4) (accA + 5), .copyN (brF + 5) (accA + 6),
    .copyN (brF + 6) (accA + 7)]

/-- **The brute-force shot of stage 2.** -/
def stbProg (sh : Stmt) : Stmt :=
  .seq (block stbPre) (.seq bLoop (.seq (symShot sh MD₁ SweepIo.bBase SweepIo.bN CD₁ K0) (block stbPost)))

/-- The cost constant. -/
def stbK : ℕ := 3 * bruteK + 100

/-- The registers written by `stbPre`. -/
def StbPreW (q : ℕ) : Prop :=
  (sw 3990 ≤ q ∧ q ≤ sw 3994) ∨ (sw 3231 ≤ q ∧ q ≤ sw 3233) ∨ q = qD ∨ q = accA

theorem stbPre_val (m f : ℕ → ℕ) :
    (∀ i, i < 5 → regB m stbPre f (stbSv + i) = f (sw 4001 + i)) ∧
    regB m stbPre f sO = f brOS ∧ regB m stbPre f (sO + 1) = f (brOS + 1) ∧
    regB m stbPre f (sO + 2) = f (brOS + 2) ∧ regB m stbPre f qD = f brOD ∧
    regB m stbPre f accA = 0 ∧
    (∀ q, ¬ StbPreW q → regB m stbPre f q = f q) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · interval_cases i <;> simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  · simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  · simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  · simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  · simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  · simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  refine regB_other _ _ _ (fun i hi => ?_)
  simp only [stbPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  unfold StbPreW at hq
  simp only [qD, accA, sw] at hq
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dstI, stbSv, sO, qD, accA, sw] <;> omega

theorem stbPre_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m stbPre f := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by unfold sw; omega) (by unfold sw; omega)
  simp only [stbPre, okB, okI]
  refine ⟨s 3990 (by norm_num) (by norm_num), s 3991 (by norm_num) (by norm_num),
    s 3992 (by norm_num) (by norm_num), s 3993 (by norm_num) (by norm_num),
    s 3994 (by norm_num) (by norm_num), s 3231 (by norm_num) (by norm_num),
    s 3232 (by norm_num) (by norm_num), s 3233 (by norm_num) (by norm_num),
    s 3212 (by norm_num) (by norm_num), ⟨s 2000 (by norm_num) (by norm_num), Nat.zero_le _⟩,
    trivial⟩

/-- The registers written by `stbPost`. -/
def StbPostW (q : ℕ) : Prop := (sw 4001 ≤ q ∧ q ≤ sw 4005) ∨ (brF ≤ q ∧ q ≤ brF + 6)

theorem stbPost_val (m f : ℕ → ℕ) :
    (∀ i, i < 5 → regB m stbPost f (sw 4001 + i) = f (stbSv + i)) ∧
    regB m stbPost f brF = f accA ∧ regB m stbPost f (brF + 1) = f (accA + 1) ∧
    regB m stbPost f (brF + 2) = f (accA + 2) ∧
    (∀ j, j < 4 → regB m stbPost f (brF + 3 + j) = f (accA + 4 + j)) ∧
    (∀ q, ¬ StbPostW q → regB m stbPost f q = f q) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, fun j hj => ?_, fun q hq => ?_⟩
  · interval_cases i <;> simp [stbPost, regB, regI, upd, stbSv, accA, brF, sw]
  · simp [stbPost, regB, regI, upd, stbSv, accA, brF, sw]
  · simp [stbPost, regB, regI, upd, stbSv, accA, brF, sw]
  · simp [stbPost, regB, regI, upd, stbSv, accA, brF, sw]
  · interval_cases j <;> simp [stbPost, regB, regI, upd, stbSv, accA, brF, sw]
  refine regB_other _ _ _ (fun i hi => ?_)
  simp only [stbPost, List.mem_cons, List.not_mem_nil, or_false] at hi
  unfold StbPostW at hq
  simp only [brF, sw] at hq
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dstI, brF, sw] <;> omega

theorem stbPost_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m stbPost f := by
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by unfold sw; omega) (by unfold sw; omega)
  simp only [stbPost, okB, okI]
  refine ⟨s 4001 (by norm_num) (by norm_num), s 4002 (by norm_num) (by norm_num),
    s 4003 (by norm_num) (by norm_num), s 4004 (by norm_num) (by norm_num),
    s 4005 (by norm_num) (by norm_num), s 4084 (by norm_num) (by norm_num),
    s 4085 (by norm_num) (by norm_num), s 4086 (by norm_num) (by norm_num),
    s 4087 (by norm_num) (by norm_num), s 4088 (by norm_num) (by norm_num),
    s 4089 (by norm_num) (by norm_num), s 4090 (by norm_num) (by norm_num), trivial⟩

/-- The cost bound. -/
theorem stb_cost (A K Fg : ℕ) (hA : A ≤ 3 * K + 1) :
    10 + (bLoopK A + (symShotK Fg A + 12)) ≤ stbK * (K + 1) * (Fg + 1) := by
  have h := brute_cost A Fg
  have h2 : bruteK * (A + 1) * (Fg + 1) ≤ bruteK * (3 * (K + 1)) * (Fg + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) le_rfl
  have e : stbK * (K + 1) * (Fg + 1) =
      bruteK * (3 * (K + 1)) * (Fg + 1) + 100 * ((K + 1) * (Fg + 1)) := by
    unfold stbK; ring
  have h3 : 1 ≤ (K + 1) * (Fg + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

end

end SweepEv

end Chazelle.Core
