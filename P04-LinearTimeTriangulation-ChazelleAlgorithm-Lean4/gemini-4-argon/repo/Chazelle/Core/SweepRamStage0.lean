module

public import Chazelle.Core.SweepRamInit
public import Chazelle.Core.SweepPrimJun

/-!
# The sweep RAM (WP-D), part 4: the program of stage 0

`initS` (design-merge-v2 §9.8, stage 0) runs on entry of the sweep:

1. `init0`: the constants `sw 90 = 0`, `sw 91 = 1`, `sw 92 = 7`, `sw 93 = 2` and the three
   junction descriptors into the input slots `50200 … 50202` of `junConst`;
2. `junConst`: the ten constants of the two correspondences into `50210 … 50219`;
3. `initSide`: for the side `i = sw 7`, the descriptors of the **query chain** `sideChain J i`
   (`sw 20`) and of the **label chain** `sideChain J (1 - i)` (`sw 21`), their normal forms
   (`sw 23`, `sw 24`), the constants of the label correspondence (`sw 40 … 44`) and of the query
   correspondence (`sw 45 … 49`);
4. `nBlk`: the walk lengths `2 m + 7` of the query model, the label model and the model of `C`
   (`sw 33`, `sw 34`, `sw 35`);
5. `mdBlk`: model descriptors of the query model and of the label model in fresh memory (`sw 30`,
   `sw 31`, twelve words), which the shooter takes.

`initS_exec`: the state `St0` after stage 0, in at most `200` steps, with the frame of the bands
`bSweep` and `bLocate`.  The precondition includes `2 · J.whole.m + 7 ≤ W` (the walk length of
`C` is a word); see the report of round 19 on `hostWords`.
-/

namespace Chazelle.Core

namespace SweepRam

open Machine Machine.Stmt Programs SignK SweepPrim
open ShotList (hostAt_agree chainDescAt_copy chainWF_copy)

@[expose] public section

/-! ## The constants of the correspondences -/

/-- The five constants of the right correspondence (`g, g', L1, L2, δ`). -/
noncomputable def cstR (J : Merge.Junction) (k : ℕ) : ℕ :=
  [6 + WalkEmbed.tpos J.whole J.m₁, 6 + WalkEmbed.tpos J.right 0, Sweep.rL1 J, Sweep.rL2 J,
    Sweep.rδ J].getD k 0

/-- The five constants of the left correspondence. -/
noncomputable def cstL (J : Merge.Junction) (k : ℕ) : ℕ :=
  [6 + WalkEmbed.tpos J.whole (J.m₁ + 2 * J.m₂), 6 + WalkEmbed.tpos J.left J.m₁, Sweep.lL1 J,
    Sweep.lL2 J, Sweep.lδ J].getD k 0

/-- The constants of the correspondence of the label chain of side `i`. -/
noncomputable def cstLb (J : Merge.Junction) (i k : ℕ) : ℕ := if i = 0 then cstR J k else cstL J k

/-- The constants of the correspondence of the query chain of side `i`. -/
noncomputable def cstQ (J : Merge.Junction) (i k : ℕ) : ℕ := if i = 0 then cstL J k else cstR J k

/-! ## The blocks -/

/-- The register constants and the inputs of `junConst`. -/
def init0 : Stmt := block [.constN (sw 90) 0, .constN (sw 91) 1, .constN (sw 92) 7,
  .constN (sw 93) 2, .copyN 50200 (sw 0), .copyN 50201 (sw 1), .copyN 50202 (sw 2)]

/-- Side `0`: query chain `C₁`, label chain `C₂`. -/
def sideT : Stmt := block [.copyN (sw 20) (sw 0), .copyN (sw 21) (sw 1), .copyN (sw 23) (sw 3),
  .copyN (sw 24) (sw 4), .copyN (sw 40) 50210, .copyN (sw 41) 50211, .copyN (sw 42) 50212,
  .copyN (sw 43) 50213, .copyN (sw 44) 50214, .copyN (sw 45) 50215, .copyN (sw 46) 50216,
  .copyN (sw 47) 50217, .copyN (sw 48) 50218, .copyN (sw 49) 50219]

/-- Side `1`: query chain `C₂`, label chain `C₁`. -/
def sideF : Stmt := block [.copyN (sw 20) (sw 1), .copyN (sw 21) (sw 0), .copyN (sw 23) (sw 4),
  .copyN (sw 24) (sw 3), .copyN (sw 40) 50215, .copyN (sw 41) 50216, .copyN (sw 42) 50217,
  .copyN (sw 43) 50218, .copyN (sw 44) 50219, .copyN (sw 45) 50210, .copyN (sw 46) 50211,
  .copyN (sw 47) 50212, .copyN (sw 48) 50213, .copyN (sw 49) 50214]

/-- The side selection. -/
def initSide : Stmt := .ifLtN (sw 7) (sw 91) sideT sideF

/-- The walk lengths `2 m + 7` of the three chain models. -/
def nBlk : Stmt := block [
  .addN (sw 97) (sw 20) (sw 93), .loadN (sw 98) (sw 97), .addN (sw 33) (sw 98) (sw 98),
  .addN (sw 33) (sw 33) (sw 92),
  .addN (sw 97) (sw 21) (sw 93), .loadN (sw 98) (sw 97), .addN (sw 34) (sw 98) (sw 98),
  .addN (sw 34) (sw 34) (sw 92),
  .addN (sw 97) (sw 2) (sw 93), .loadN (sw 98) (sw 97), .addN (sw 35) (sw 98) (sw 98),
  .addN (sw 35) (sw 35) (sw 92)]

/-- Destination pointer at the allocator; the query model descriptor's base. -/
def mdA : Stmt := block [.copyN (sw 96) ALLOC, .copyN (sw 30) ALLOC, .copyN (sw 97) (sw 20)]

/-- The label model descriptor's base. -/
def mdB : Stmt := block [.copyN (sw 31) (sw 96), .copyN (sw 97) (sw 21)]

/-- Move the allocator past the two descriptors. -/
def mdC : Stmt := block [.copyN ALLOC (sw 96)]

/-- The two model descriptors. -/
def mdBlk : Stmt := .seq mdA (.seq copyDesc (.seq mdB (.seq copyDesc mdC)))

/-- **Stage 0.** -/
def initS : Stmt := .seq init0 (.seq junConst (.seq initSide (.seq nBlk mdBlk)))

/-! ## Write sets -/

/-- The registers of the sweep band and the input slots of the primitives. -/
def Bs0 (r : ℕ) : Bool := decide (240000 ≤ r ∧ r < 250000) || decide (50100 ≤ r ∧ r < 50220)

/-- `junConst` writes no register of the sweep band. -/
theorem Bjun_sw (j : ℕ) : Bjun (sw j) = false := by
  unfold sw; simp only [Bjun, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- `init0` writes inside `Bs0`. -/
theorem wr_init0 : wr Bs0 init0 = true := by decide

/-- The registers `init0` writes. -/
def B0 (r : ℕ) : Bool := decide (240090 ≤ r ∧ r < 240094) || decide (50200 ≤ r ∧ r < 50203)

/-- The registers `initSide` writes. -/
def Bside (r : ℕ) : Bool := decide (240020 ≤ r ∧ r < 240050)

/-- The registers `nBlk` writes. -/
def Bn (r : ℕ) : Bool := decide (240033 ≤ r ∧ r < 240036) || decide (240097 ≤ r ∧ r < 240099)

/-- `init0` writes only `B0`. -/
theorem wr_init0' : wr B0 init0 = true := by decide
/-- `initSide` writes only `Bside`. -/
theorem wr_initSide' : wr Bside initSide = true := by decide
/-- `nBlk` writes only `Bn`. -/
theorem wr_nBlk' : wr Bn nBlk = true := by decide
/-- `initSide` writes inside `Bs0`. -/
theorem wr_initSide : wr Bs0 initSide = true := by decide
/-- `nBlk` writes inside `Bs0`. -/
theorem wr_nBlk : wr Bs0 nBlk = true := by decide

/-! ## Execution of the blocks -/

/-- **`init0`**: the register constants and the inputs of `junConst`. -/
theorem init0_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 7 ≤ W) :
    ∃ c' k, Exec P W init0 c c' k ∧ k = 7 ∧
      c'.nreg (sw 90) = 0 ∧ c'.nreg (sw 91) = 1 ∧ c'.nreg (sw 92) = 7 ∧ c'.nreg (sw 93) = 2 ∧
      c'.nreg 50200 = c.nreg (sw 0) ∧ c'.nreg 50201 = c.nreg (sw 1) ∧
      c'.nreg 50202 = c.nreg (sw 2) := by
  unfold init0
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  all_goals try omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp

/-- **Side `0`** of the side selection. -/
theorem sideT_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W sideT c c' k ∧ k = 14 ∧
      c'.nreg (sw 20) = c.nreg (sw 0) ∧ c'.nreg (sw 21) = c.nreg (sw 1) ∧
      c'.nreg (sw 23) = c.nreg (sw 3) ∧ c'.nreg (sw 24) = c.nreg (sw 4) ∧
      c'.nreg (sw 40) = c.nreg 50210 ∧ c'.nreg (sw 41) = c.nreg 50211 ∧
      c'.nreg (sw 42) = c.nreg 50212 ∧ c'.nreg (sw 43) = c.nreg 50213 ∧
      c'.nreg (sw 44) = c.nreg 50214 ∧ c'.nreg (sw 45) = c.nreg 50215 ∧
      c'.nreg (sw 46) = c.nreg 50216 ∧ c'.nreg (sw 47) = c.nreg 50217 ∧
      c'.nreg (sw 48) = c.nreg 50218 ∧ c'.nreg (sw 49) = c.nreg 50219 := by
  unfold sideT
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp

/-- **Side `1`** of the side selection. -/
theorem sideF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W sideF c c' k ∧ k = 14 ∧
      c'.nreg (sw 20) = c.nreg (sw 1) ∧ c'.nreg (sw 21) = c.nreg (sw 0) ∧
      c'.nreg (sw 23) = c.nreg (sw 4) ∧ c'.nreg (sw 24) = c.nreg (sw 3) ∧
      c'.nreg (sw 40) = c.nreg 50215 ∧ c'.nreg (sw 41) = c.nreg 50216 ∧
      c'.nreg (sw 42) = c.nreg 50217 ∧ c'.nreg (sw 43) = c.nreg 50218 ∧
      c'.nreg (sw 44) = c.nreg 50219 ∧ c'.nreg (sw 45) = c.nreg 50210 ∧
      c'.nreg (sw 46) = c.nreg 50211 ∧ c'.nreg (sw 47) = c.nreg 50212 ∧
      c'.nreg (sw 48) = c.nreg 50213 ∧ c'.nreg (sw 49) = c.nreg 50214 := by
  unfold sideF
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp

/-- **The side selection**: query chain descriptor, label chain descriptor, normal forms and
correspondence constants of the side `i = sw 7`. -/
theorem initSide_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h91 : c.nreg (sw 91) = 1) (hi : c.nreg (sw 7) ≤ 1) :
    ∃ c' k, Exec P W initSide c c' k ∧ k ≤ 16 ∧
      c'.nreg (sw 20) = c.nreg (sw (c.nreg (sw 7))) ∧
      c'.nreg (sw 21) = c.nreg (sw (1 - c.nreg (sw 7))) ∧
      c'.nreg (sw 23) = c.nreg (sw (3 + c.nreg (sw 7))) ∧
      c'.nreg (sw 24) = c.nreg (sw (4 - c.nreg (sw 7))) ∧
      (∀ k, k < 5 → c'.nreg (sw (40 + k)) =
        c.nreg (if c.nreg (sw 7) = 0 then 50210 + k else 50215 + k)) ∧
      (∀ k, k < 5 → c'.nreg (sw (45 + k)) =
        c.nreg (if c.nreg (sw 7) = 0 then 50215 + k else 50210 + k)) := by
  unfold initSide
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with h0 | h1
  · obtain ⟨c', k, ex, hk, a20, a21, a23, a24, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49⟩ :=
      sideT_exec (P := P) c hw
    refine ⟨c', k + 1, .ifLtN_true (by rw [h0, h91]; omega) ex, by omega, ?_, ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_⟩
    · rwa [h0]
    · rwa [h0]
    · rwa [h0]
    · rwa [h0]
    · rw [h0]; simp only [↓reduceIte]; interval_cases k <;> assumption
    · rw [h0]; simp only [↓reduceIte]; interval_cases k <;> assumption
  · obtain ⟨c', k, ex, hk, a20, a21, a23, a24, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49⟩ :=
      sideF_exec (P := P) c hw
    refine ⟨c', k + 2, .ifLtN_false (by rw [h1, h91]; omega) ex, by omega, ?_, ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_⟩
    · rwa [h1]
    · rwa [h1]
    · rwa [h1]
    · rwa [h1]
    · rw [h1]; simp only [one_ne_zero, ↓reduceIte]; interval_cases k <;> assumption
    · rw [h1]; simp only [one_ne_zero, ↓reduceIte]; interval_cases k <;> assumption

/-- **The walk lengths** `2 m + 7` read from the three chain descriptors. -/
theorem nBlk_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h92 : c.nreg (sw 92) = 7) (h93 : c.nreg (sw 93) = 2)
    (a20 : c.nreg (sw 20) + 2 ≤ W) (a21 : c.nreg (sw 21) + 2 ≤ W) (a2 : c.nreg (sw 2) + 2 ≤ W)
    (m20 : 2 * c.nmem (c.nreg (sw 20) + 2) + 7 ≤ W) (m21 : 2 * c.nmem (c.nreg (sw 21) + 2) + 7 ≤ W)
    (m2 : 2 * c.nmem (c.nreg (sw 2) + 2) + 7 ≤ W) :
    ∃ c' k, Exec P W nBlk c c' k ∧ k = 12 ∧
      c'.nreg (sw 33) = 2 * c.nmem (c.nreg (sw 20) + 2) + 7 ∧
      c'.nreg (sw 34) = 2 * c.nmem (c.nreg (sw 21) + 2) + 7 ∧
      c'.nreg (sw 35) = 2 * c.nmem (c.nreg (sw 2) + 2) + 7 := by
  unfold nBlk
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  all_goals (config_simp; simp only [h92, h93]; omega)

/-- The first block of `mdBlk`. -/
theorem mdA_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mdA c c' k ∧ k = 3 ∧ c'.nreg (sw 96) = c.nreg ALLOC ∧
      c'.nreg (sw 30) = c.nreg ALLOC ∧ c'.nreg (sw 97) = c.nreg (sw 20) ∧
      (∀ r, r ≠ sw 96 → r ≠ sw 30 → r ≠ sw 97 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdA ALLOC
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  refine ⟨by omega, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp
  · config_simp
  · intro r h1 h2 h3; config_simp; simp [h1, h2, h3]

/-- The second block of `mdBlk`. -/
theorem mdB_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mdB c c' k ∧ k = 2 ∧ c'.nreg (sw 31) = c.nreg (sw 96) ∧
      c'.nreg (sw 97) = c.nreg (sw 21) ∧
      (∀ r, r ≠ sw 31 → r ≠ sw 97 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdB
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  refine ⟨by omega, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp
  · intro r h1 h2; config_simp; simp [h1, h2]

/-- The allocator update of `mdBlk`. -/
theorem mdC_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mdC c c' k ∧ k = 1 ∧ c'.nreg ALLOC = c.nreg (sw 96) ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdC ALLOC
  simp only [sw, Nat.reduceAdd] at *
  exec_block
  refine ⟨by omega, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · intro r h1; config_simp; simp [h1]

/-- **The two model descriptors**: `0` and the query chain descriptor at `A = ALLOC`, `0` and
the label chain descriptor at `A + 6`; the allocator moves to `A + 12`. -/
theorem mdBlk_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h90 : c.nreg (sw 90) = 0) (h91 : c.nreg (sw 91) = 1)
    (s20 : c.nreg (sw 20) + 5 ≤ c.nreg ALLOC) (s21 : c.nreg (sw 21) + 5 ≤ c.nreg ALLOC)
    (hA : c.nreg ALLOC + 12 ≤ W) :
    ∃ c' k, Exec P W mdBlk c c' k ∧ k ≤ 50 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 12 ∧ c'.nreg (sw 30) = c.nreg ALLOC ∧
      c'.nreg (sw 31) = c.nreg ALLOC + 6 ∧
      c'.nmem (c.nreg ALLOC) = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg ALLOC + 1 + j) = c.nmem (c.nreg (sw 20) + j)) ∧
      c'.nmem (c.nreg ALLOC + 6) = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg ALLOC + 6 + 1 + j) = c.nmem (c.nreg (sw 21) + j)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ ALLOC → r ≠ sw 30 → r ≠ sw 31 → r ≠ sw 96 → r ≠ sw 97 → r ≠ sw 98 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A := c.nreg ALLOC with hAd
  have n90 : sw 90 ≠ sw 96 ∧ sw 90 ≠ sw 97 ∧ sw 90 ≠ sw 30 ∧ sw 90 ≠ sw 31 ∧ sw 90 ≠ sw 98 := by
    unfold sw; omega
  have n91 : sw 91 ≠ sw 96 ∧ sw 91 ≠ sw 97 ∧ sw 91 ≠ sw 30 ∧ sw 91 ≠ sw 31 ∧ sw 91 ≠ sw 98 := by
    unfold sw; omega
  obtain ⟨c₁, k₁, e₁, hk₁, a96, a30, a97, ar, am, arr, arm, ao⟩ := mdA_exec (P := P) c hw
  rw [← hAd] at a96 a30
  have b90 : c₁.nreg (sw 90) = 0 := by rw [ar _ n90.1 n90.2.2.1 n90.2.1, h90]
  have b91 : c₁.nreg (sw 91) = 1 := by rw [ar _ n91.1 n91.2.2.1 n91.2.1, h91]
  obtain ⟨c₂, k₂, e₂, hk₂, d96, d0, dv, dlo, dr, drr, drm, dout⟩ :=
    copyDesc_exec (P := P) c₁ e₁.wb_right b90 b91 (by rwa [a96, a97])
      (by rw [a96]; omega)
  have c90 : c₂.nreg (sw 90) = 0 := by rw [dr _ n90.1 n90.2.1 n90.2.2.2.2, b90]
  have c91 : c₂.nreg (sw 91) = 1 := by rw [dr _ n91.1 n91.2.1 n91.2.2.2.2, b91]
  obtain ⟨c₃, k₃, e₃, hk₃, b31, b97, br, bm, brr, brm, bo⟩ := mdB_exec (P := P) c₂ e₂.wb_right
  have g90 : c₃.nreg (sw 90) = 0 := by rw [br _ n90.2.2.2.1 n90.2.1, c90]
  have g91 : c₃.nreg (sw 91) = 1 := by rw [br _ n91.2.2.2.1 n91.2.1, c91]
  have g96 : c₃.nreg (sw 96) = A + 6 := by
    rw [br _ (by unfold sw; omega) (by unfold sw; omega), d96, a96]
  have g97 : c₃.nreg (sw 97) = c.nreg (sw 21) := by
    rw [b97, dr _ (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega),
      ar _ (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega)]
  obtain ⟨c₄, k₄, e₄, hk₄, f96, f0, fv, flo, fr, frr, frm, fout⟩ :=
    copyDesc_exec (P := P) c₃ e₃.wb_right g90 g91 (by rw [g96, g97]; omega) (by rw [g96]; omega)
  obtain ⟨c₅, k₅, e₅, hk₅, hA5, hr5, hm5, hrr5, hrm5, ho5⟩ := mdC_exec (P := P) c₄ e₄.wb_right
  have ex : Exec P W mdBlk c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  -- memory of the final configuration
  have mem : ∀ a, c₅.nmem a = c₄.nmem a := fun a => by rw [hm5]
  have m4 : ∀ a, a < A + 6 → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [flo a (by rwa [g96]), bm]
  have m2 : ∀ a, a < A → c₂.nmem a = c.nmem a := fun a ha => by
    rw [dlo a (by rwa [a96]), am]
  refine ⟨c₅, _, ex, by omega, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_,
    fun a ha => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_⟩
  · rw [hA5, f96, g96]
  · rw [hr5 _ (by unfold sw ALLOC; omega),
      fr _ (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega),
      br _ (by unfold sw; omega) (by unfold sw; omega),
      dr _ (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega), a30]
  · rw [hr5 _ (by unfold sw ALLOC; omega),
      fr _ (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega), b31, d96, a96]
  · rw [mem, m4 _ (by omega), ← a96, d0]
  · rw [mem, m4 _ (by omega), ← a96, dv j hj, a97, am]
  · rw [mem, ← g96, f0]
  · rw [mem, ← g96, fv j hj, g97, bm, dlo _ (by rw [a96]; omega), am]
  · rw [mem, m4 _ (by omega), m2 _ ha]
  · rw [hr5 _ h1, fr _ h4 h5 h6, br _ h3 h5, dr _ h4 h5 h6, ar _ h4 h2 h5]
  · rw [hrr5, frr, brr, drr, arr]
  · rw [hrm5, frm, brm, drm, arm]
  · rw [ho5, fout, bo, dout, ao]

/-! ## The state after stage 0 -/

/-- A chain descriptor below `E` survives a change of the memory at or above `E`. -/
theorem chainDesc_keep {P : Polygon} {m m' : ℕ → ℕ} {bw E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) (hEE : E ≤ E') :
    ChainDescAt m' bw (Qof P) H C ∧ ChainWF P E' m' bw := by
  obtain ⟨hb, hwf'⟩ := hwf
  obtain ⟨-, -, hEb, -⟩ := hwf' H C hC
  have hc : ∀ j, j < 5 → m' (bw + j) = m (bw + j) := fun j hj => he _ (by omega)
  exact ⟨chainDescAt_copy hC hEb he hc, chainWF_copy ⟨hb, hwf'⟩ hC he hc (by omega) hEE⟩

/-- **The state after stage 0** (entry configuration `c₀`, junction `J` on host `H`, side
`i = sw 7`). -/
def St0 (P : Polygon) (c₀ c : Config) (H : Host) (J : Merge.Junction) : Prop :=
  c.nreg (sw 90) = 0 ∧ c.nreg (sw 91) = 1 ∧ c.nreg (sw 92) = 7 ∧ c.nreg (sw 93) = 2 ∧
    (∀ j, j < 20 → c.nreg (sw j) = c₀.nreg (sw j)) ∧
    c.nreg ALLOC = c₀.nreg ALLOC + 12 ∧
    JunctionAt c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)) (Qof P) H J ∧
    JunctionWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)) ∧
    ChainDescAt c.nmem (c.nreg (sw 20)) (Qof P) H (sideChain J (c₀.nreg (sw 7))) ∧
    ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 20)) ∧
    ChainDescAt c.nmem (c.nreg (sw 21)) (Qof P) H (sideChain J (1 - c₀.nreg (sw 7))) ∧
    ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 21)) ∧
    c.nreg (sw 23) = c₀.nreg (sw (3 + c₀.nreg (sw 7))) ∧
    c.nreg (sw 24) = c₀.nreg (sw (4 - c₀.nreg (sw 7))) ∧
    (∀ k, k < 5 → c.nreg (sw (40 + k)) = cstLb J (c₀.nreg (sw 7)) k) ∧
    (∀ k, k < 5 → c.nreg (sw (45 + k)) = cstQ J (c₀.nreg (sw 7)) k) ∧
    c.nreg (sw 33) = 2 * (sideChain J (c₀.nreg (sw 7))).m + 7 ∧
    c.nreg (sw 34) = 2 * (sideChain J (1 - c₀.nreg (sw 7))).m + 7 ∧
    c.nreg (sw 35) = 2 * J.whole.m + 7 ∧
    ModelDescAt c.nmem (c.nreg (sw 30)) (Qof P) (chainModel (sideChain J (c₀.nreg (sw 7)))) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 30)) ∧
    ModelDescAt c.nmem (c.nreg (sw 31)) (Qof P)
      (chainModel (sideChain J (1 - c₀.nreg (sw 7)))) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 31))

/-- The side facts of the entry configuration. -/
theorem side_desc {P : Polygon} {m : ℕ → ℕ} {E b0 b1 b2 : ℕ} {H : Host} {J : Merge.Junction}
    (hJ : JunctionAt m b0 b1 b2 (Qof P) H J) (wl : ChainWF P E m b0) (wr' : ChainWF P E m b1)
    {t : ℕ} (ht : t ≤ 1) :
    ChainDescAt m (if t = 0 then b0 else b1) (Qof P) H (sideChain J t) ∧
      ChainWF P E m (if t = 0 then b0 else b1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
  · simp only [sideChain, ↓reduceIte]; exact ⟨hJ.1, wl⟩
  · simp only [sideChain, one_ne_zero, ↓reduceIte]; exact ⟨hJ.2.1, wr'⟩

/-- A side chain has at most as many edges as the union. -/
theorem sideChain_m_le (J : Merge.Junction) (t : ℕ) : (sideChain J t).m ≤ J.whole.m := by
  unfold sideChain
  split
  · show J.m₁ ≤ J.m₁ + J.m₂; omega
  · show J.m₂ ≤ J.m₁ + J.m₂; omega

/-- Reading the descriptor register of side `t ≤ 1`. -/
theorem sw_side {c : Config} {t : ℕ} (ht : t ≤ 1) :
    c.nreg (sw t) = c.nreg (if t = 0 then sw 0 else sw 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl <;> rfl

/-- `junConst` writes inside `Bs0`. -/
theorem wr_junConst' : wr Bs0 junConst = true := by decide

/-- The correspondence constants selected by the side. -/
theorem cstLb_eq (J : Merge.Junction) {i : ℕ} (hi : i ≤ 1) (m : ℕ → ℕ)
    (h : ∀ k, k < 5 → m (50210 + k) = cstR J k) (h' : ∀ k, k < 5 → m (50215 + k) = cstL J k)
    {k : ℕ} (hk : k < 5) :
    m (if i = 0 then 50210 + k else 50215 + k) = cstLb J i k ∧
      m (if i = 0 then 50215 + k else 50210 + k) = cstQ J i k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · simp only [↓reduceIte, cstLb, cstQ]; exact ⟨h k hk, h' k hk⟩
  · simp only [one_ne_zero, ↓reduceIte, cstLb, cstQ]; exact ⟨h' k hk, h k hk⟩

/-- **Stage 0.** -/
theorem initS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {H : Host}
    {J : Merge.Junction} (hi : c.nreg (sw 7) ≤ 1)
    (hJ : JunctionAt c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)) (Qof P) H J)
    (hwf : JunctionWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)))
    (hWm : 2 * J.whole.m + 7 ≤ W) (hroom : c.nreg ALLOC + 220 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k ≤ 220 ∧ St0 P c c' H J ∧
      Frame {bSweep, bLocate} c c' k := by
  set i := c.nreg (sw 7)
  set A := c.nreg ALLOC
  obtain ⟨wl, wr', ww, hreg⟩ := hwf
  have hl5 := wl.1
  have hr5 := wr'.1
  have hw5 := ww.1
  have nA : ∀ j, sw j ≠ ALLOC := fun j => by unfold sw ALLOC; omega
  have mle := sideChain_m_le J
  have hwm : J.whole.m = J.m₁ + J.m₂ := rfl
  -- 0.1
  obtain ⟨c₁, k₁, e₁, hk₁, u90, u91, u92, u93, u200, u201, u202⟩ :=
    init0_exec (P := P) c hw (by omega)
  have G₁ := exec_frameB e₁ wr_init0'
  have ulo : ∀ j, j < 20 → c₁.nreg (sw j) = c.nreg (sw j) := fun j hj => G₁.1 _ (by
    unfold sw; simp only [B0, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have F₁ := exec_frameB e₁ wr_init0
  have A1 : c₁.nreg ALLOC = A := F₁.1 ALLOC (by unfold ALLOC; decide)
  have M1 : c₁.nmem = c.nmem := F₁.2.2.1
  have hJ1 : JunctionAt c₁.nmem (c₁.nreg 50200) (c₁.nreg 50201) (c₁.nreg 50202) (Qof P) H J := by
    rwa [M1, u200, u201, u202]
  -- 0.2: `junConst`
  obtain ⟨c₂, k₂, e₂, hk₂, p₂, -⟩ := junConst_meets P W c₁ e₁.wb_right
    ⟨by rw [u200]; omega, by rw [u201]; omega, by rw [u202]; omega, H, J, hJ1, hWm⟩
    (by rw [A1]; show A + 120 ≤ W; omega)
  replace hk₂ : k₂ ≤ 120 := hk₂
  obtain ⟨v10, v11, v12, v13, v14, v15, v16, v17, v18, v19⟩ := p₂ H J hJ1
  have J₂ := exec_frameB e₂ wr_junConst
  have F₂ := exec_frameB e₂ wr_junConst'
  have k₂s : ∀ j, c₂.nreg (sw j) = c₁.nreg (sw j) := fun j => J₂.1 _ (Bjun_sw j)
  have A2 : c₂.nreg ALLOC = A := by
    rw [J₂.1 ALLOC (by unfold ALLOC; decide), A1]
  have M2 : c₂.nmem = c.nmem := by rw [J₂.2.2.1, M1]
  have cR : ∀ k, k < 5 → c₂.nreg (50210 + k) = cstR J k := fun k hk => by
    interval_cases k <;> simp only [cstR] <;> assumption
  have cL : ∀ k, k < 5 → c₂.nreg (50215 + k) = cstL J k := fun k hk => by
    interval_cases k <;> simp only [cstL] <;> assumption
  -- 0.3: the side
  have i2 : c₂.nreg (sw 7) = i := by rw [k₂s, ulo _ (by omega)]
  have o91 : c₂.nreg (sw 91) = 1 := by rw [k₂s, u91]
  obtain ⟨c₃, k₃, e₃, hk₃, t20, t21, t23, t24, t40, t45⟩ :=
    initSide_exec (P := P) c₂ e₂.wb_right o91 (by rwa [i2])
  have G₃ := exec_frameB e₃ wr_initSide'
  have tlo : ∀ r, (r < sw 20 ∨ sw 50 ≤ r) → c₃.nreg r = c₂.nreg r := fun r hr => G₃.1 r (by
    unfold sw at hr; simp only [Bside, decide_eq_false_iff_not]; omega)
  rw [i2] at t20 t21 t23 t24 t40 t45
  have F₃ := exec_frameB e₃ wr_initSide
  have A3 : c₃.nreg ALLOC = A := by rw [F₃.1 ALLOC (by unfold ALLOC; decide), A2]
  have M3 : c₃.nmem = c.nmem := by rw [F₃.2.2.1, M2]
  have lo3 : ∀ j, j < 20 → c₃.nreg (sw j) = c.nreg (sw j) := fun j hj => by
    rw [tlo _ (Or.inl (by unfold sw; omega)), k₂s, ulo _ (by omega)]
  have hi1 : 1 - i ≤ 1 := by omega
  obtain ⟨dq, wq⟩ := side_desc hJ wl wr' hi
  obtain ⟨dl, wl'⟩ := side_desc hJ wl wr' hi1
  have q20 : c₃.nreg (sw 20) = if i = 0 then c.nreg (sw 0) else c.nreg (sw 1) := by
    rw [t20, k₂s, ulo _ (by omega), sw_side hi]; split <;> rfl
  have q21 : c₃.nreg (sw 21) = if 1 - i = 0 then c.nreg (sw 0) else c.nreg (sw 1) := by
    rw [t21, k₂s, ulo _ (by omega), sw_side hi1]; split <;> rfl
  -- 0.4: the walk lengths
  have x92 : c₃.nreg (sw 92) = 7 := by
    rw [tlo _ (Or.inr (by unfold sw; omega)), k₂s, u92]
  have x93 : c₃.nreg (sw 93) = 2 := by
    rw [tlo _ (Or.inr (by unfold sw; omega)), k₂s, u93]
  have mq : c.nmem ((if i = 0 then c.nreg (sw 0) else c.nreg (sw 1)) + 2) = (sideChain J i).m :=
    dq.2.2.2.1
  have ml : c.nmem ((if 1 - i = 0 then c.nreg (sw 0) else c.nreg (sw 1)) + 2) =
      (sideChain J (1 - i)).m := dl.2.2.2.1
  have mw : c.nmem (c.nreg (sw 2) + 2) = J.whole.m := hJ.2.2.2.2.2.1
  have bq := wq.1
  have bl := wl'.1
  have mq' := mle i
  have ml' := mle (1 - i)
  obtain ⟨c₄, k₄, e₄, hk₄, n33, n34, n35⟩ := nBlk_exec (P := P) c₃ e₃.wb_right x92 x93
    (by rw [q20]; omega) (by rw [q21]; omega) (by rw [lo3 _ (by omega)]; omega)
    (by rw [M3, q20, mq]; omega) (by rw [M3, q21, ml]; omega)
    (by rw [M3, lo3 _ (by omega), mw]; omega)
  have F₄ := exec_frameB e₄ wr_nBlk
  have G₄ := exec_frameB e₄ wr_nBlk'
  have nlo : ∀ r, r ≠ sw 33 → r ≠ sw 34 → r ≠ sw 35 → r ≠ sw 97 → r ≠ sw 98 →
      c₄.nreg r = c₃.nreg r := fun r h1 h2 h3 h4 h5 => G₄.1 r (by
    unfold sw at h1 h2 h3 h4 h5
    simp only [Bn, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have A4 : c₄.nreg ALLOC = A := by rw [F₄.1 ALLOC (by unfold ALLOC; decide), A3]
  have M4 : c₄.nmem = c.nmem := by rw [F₄.2.2.1, M3]
  have k4 : ∀ j, j ≠ 33 → j ≠ 34 → j ≠ 35 → j ≠ 97 → j ≠ 98 → c₄.nreg (sw j) = c₃.nreg (sw j) :=
    fun j h1 h2 h3 h4 h5 => nlo _ (by unfold sw; omega) (by unfold sw; omega)
      (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega)
  -- 0.5: the model descriptors
  have y90 : c₄.nreg (sw 90) = 0 := by
    rw [k4 _ (by omega) (by omega) (by omega) (by omega) (by omega),
      tlo _ (Or.inr (by unfold sw; omega)), k₂s, u90]
  have y91 : c₄.nreg (sw 91) = 1 := by
    rw [k4 _ (by omega) (by omega) (by omega) (by omega) (by omega),
      tlo _ (Or.inr (by unfold sw; omega)), k₂s, u91]
  have y20 : c₄.nreg (sw 20) = if i = 0 then c.nreg (sw 0) else c.nreg (sw 1) := by
    rw [k4 _ (by omega) (by omega) (by omega) (by omega) (by omega), q20]
  have y21 : c₄.nreg (sw 21) = if 1 - i = 0 then c.nreg (sw 0) else c.nreg (sw 1) := by
    rw [k4 _ (by omega) (by omega) (by omega) (by omega) (by omega), q21]
  obtain ⟨c₅, k₅, e₅, hk₅, zA, z30, z31, z0, zq, z6, zl, zlo, zr, zrr, zrm, zo⟩ :=
    mdBlk_exec (P := P) c₄ e₄.wb_right y90 y91 (by rwa [y20, A4])
      (by rwa [y21, A4]) (by rw [A4]; omega)
  rw [A4] at zA z30 z31 z0 zq z6 zl zlo
  rw [y20, M4] at zq
  rw [y21, M4] at zl
  rw [M4] at zlo
  have k5 : ∀ j, j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 → c₅.nreg (sw j) = c₄.nreg (sw j) :=
    fun j h1 h2 h3 h4 h5 => zr _ (nA j) (by unfold sw; omega) (by unfold sw; omega)
      (by unfold sw; omega) (by unfold sw; omega) (by unfold sw; omega)
  have ex : Exec P W initS c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  -- register reading through stages 0.4 and 0.5
  have r45 : ∀ j, j < 30 ∨ (35 < j ∧ j < 96) → c₅.nreg (sw j) = c₃.nreg (sw j) := fun j hj => by
    rw [k5 _ (by omega) (by omega) (by omega) (by omega) (by omega),
      k4 _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  have lo5 : ∀ j, j < 20 → c₅.nreg (sw j) = c.nreg (sw j) := fun j hj => by
    rw [r45 _ (Or.inl (by omega)), lo3 _ hj]
  -- memory
  have keep := fun {b : ℕ} {C : Chain} (hw' : ChainWF P A c.nmem b)
      (hC : ChainDescAt c.nmem b (Qof P) H C) =>
    chainDesc_keep (m' := c₅.nmem) (E' := A + 12) hw' hC zlo (by omega)
  obtain ⟨j0, w0⟩ := keep wl hJ.1
  obtain ⟨j1, w1⟩ := keep wr' hJ.2.1
  obtain ⟨j2, w2⟩ := keep ww hJ.2.2
  obtain ⟨jq, wq5⟩ := keep wq dq
  obtain ⟨jl, wl5⟩ := keep wl' dl
  obtain ⟨mdq, mwq, -⟩ := modelDesc_of_copy (E' := A + 12) wq dq le_rfl zlo z0
    (fun j hj => zq j hj) (by omega)
  obtain ⟨mdl, mwl, -⟩ := modelDesc_of_copy (A := A + 6) (E' := A + 12) wl' dl (by omega) zlo z6
    (fun j hj => zl j hj) (by omega)
  refine ⟨c₅, _, ex, by omega, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, lo5, zA, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r45 _ (Or.inr (by omega)), tlo _ (Or.inr (by unfold sw; omega)), k₂s, u90]
    · rw [r45 _ (Or.inr (by omega)), tlo _ (Or.inr (by unfold sw; omega)), k₂s, u91]
    · rw [r45 _ (Or.inr (by omega)), x92]
    · rw [r45 _ (Or.inr (by omega)), x93]
    · rw [lo5 0 (by omega), lo5 1 (by omega), lo5 2 (by omega)]; exact ⟨j0, j1, j2⟩
    · rwa [lo5 0 (by omega), zA]
    · rwa [lo5 1 (by omega), zA]
    · rwa [lo5 2 (by omega), zA]
    · intro H' hH'
      rw [lo5 2 (by omega)] at hH'
      have hb : c₅.nmem (c.nreg (sw 2)) = c.nmem (c.nreg (sw 2)) := zlo _ (by omega)
      rw [hb] at hH'
      obtain ⟨-, -, hEb, -⟩ := ww.2 H J.whole hJ.2.2
      have hH : HostAt c₅.nmem (c.nmem (c.nreg (sw 2))) H := hostAt_agree hJ.2.2.1 hEb zlo
      rw [NFLoc.hostAt_unique hH' hH]
      exact hreg H hJ.2.2.1
    · rwa [r45 _ (Or.inl (by omega)), q20]
    · rwa [r45 _ (Or.inl (by omega)), q20, zA]
    · rwa [r45 _ (Or.inl (by omega)), q21]
    · rwa [r45 _ (Or.inl (by omega)), q21, zA]
    · rw [r45 _ (Or.inl (by omega)), t23, k₂s, ulo _ (by omega)]
    · rw [r45 _ (Or.inl (by omega)), t24, k₂s, ulo _ (by omega)]
    · rw [r45 _ (Or.inr (by omega)), t40 k hk]
      exact (cstLb_eq J hi c₂.nreg cR cL hk).1
    · rw [r45 _ (Or.inr (by omega)), t45 k hk]
      exact (cstLb_eq J hi c₂.nreg cR cL hk).2
    · rw [k5 _ (by omega) (by omega) (by omega) (by omega) (by omega), n33, M3, q20, mq]
    · rw [k5 _ (by omega) (by omega) (by omega) (by omega) (by omega), n34, M3, q21, ml]
    · rw [k5 _ (by omega) (by omega) (by omega) (by omega) (by omega), n35, M3,
        lo3 _ (by omega), mw]
    · rwa [z30]
    · rwa [z30, zA]
    · rwa [z31]
    · rwa [z31, zA]
  · -- the frame
    have F4 : FrameB Bs0 c c₄ := F₁.trans (F₂.trans (F₃.trans F₄))
    have hB : ∀ r, bandOf r ∉ ({bSweep, bLocate} : Finset ℕ) → Bs0 r = false := by
      intro r hr
      simp only [bandOf, bSweep, bLocate, Finset.mem_insert, Finset.mem_singleton] at hr
      simp only [Bs0, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hsw : ∀ r j, bandOf r ∉ ({bSweep, bLocate} : Finset ℕ) → j < 10000 → r ≠ sw j := by
      intro r j hr hj h
      apply hr
      rw [h]; unfold sw
      simp only [bandOf, bSweep, bLocate, Finset.mem_insert, Finset.mem_singleton]; omega
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
    · rw [zr r hra (hsw r 30 hr (by omega)) (hsw r 31 hr (by omega)) (hsw r 96 hr (by omega))
        (hsw r 97 hr (by omega)) (hsw r 98 hr (by omega)), F4.1 r (hB r hr)]
    · rw [zrr, F4.2.1 r (hB r hr)]
    · rw [zlo a ha]
    · rw [zrm, F4.2.2.2.1]
    · rw [zo, F4.2.2.2.2]
    · rw [zA]; omega
    · rw [zA]; omega

end

end SweepRam

end Chazelle.Core
