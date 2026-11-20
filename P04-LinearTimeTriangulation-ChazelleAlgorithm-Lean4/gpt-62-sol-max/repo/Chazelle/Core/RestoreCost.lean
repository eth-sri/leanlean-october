module

public import Chazelle.Core.SpecMerge

/-!
# WP-E, part 3: the oracle costs are positive

The cost bound of `RestoreSpec` is a product `… · F γ · G γ · …` of the oracle costs.  A
procedure has to run at least one instruction, so the bound is only usable once `1 ≤ F γ` and
`1 ≤ G γ` are known.  Both follow from the oracle interfaces themselves, as soon as their
preconditions can be met:

* `exec_zero`: an execution of cost `0` changes nothing;
* `cutter_cost_pos`: the arc-cutter returns at least one piece and at most `G γ`, so
  `1 ≤ G γ`;
* `shooter_cost_pos`: if `F γ = 0`, the shooter would run in `0` steps, so its hit flag would be
  the one it was given; given `1` it must report a first hit, given `0` it must report no hit, on
  the same ray — a contradiction.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Machine (Stmt Exec)

/-- **An execution of cost `0` changes nothing.** -/
theorem exec_zero {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hk : k = 0) : c' = c := by
  induction h <;> first | rfl | omega | simp_all

/-- **The arc-cutter costs at least one step**: from any configuration meeting its
precondition (with room), `1 ≤ G γ`. -/
theorem cutter_cost_pos {cu : Stmt} {B : Finset ℕ} {G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : CutterOK cu B G H X Ok) {P : Polygon} {W : ℕ}
    {c : Config} (hw : WordsBounded W c)
    (hpre : CutterPre X Ok P W c)
    (hroom : c.nreg ALLOC + G (rd c bCut 9) ≤ W) : 1 ≤ G (rd c bCut 9) := by
  obtain ⟨c', k, -, -, hpost, -⟩ := h P W c hw hpre hroom
  obtain ⟨M, hM, -⟩ := hpre.2.2.2.2.2
  obtain ⟨-, -, hq, hq1, -⟩ := hpost M hM
  omega

/-- The configuration `c` with the hit-flag register of the shooter set to `v`. -/
def withFlag (c : Config) (v : ℕ) : Config :=
  { c with nreg := upd c.nreg (bandReg bShoot 10) v }

theorem withFlag_rd (c : Config) (v : ℕ) {i : ℕ} (hi : i ≠ 10) :
    rd (withFlag c v) bShoot i = rd c bShoot i := by
  ram_finish [rd, withFlag, bandReg]

theorem withFlag_flag (c : Config) (v : ℕ) : rd (withFlag c v) bShoot 10 = v := rfl

theorem withFlag_alloc (c : Config) (v : ℕ) : (withFlag c v).nreg ALLOC = c.nreg ALLOC := rfl

theorem withFlag_nmem (c : Config) (v : ℕ) : (withFlag c v).nmem = c.nmem := rfl

theorem withFlag_originIn (c : Config) (v : ℕ) (o : Origin) :
    OriginIn (withFlag c v) (bandReg bShoot 5) o ↔ OriginIn c (bandReg bShoot 5) o := Iff.rfl

theorem withFlag_wb {W : ℕ} {c : Config} (hw : WordsBounded W c) {v : ℕ} (hv : v ≤ W) :
    WordsBounded W (withFlag c v) := by
  refine ⟨fun r => ?_, hw.2⟩
  simp only [withFlag, Machine.upd_apply]
  split_ifs
  · exact hv
  · exact hw.1 r

/-- **The ray-shooter costs at least one step**: from any configuration meeting its
precondition (with room), `1 ≤ F γ`. -/
theorem shooter_cost_pos {sh : Stmt} {B : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (h : ShooterOK sh B F X Ok) {P : Polygon} {W : ℕ}
    {c : Config} (hw : WordsBounded W c)
    (hpre : ShooterPre X Ok P W c)
    (hroom : c.nreg ALLOC + F (rd c bShoot 9) ≤ W) : 1 ≤ F (rd c bShoot 9) := by
  by_contra hF
  have hF0 : F (rd c bShoot 9) = 0 := by omega
  have hW1 : 1 ≤ W := le_trans (by unfold hostWords; omega) hpre.2.1
  -- The flag is not an input. With zero steps both initial flag values would be returned.
  have run (v : ℕ) (hv : v ≤ 1) : ShooterPost P c (withFlag c v) := by
    have hwv := withFlag_wb hw (hv.trans hW1)
    have hvpre : ShooterPre X Ok P W (withFlag c v) := by
      simpa (disch := decide) only [ShooterPre, withFlag_rd, withFlag_alloc, withFlag_nmem,
        withFlag_originIn] using hpre
    have hvroom : (withFlag c v).nreg ALLOC + F (rd (withFlag c v) bShoot 9) ≤ W := by
      simpa (disch := decide) only [withFlag_alloc, withFlag_rd] using hroom
    obtain ⟨c', k, ex, hk, hp, -⟩ := h P W (withFlag c v) hwv hvpre hvroom
    change k ≤ F (rd (withFlag c v) bShoot 9) at hk
    simp (disch := decide) only [withFlag_rd, hF0] at hk
    have e := exec_zero ex (by omega)
    subst c'
    simpa (disch := decide) only [ShooterPost, withFlag_rd, withFlag_nmem, withFlag_originIn]
      using hp
  obtain ⟨-, -, -, -, -, -, M, hM, -, -, -, -, -, -, -, -, o, -, ho, -⟩ := hpre
  obtain ⟨t, ht, -⟩ := (run 1 le_rfl M o hM ho).1 (withFlag_flag c 1)
  exact (run 0 (by omega) M o hM ho).2 (by rw [withFlag_flag]; omega) t ht.1 ht.2.1

end

end Restore

end Chazelle.Core
