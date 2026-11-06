module

public import Chazelle.Core.SweepEvTasks4
public import Chazelle.Core.SweepEvOrigin
public import Chazelle.Core.SweepEvCount
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics

/-!
# The sweep (WP-D), stage 3: the last iteration (task L2, `DoneTask`)

When the next-key step finds no candidate (`dF = 1`), the outputs are those of the invariant at
the start of the iteration:

* the stops (`StopData`) and the log (`LoopInv.log`) are unchanged in memory;
* the log is complete (`LogOK`) given that no cut of `F₂⁺` lies after the last key (`hnc`);
* the table (`TabOK`): a slot is the one of the invariant (`TabInv`) or an accepted triple of the
  batch (`BatchA`); a valid query without an entry has its first hit in `C` on `C₂`, since a hit
  on the `C₁` part (`originTask`) is either at an offset `≤` the key (flag by `TabInv`) or a cut
  after the last key;
* the log size from the measure and `countTask`.

`done_out`: the outputs, from `EvEnv`, `LoopInv`, `IterRel`, `dF = 1`, the chord family of `F₂⁺`
and the absence of cuts after the last key.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The output registers of the finalisation. -/
theorem fin_rd (c : Config) : rd (finCfg c) bSweep 200 = c.nreg sB ∧
    rd (finCfg c) bSweep 201 = c.nreg sC ∧ rd (finCfg c) bSweep 300 = c.nreg lB ∧
    rd (finCfg c) bSweep 301 = c.nreg lC ∧ rd (finCfg c) bSweep 302 = c.nreg cTB ∧
    (finCfg c).nmem = c.nmem := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp [rd, finCfg, finL, SweepIo.regB, SweepIo.regI, bandReg, bSweep, SweepRam.sw, sB, sC, lB,
      lC, cTB]

section done

variable {P : Polygon} {J : Merge.Junction} {N₁ N₂ : NF} {c₀ c cw cs co c' : Config}

/-- **The registers kept by the iteration** (window, reset, batch; the next key in its
no-candidate case is handled by the caller). -/
theorem done_iter_keep (hIt : IterRel P J N₁ N₂ c cw cs co c') {r : ℕ} (hr : 240000 ≤ r ∧ r < 250000)
    (hW : ¬ WR r) (hb : r ≠ bF ∧ r ≠ bN) (hO : ¬ OrgR r) (hL : ¬ LR r) :
    co.nreg r = c.nreg r := by
  obtain ⟨⟨rs, -, -, -, -, -, -, -, -, -, -, hWr⟩, -, ⟨-, -, -, hRr⟩, ⟨hBr, -, -⟩, -⟩ := hIt
  have hA : r ≠ ALLOC := by ufo ALLOC
  rw [hBr r (band_sw_not hr) hO hL hA, hRr r hb.1 hb.2, hWr r (band_sw_not hr) hW hA]

/-- **The memory kept by the iteration**, below the allocator of `c` and outside the table. -/
theorem done_iter_mem (hIt : IterRel P J N₁ N₂ c cw cs co c')
    (hT : c.nreg cTB = c₀.nreg cTB) (hT' : cs.nreg cTB = c₀.nreg cTB) {x : ℕ}
    (hx : x < c.nreg ALLOC) (hxT : x < c.nreg cTB ∨ c.nreg cTB + 6 * N₂.nChords ≤ x) :
    co.nmem x = c.nmem x := by
  obtain ⟨⟨rs, -, -, -, -, -, -, -, -, -, hWm, hWr⟩, hAw, ⟨hRm, -, -, hRr⟩, ⟨-, -, A, hB⟩, -⟩ :=
    hIt
  have hAs : cs.nreg ALLOC = cw.nreg ALLOC := hRr ALLOC (by ufo ALLOC bF sw)
    (by ufo ALLOC bN sw)
  rw [hB.memT x (by omega) (by rwx [hT', ← hT]), hRm, hWm x hx]

end done

end

end SweepEv

end Chazelle.Core
