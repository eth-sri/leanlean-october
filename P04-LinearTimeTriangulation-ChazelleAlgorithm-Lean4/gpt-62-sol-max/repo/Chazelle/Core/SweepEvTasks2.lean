module

public import Chazelle.Core.SweepEvTasks

/-!
# The sweep (WP-D), stages 2–3: the top-level split (initialisation, run steps, assembly)

`sweepEvSpec`'s program is `init ; run sh ; fin`:

* `init` (task `InitTask`): from the precondition `SweepEv.Pre` at the entry configuration `c`,
  it sets the fixed registers of the run steps (constants, descriptors, the power table) and
  reaches the configuration `c₀` with the environment `EvEnv`;
* `run sh` (task `RunTask`, stage 3): the run steps (`IRS` from `c₀`): stage 2, the table,
  the event loop; it leaves the stop records at `sB` (count `sC`), the log at `lB` (count `lC`)
  and the endpoint table at `cTB` (`RunOut`);
* `fin`: copies `sB, sC, lB, lC, cTB` to the output registers `sw 200, 201, 300, 301, 302`.

`AsmTask`: `InitTask → RunTask → SweepEvSpec` (the assembly, `Meets`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## The output registers of the run steps and the finalisation -/

/-- The log registers (outputs of the run steps): base and record count. -/
def lB : ℕ := sw 2430
def lC : ℕ := sw 2431

/-- The finalisation block: the outputs to `sw 200, 201, 300, 301, 302`. -/
def finL : List Instr :=
  [.copyN (sw 200) sB, .copyN (sw 201) sC, .copyN (sw 300) lB, .copyN (sw 301) lC,
    .copyN (sw 302) cTB]

/-- The finalisation. -/
def fin : Stmt := block finL

/-- The configuration after the finalisation (only registers change). -/
def finCfg (c : Config) : Config := { c with nreg := regB c.nmem finL c.nreg }

/-- **The post of the run steps** (from `c₀`, the start of the run steps, to `c'`): the outputs
`Out` read at the registers of `finCfg c'`; the three arrays lie at or above the allocator of
`c₀` and below that of `c'`; at most `16 (K₁ + K₂ + 1)` stops and log records. -/
def RunOut (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c₀ c' : Config) : Prop :=
  Out P J N₂ (finCfg c') ∧
    c₀.nreg ALLOC ≤ c'.nreg sB ∧ c'.nreg sB + 5 * c'.nreg sC ≤ c'.nreg ALLOC ∧
    c₀.nreg ALLOC ≤ c'.nreg lB ∧ c'.nreg lB + 7 * c'.nreg lC ≤ c'.nreg ALLOC ∧
    c'.nreg cTB + 3 * (2 * N₂.nChords) ≤ c'.nreg ALLOC ∧
    c'.nreg sC ≤ 16 * (N₁.nChords + N₂.nChords + 1) ∧
    c'.nreg lC ≤ 16 * (N₁.nChords + N₂.nChords + 1)

/-- **The run steps** (stage 3), for every shooter, at cost
`κR D · (K₁ + K₂ + 1) · (F γ + ⌈log₂ (K₁ + K₂ + 1)⌉ + 1)` (`D = c₀.nreg (sw 6)`,
`γ = c₀.nreg (sw 5)`, `K₁ = N₁.nChords`, `K₂ = N₂.nChords`). -/
def RunTask : Prop :=
  ∃ (run : Stmt → Stmt) (κR : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → WordsBounded W c₀ →
      c₀.nreg ALLOC + κR (c₀.nreg (sw 6)) * (N₁.nChords + N₂.nChords + 1) *
          (F (c₀.nreg (sw 5)) + Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 1) ≤ W →
      IRS P W c₀ (run sh) c₀ (κR (c₀.nreg (sw 6)) * (N₁.nChords + N₂.nChords + 1) *
          (F (c₀.nreg (sw 5)) + Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 1))
        (RunOut P J N₁ N₂ c₀)

/-! ## The initialisation -/

/-- The facts of the precondition `Pre` for given `H J N₁ N₂` (the body of its existential). -/
def PreAt (_X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (c : Config) (H : Host)
    (J : Merge.Junction) (N₁ N₂ : NF) : Prop :=
  JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) (Qof P) H J ∧
    J.P.Simple ∧
    Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧
    NFWithin c.nmem (rd c bSweep 3) (c.nreg ALLOC) N₁ ∧
    NFWithin c.nmem (rd c bSweep 4) (c.nreg ALLOC) N₂ ∧
    IsNF (chainModel J.left) (Qof P) N₁ ∧ IsNF (chainModel J.right) (Qof P) N₂ ∧
    (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (rd c bSweep 6) ∧
    (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (rd c bSweep 6) ∧
    (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (rd c bSweep 5) ∧
    (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (rd c bSweep 5) ∧
    St0S P c H J

/-- **Task I: the initialisation**, at cost `κI · (K₁ + K₂ + 1)` (`K₁ = c.nmem (rd c bSweep 3)`,
`K₂ = c.nmem (rd c bSweep 4)`): from `Pre` at `c` it reaches `c₀` with `EvEnv` for every
`H J N₁ N₂` of the precondition, writing only the bands of the sweep and the oracles, keeping the
registers `sw 0 … 199`, with `WordsBounded W c₀`. -/
def InitTask : Prop :=
  ∃ (init : Stmt) (κI : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands → ShooterOK sh Bs F X Ok →
    ∀ (P : Polygon) (W : ℕ) (c : Config), WordsBounded W c → Pre X Ok P W c →
      c.nreg ALLOC + κI * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) ≤ W →
      ∃ c₀ k, Exec P W init c c₀ k ∧ k ≤ κI * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) ∧
        Frame (sweepBands ∪ oracleBands) c c₀ k ∧ WordsBounded W c₀ ∧
        (∀ j, j < 200 → c₀.nreg (sw j) = c.nreg (sw j)) ∧
        ∀ H J N₁ N₂, PreAt X Ok P c H J N₁ N₂ → EvEnv sh Bs F X Ok P W c₀ J N₁ N₂

/-! ## Valid origins (mathematics) -/

/-- **Task O (mathematics): the chord seen from a valid origin.**  For the endpoint query `j` of
`N₂` whose origin `a = endOrigin j` is a point of `C₂` other than the shared vertex and the top
of `C₂`, and whose first hit in `C` comes strictly before its first hit in `C₂` (direction
`σ = endDir j`):

1. the chord `e = shoot J.whole a σ` is not a stop chord (`StopChord2`), and it is attached at a
   position `(p, t)` of the walk of `C` (`p < n`, `0 ≤ t < 1`) whose point is the first hit
   `rayPt a σ (J.whole.hitParam a σ)`, on the `C₁` part strictly beyond the start
   (`Lst < oW (p + t)`), and not the shared vertex;
2. the chord determines the query: two such queries `j, j'` with the same chord are equal. -/
def OriginTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (N : NF), J.P.Simple → IsNF (chainModel J.right) Q N →
    (chainModel J.whole).ChordFamily Q (F₂plus J (N.F (chainModel J.right) Q)) →
    (∀ j, j < 2 * N.nChords → endOrigin J Q N j ∈ J.right.set → endOrigin J Q N j ≠ J.shared →
      endOrigin J Q N j ≠ J.right.top →
      J.whole.hitParam (endOrigin J Q N j) (endDir j) <
        J.right.hitParam (endOrigin J Q N j) (endDir j) →
      ¬ StopChord2 J (N.F (chainModel J.right) Q)
          (Merge.shoot J.whole (endOrigin J Q N j) (endDir j)) ∧
        ∃ (p : ℕ) (t : ℝ), p < (chainModel J.whole).W.n ∧ 0 ≤ t ∧ t < 1 ∧
          SideAttach (chainModel J.whole).W
            (Merge.shoot J.whole (endOrigin J Q N j) (endDir j)) p t ∧
          sidePt (chainModel J.whole).W p t = rayPt (endOrigin J Q N j) (endDir j)
            (J.whole.hitParam (endOrigin J Q N j) (endDir j)) ∧
          (Lst J : ℝ) < oW J (p + t) ∧ sidePt (chainModel J.whole).W p t ≠ J.shared) ∧
    (∀ j j', j < 2 * N.nChords → j' < 2 * N.nChords →
      endOrigin J Q N j ∈ J.right.set → endOrigin J Q N j ≠ J.shared →
      endOrigin J Q N j ≠ J.right.top →
      J.whole.hitParam (endOrigin J Q N j) (endDir j) <
        J.right.hitParam (endOrigin J Q N j) (endDir j) →
      endOrigin J Q N j' ∈ J.right.set → endOrigin J Q N j' ≠ J.shared →
      endOrigin J Q N j' ≠ J.right.top →
      J.whole.hitParam (endOrigin J Q N j') (endDir j') <
        J.right.hitParam (endOrigin J Q N j') (endDir j') →
      Merge.shoot J.whole (endOrigin J Q N j) (endDir j) =
        Merge.shoot J.whole (endOrigin J Q N j') (endDir j') → j = j')

/-! ## The assembly -/

/-- **Task Z: the assembly** of `sweepEvSpec` from the initialisation and the run steps
(program `init ; run sh ; fin`). -/
def AsmTask : Prop := InitTask → RunTask → SweepEvSpec

end

end SweepEv

end Chazelle.Core
