module

public import Chazelle.Core.SweepIface
public import Chazelle.Core.SweepRamStage0

/-!
# The sweep (WP-D): the contract of stages 2 and 3 (stops, event log, endpoint table)

`SweepEvSpec` is the contract of the program `mk sh` that runs stages 2 and 3 of the sweep of
`SweepSpec` (finding S-1: one sweep along the `C₁` part of the walk of `C = J.whole`, side `0`),
after stage 0 (`SweepRamStage0.initS`, side `0`) and possibly stage 1 (registers `sw 100 … 199`).
The interfaces are the ones of `SweepIface.lean`.

## Precondition `SweepEv.Pre X Ok P W c`

The facts of the precondition of `SweepSpec` except the query list (good environment,
`hostWords`, the context `X` at `rd 10` with `γ = rd 5 ≤ cap`, `JunctionWF`, and for some
`H J N₁ N₂`: `JunctionAt`, `J.P.Simple`, `Ok` of both chain models, `NFWithin`/`IsNF`/`DegLe`/
`Semigranular` of `N₁` (in `chainModel J.left`, at `rd 3`) and `N₂` (in `chainModel J.right`, at
`rd 4`) with `D = rd 6`, `γ = rd 5`), plus the stage-0 state of side `0` (`St0S`: the facts of
`SweepRam.St0 P c₀ c H J` for `c₀.nreg (sw 7) = 0`, stated without `c₀`; `st0S_of_st0`).

## Postcondition `SweepEv.Post P c c'`

* the registers `sw 0 … 199` are kept (stage 0 and stage 1);
* for every `H J N₂` with `JunctionAt` at `c` (registers `sw 0, 1, 2`), `NFAt` at `rd c 4` and
  `IsNF (chainModel J.right) (Qof P) N₂`, with `Q = Qof P` and `S₂ = N₂.F (chainModel J.right) Q`:
  * **stops**: records `rs` at `rd c' 200` (count `rd c' 201`), `StopRecsAt`, with
    `StopsOK J S₂ (stopsOf J Q N₂ rs)`;
  * **event log**: records `ls` at `rd c' 300` (count `rd c' 301`), `LogRecsAt`, with
    `LogOK J S₂ (logOf J Q N₂ ls)`;
  * **endpoint table**: at `rd c' 302`, `2 · K₂` records of three words
    (`K₂ = N₂.nChords = c.nmem (rd c 4)`), with `TabOK J Q N₂ (tabOf J Q c'.nmem (rd c' 302))`;
* the three arrays are fresh: they lie between the allocator of `c` and the allocator of `c'`;
* word-level facts (`PosW`: every stored position `(e, h)` has `e < n`, is `ProperPos` in
  `chainModel J.whole`, and `h = 0 → 6 ≤ e`; stop codes `kind ≤ 2`, `b ≤ 1`, `kind = 1 → k < K₂`;
  log label counts `≤ 4` with the used labels `< N₂.nRegions`; table flags `≤ 1`, flag `1` with
  `PosW`), and the sizes: at most `16 (K₁ + K₂ + 1)` stops and log records.

## Cost

`κ D · (K₁ + K₂ + 1) · (F γ + ⌈log₂ (K₁ + K₂ + 1)⌉ + 1)` with `K₁ = c.nmem (rd 3)`,
`K₂ = c.nmem (rd 4)` (the chord counts), `D = rd 6`, `γ = rd 5`, as in `SweepSpec`.

Status: the definitions are **stable**.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt)

namespace SweepEv

open SweepRam

/-- **The stage-0 state of side `0`** (`SweepRam.St0` for `c₀.nreg (sw 7) = 0`, without the entry
configuration): the register constants, the descriptors of `C₁` (`sw 20`) and `C₂` (`sw 21`), the
normal forms (`sw 23 = sw 3`, `sw 24 = sw 4`), the constants of the right correspondence
(`sw 40 … 44`) and of the left one (`sw 45 … 49`), the walk lengths (`sw 33 … 35`) and the model
descriptors of `C₁` (`sw 30`) and `C₂` (`sw 31`). -/
def St0S (P : Polygon) (c : Config) (H : Host) (J : Merge.Junction) : Prop :=
  c.nreg (sw 90) = 0 ∧ c.nreg (sw 91) = 1 ∧ c.nreg (sw 92) = 7 ∧ c.nreg (sw 93) = 2 ∧
    JunctionAt c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)) (Qof P) H J ∧
    JunctionWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)) ∧
    ChainDescAt c.nmem (c.nreg (sw 20)) (Qof P) H J.left ∧
    ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 20)) ∧
    ChainDescAt c.nmem (c.nreg (sw 21)) (Qof P) H J.right ∧
    ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 21)) ∧
    c.nreg (sw 23) = c.nreg (sw 3) ∧ c.nreg (sw 24) = c.nreg (sw 4) ∧
    (∀ k, k < 5 → c.nreg (sw (40 + k)) = cstR J k) ∧
    (∀ k, k < 5 → c.nreg (sw (45 + k)) = cstL J k) ∧
    c.nreg (sw 33) = 2 * J.left.m + 7 ∧ c.nreg (sw 34) = 2 * J.right.m + 7 ∧
    c.nreg (sw 35) = 2 * J.whole.m + 7 ∧
    ModelDescAt c.nmem (c.nreg (sw 30)) (Qof P) (chainModel J.left) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 30)) ∧
    ModelDescAt c.nmem (c.nreg (sw 31)) (Qof P) (chainModel J.right) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 31))

/-- `St0` of side `0` gives `St0S`. -/
theorem st0S_of_st0 {P : Polygon} {c₀ c : Config} {H : Host} {J : Merge.Junction}
    (h : St0 P c₀ c H J) (h7 : c₀.nreg (sw 7) = 0) : St0S P c H J := by
  obtain ⟨h90, h91, h92, h93, hlo, -, hJ, hwf, d20, w20, d21, w21, h23, h24, h40, h45, h33, h34,
    h35, d30, w30, d31, w31⟩ := h
  simp [h7, sideChain, ↓reduceIte, Nat.sub_zero, one_ne_zero, Nat.add_zero] at *
  refine ⟨h90, h91, h92, h93, hJ, hwf, d20, w20, d21, w21, ?_, ?_, fun k hk => ?_,
    fun k hk => ?_, h33, h34, h35, d30, w30, d31, w31⟩
  · rw [h23, hlo 3 (by omega)]
  · rw [h24, hlo 4 (by omega)]
  · rw [h40 k hk]; simp [cstLb]
  · rw [h45 k hk]; simp [cstQ]

/-- **The precondition of stages 2 and 3.** -/
def Pre (X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem (rd c bSweep 10) (c.nreg ALLOC) ∧
    rd c bSweep 5 ≤ X.cap P c.nmem (rd c bSweep 10) ∧
    JunctionWF P (c.nreg ALLOC) c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) ∧
    ∃ H J N₁ N₂, JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) (Qof P) H J ∧
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

/-- **Word-level facts of a stored position** `(e, h)` of the walk of `C`: an edge of the walk, a
proper position, and a height code `0` only on the tour (so that `offCmp`, `arrivalPos` and
`absKey` accept it). -/
def PosW (P : Polygon) (J : Merge.Junction) (e h : ℕ) : Prop :=
  e < (chainModel J.whole).W.n ∧ ProperPos (chainModel J.whole) (Qof P) P.n ⟨e, h⟩ ∧
    (h = 0 → 6 ≤ e)

/-- **The outputs of stages 2 and 3** for one junction and normal form `N₂` of `S₂`: the stops,
the event log and the endpoint table, in the memory of `c'` at the bases read in `c'`, with the
word-level facts of the stored positions, codes and labels. -/
def Out (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c' : Config) : Prop :=
  ∃ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)),
    rs.length = rd c' bSweep 201 ∧ Sweep.StopRecsAt c'.nmem (rd c' bSweep 200) rs ∧
    Sweep.StopsOK J (N₂.F (chainModel J.right) (Qof P)) (Sweep.stopsOf J (Qof P) N₂ rs) ∧
    (∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      (r.2.2.1 = 1 → r.2.2.2.1 < N₂.nChords)) ∧
    ls.length = rd c' bSweep 301 ∧ Sweep.LogRecsAt c'.nmem (rd c' bSweep 300) ls ∧
    Sweep.LogOK J (N₂.F (chainModel J.right) (Qof P)) (Sweep.logOf J (Qof P) N₂ ls) ∧
    (∀ r ∈ ls, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 4 ∧
      (0 < r.2.2.1 → r.2.2.2.1 < N₂.nRegions) ∧ (1 < r.2.2.1 → r.2.2.2.2.1 < N₂.nRegions) ∧
      (2 < r.2.2.1 → r.2.2.2.2.2.1 < N₂.nRegions) ∧ (3 < r.2.2.1 → r.2.2.2.2.2.2 < N₂.nRegions)) ∧
    Sweep.TabOK J (Qof P) N₂ (Sweep.tabOf J (Qof P) c'.nmem (rd c' bSweep 302)) ∧
    ∀ j, j < 2 * N₂.nChords → c'.nmem (rd c' bSweep 302 + 3 * j) ≤ 1 ∧
      (c'.nmem (rd c' bSweep 302 + 3 * j) = 1 →
        PosW P J (c'.nmem (rd c' bSweep 302 + 3 * j + 1)) (c'.nmem (rd c' bSweep 302 + 3 * j + 2)))

/-- **The postcondition of stages 2 and 3.** -/
def Post (P : Polygon) (c c' : Config) : Prop :=
  (∀ j, j < 200 → c'.nreg (sw j) = c.nreg (sw j)) ∧
    c.nreg ALLOC ≤ rd c' bSweep 200 ∧
    rd c' bSweep 200 + 5 * rd c' bSweep 201 ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ rd c' bSweep 300 ∧
    rd c' bSweep 300 + 7 * rd c' bSweep 301 ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ rd c' bSweep 302 ∧
    rd c' bSweep 302 + 3 * (2 * c.nmem (rd c bSweep 4)) ≤ c'.nreg ALLOC ∧
    rd c' bSweep 201 ≤ 16 * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) ∧
    rd c' bSweep 301 ≤ 16 * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) ∧
    ∀ H J N₂, JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) (Qof P) H J →
      NFAt c.nmem (rd c bSweep 4) N₂ → IsNF (chainModel J.right) (Qof P) N₂ →
      Out P J N₂ c'

/-- **The cost of stages 2 and 3.** -/
def cost (κ F : ℕ → ℕ) (_P : Polygon) (c : Config) : ℕ :=
  κ (rd c bSweep 6) * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) *
    (F (rd c bSweep 5) + Nat.clog 2 (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) + 1)

end SweepEv

/-- **WP-D, stages 2 and 3 of the sweep** (finding S-1): the stops, the event log with label sets
and the endpoint table of the sweep along the `C₁` part of the walk of `C`, for every shooter. -/
def SweepEvSpec : Prop :=
  ∃ (mk : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ)
    (X : MemCtx) (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands →
    ShooterOK sh Bs F X Ok →
    Meets (mk sh) (sweepBands ∪ oracleBands) (SweepEv.Pre X Ok) SweepEv.Post (SweepEv.cost κ F)

end

end Chazelle.Core
