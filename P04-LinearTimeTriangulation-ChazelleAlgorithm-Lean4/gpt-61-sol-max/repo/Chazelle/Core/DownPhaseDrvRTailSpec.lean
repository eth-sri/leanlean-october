module

public import Chazelle.Core.DownPhaseDrvRLvB
public import Chazelle.Core.DownPhaseMathCount

/-!
# Down-phase driver: the contract of the tail of a level (D12)

One level (`LevelSpec`) is `lvPar ; lvLoop sH sR sX ; sT`: the parameters and the region table
(`DownPhaseDrvRLvA`), the region loop (`DownPhaseDrvRLvB`: host RAM, region procedure, extraction
for every region, the kept triples and buckets of region `r` recorded in the table at `T + 3 r`)
and the **tail** `sT`:

* gather the kept lists `Lx_0, …, Lx_K` of the table into one triple list `L₂` and one bucket
  list (the buckets of `L₂`'s ends, `keyBkt Q N (endPos L₂ q)`), as `SplPre` wants them
  (registers `210020 … 210024`);
* splice `L₂` into `(L, E)` and rebuild (`splice_meets`);
* the restoration rounds (`RoundsSpec`, `d₀ = regCap + 4`, `γ = 2^(⌈βμ⌉+12)`);
* `Inv(μ)`: (I1), (I2) from the rounds, (I3) from `LevelMathSpec` (4), the rounds' factor
  `2^(regCap+4)` and `DownMath.cnt_step` (`level_bound`).

**`LvTailSpec`**: from the region loop's invariant after all `K + 1` regions (`LvInv`, with the
context `LvCtx` of the configuration after `lvPar`) and (I3) at `λ`, the tail establishes
`Inv(μ)`, `μ = nextLvl λ`, for the count `lvCnt = DownMath.cnt (2^(regCap+4)) (1120 (regCap+2))`,
keeps register `210000` (`λ`), writes only `drvBands`, in `κ (K + 1) (lemma41Nat μ + 1)` steps.

Registers: the tail may write the band-`21` registers `210006 … 210099` (the splice's),
`211100 … 211999` and `216000 … 216999` (the rounds'), and the other `drvBands` (through its
components).
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine

/-- **The count bound of the levels**: `A = 2^(regCap+4)` (the restoration rounds),
`B = 1120 (regCap + 2)` (`LevelMathSpec` (4)). -/
def lvCnt : ℕ → ℕ := DownMath.cnt (2 ^ (regCap + 4)) (1120 * (regCap + 2))

/-- **The contract of the tail of a level (D12).** -/
def LvTailSpec (O : OracleIface) : Prop :=
  ∃ (sT : Stmt) (κ : ℕ), ∀ (Kb : ℕ) (P : Polygon) (W : ℕ) (c₁ c : Config)
    (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point) (lam : ℕ),
    LvCtx O P W c₁ L E reg lam →
    L.length * 2 ^ Cost.ceilBeta lam ≤ lvCnt lam * (2 ^ topGrade P.n + 2 ^ Cost.ceilBeta lam) →
    LvInv O P W c₁ L E reg Kb (L.length + 1) c →
    c.nreg ALLOC + κ * (L.length + 1) * (lemma41Nat (nextLvl lam) + 1) ≤ W →
    ∃ c' k, Exec P W sT c c' k ∧ k ≤ κ * (L.length + 1) * (lemma41Nat (nextLvl lam) + 1) ∧
      Frame drvBands c c' k ∧ c'.nreg 210000 = lam ∧ InvAt lvCnt P c' (nextLvl lam)

end

end DrvR

end Chazelle.Core
