module

public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase driver: the contract of the region procedure (D5)

In one level (merge grade `μ`), for each region of the current interior normal form, the host
RAM (`HostRamSpec`) writes the host `H = regHost li n N r`; the **region procedure** then
computes the canonical map of the whole host chain `C = ⟨H.poly Q, 0, #points - 1⟩`:

* the leaf table (`DrvR.plS`, `DownPhaseDrvRPlD`: chunks of at most `C = 2^μ` edges of the
  run-interior vertices, `hostLeaves`, `LeafIn`), the connectors between consecutive leaves (the
  non-empty gaps, at most `64` edges each);
* one piece per leaf and per connector (`PieceSpec O`, registers `218000 … 218999`);
* the merges along the chain order, starting from the first piece (`DrvR.mgStep`,
  `DownPhaseDrvRMgC`: top of the union, descriptor of the union at the allocator, `MergeSpec`);
  every junction is a run-interior vertex of `H` (`DownMath.sharedGeneric_run`), the degree cap
  is `regCap = 130` (`fullDegLe_host`, `hostFullDegSpec`), each merge adds `fuseLoss = 1` to
  the granularity.

The contract is stated for an **abstract host** (at most `20` items, runs of at most `2 C + 1`
points); the level proves these for `regHost` (at most `5` arcs of at most `4` items, arcs of
weight `≤ 2^(μ+1)`).

Registers (band `bDownDrv`, `219000 … 219999` reserved for the region procedure, including the
registers of `plS` and `mgStep`): inputs `219200` the host handle `HB` (`HostAt`), `219201` the
number of host points, `219202` the merge grade `μ`, `219203` `C = 2^μ`, `219204` the target
granularity `γ₀` of the pieces, `219205` the handle of the up-phase data (`gradeCtx O`);
outputs (fresh memory) `219210` the model descriptor `MD` of `chainModel C` (`m MD = 0`, chain
descriptor on `HB` at `MD + 1`), `219211` the normal form, `219212` its granularity
`γ₀ ≤ γ_R ≤ γ₀ + 128`.  Cost `κ (lemma41Nat μ + 1)`.
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine

/-- The degree cap of the region maps (`hostFullDegSpec`: `2 (64 + 1)`). -/
def regCap : ℕ := 130

/-- **The contract of the region procedure (D5).** -/
def RegionSpec (O : OracleIface) : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (c.nreg 219205) (c.nreg ALLOC) ∧
      7 ≤ c.nreg 219202 ∧ c.nreg 219202 ≤ c.nmem (c.nreg 219205) ∧
      c.nreg 219203 = 2 ^ c.nreg 219202 ∧
      2 * gradeGran (c.nreg 219202) ≤ c.nreg 219204 ∧ 128 ≤ c.nreg 219204 ∧
      c.nreg 219204 ≤ 4096 * 2 ^ Cost.ceilBeta (c.nreg 219202) ∧
      c.nreg 219204 + 129 ≤ (gradeCtx O).cap P c.nmem (c.nreg 219205) ∧
      ∃ H : Host, Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 219200) H) ∧
        c.nreg 219200 + 3 * H.length + 1 ≤ c.nreg ALLOC ∧
        H.length ≤ 20 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly (Qof P)).Simple ∧
        c.nreg 219201 = (H.pts (Qof P).n).length ∧ 3 ≤ c.nreg 219201 ∧
        ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * c.nreg 219203)
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      c.nreg 219204 ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ c.nreg 219204 + 128 ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg 219210) ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem (c.nreg 219200) H → C.P = H.poly (Qof P) →
        C.s = 0 → C.m + 1 = C.P.n →
        Robust (c'.nreg ALLOC) c'.nmem
          (fun m => m (c'.nreg 219210) = 0 ∧
            ChainDescAt m (c'.nreg 219210 + 1) (Qof P) H C ∧
            m (c'.nreg 219210 + 1) = c.nreg 219200) ∧
        ∃ N, NFWithin c'.nmem (c'.nreg 219211) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N (c'.nreg 219212) regCap)
    (fun _ c => κ * (lemma41Nat (c.nreg 219202) + 1))

end

end DrvR

end Chazelle.Core
