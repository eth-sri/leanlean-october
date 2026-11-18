module

public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase driver: the contract of the pieces of a region chain (D4)

In one level, the canonical map of a region chain `C_R = ⟨H.poly Q, 0, #points - 1⟩` (host `H`
of the region, `HostRamSpec`) is merged from *pieces*: sub-chains `⟨H.poly Q, s, m⟩` of the host.
A piece is a **leaf** (kind `1`: its points are the vertices `v_a, …, v_{a+m}` of `Q`, no
wrap-around, `m ≤ 2^μ`; computed by Lemma 4.1 or brute force on `v_a … v_{a+m}`, transported to
the host chain by `dropWalls` and `BoxT.boxTransport_nf`, rebuilt by `BuildNFSpec` and made
canonical by `GranularizeSpec`) or a **connector** (kind `0`: at most `64` edges; the empty map,
`BuildNFSpec` with no chord and `GranularizeSpec`).  **`PieceSpec O`** is the contract of the
procedure computing one piece: its chain descriptor (with top index and orientation bit) and a
`γ`-canonical normal form of degree cap `D` in its chain model.

Registers (band `bDownDrv`, `218000 … 218999` reserved): inputs `218000` the host handle `HB`
(`HostAt`), `218001` the start `s`, `218002` the number of edges `m`, `218003` the kind,
`218004` the start `a` in `Q` (leaves), `218005` the grade bound `μ`, `218006` the degree cap
`D ≥ 4`, `218007` the target granularity `γ`, `218008` the handle of the up-phase data
(`gradeCtx O`); outputs (fresh memory) `218010` the model descriptor `MD` (`m MD = 0`, chain
descriptor at `MD + 1` on the host handle `HB`), `218011` the normal form.
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine

/-- **The contract of one piece (D4).**  For a sub-chain `C = ⟨H.poly Q, s, m⟩` of a well-formed,
regular, simple host `H` (at most `64` items): a model descriptor of `chainModel C` and a
`γ`-canonical normal form of degree cap `D` of it, fresh and robust below the new allocator.
Leaves need `γ ≥ 2 γ'_μ` and the up-phase data with at least `μ` grades; connectors need
`γ ≥ 2 m`.  Cost `κ (lemma41Nat μ + 1)`. -/
def PieceSpec (O : OracleIface) : Prop :=
  ∃ (sp : Stmt) (κ : ℕ), Meets sp drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (c.nreg 218008) (c.nreg ALLOC) ∧
      4 ≤ c.nreg 218006 ∧ 1 ≤ c.nreg 218002 ∧ c.nreg 218003 ≤ 1 ∧
      ∃ H : Host, Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 218000) H) ∧
        c.nreg 218000 + 3 * H.length + 4 ≤ c.nreg ALLOC ∧
        H.length ≤ 64 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly (Qof P)).Simple ∧
        c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts (Qof P).n).length ∧
        (c.nreg 218003 = 1 →
          c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧ c.nreg 218005 ≤ c.nmem (c.nreg 218008) ∧
          c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
          2 * gradeGran (c.nreg 218005) ≤ c.nreg 218007 ∧
          ∀ k, k ≤ c.nreg 218002 →
            (H.pts (Qof P).n).getD (c.nreg 218001 + k) (.vtx 0) = .vtx (c.nreg 218004 + k)) ∧
        (c.nreg 218003 = 0 → c.nreg 218002 ≤ 64 ∧ 2 * c.nreg 218002 ≤ c.nreg 218007))
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 219000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 218010 ∧ c.nreg ALLOC ≤ c'.nreg 218011 ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg 218010) ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem (c.nreg 218000) H → C.P = H.poly (Qof P) →
        C.s = c.nreg 218001 → C.m = c.nreg 218002 →
        Robust (c'.nreg ALLOC) c'.nmem
          (fun m => m (c'.nreg 218010) = 0 ∧
            ChainDescAt m (c'.nreg 218010 + 1) (Qof P) H C ∧
            m (c'.nreg 218010 + 1) = c.nreg 218000) ∧
        ∃ N, NFWithin c'.nmem (c'.nreg 218011) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N (c.nreg 218007) (c.nreg 218006))
    (fun _ c => κ * (lemma41Nat (c.nreg 218005) + 1))

end

end DrvR

end Chazelle.Core
