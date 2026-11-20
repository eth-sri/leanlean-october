module

public import Chazelle.Core.SpecMerge

/-!
# `SweepSpecH`: the sweep with height-coded queries

`SweepSpec` (`SpecMerge.lean`) with one more precondition: the height code of every query names
the height of its point (`FuseAsmHt.HeightOK`, which the fusion proves for every query it issues).
Without it a query on a horizontal edge of a host chain could carry a code of another height, and
the sweep would have to normalise it.  The fusion (`FuseAsm.fuseSpec_of`) uses `SweepSpecH`.
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Machine (Stmt)

/-- **WP-D: the sweep, with height-coded queries** (`SweepSpec` plus the query height condition). -/
def SweepSpecH : Prop :=
  ∃ (mk : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ)
    (X : MemCtx) (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands →
    ShooterOK sh Bs F X Ok →
    Meets (mk sh) (sweepBands ∪ oracleBands)
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem (rd c bSweep 10) (c.nreg ALLOC) ∧
        rd c bSweep 5 ≤ X.cap P c.nmem (rd c bSweep 10) ∧ rd c bSweep 7 ≤ 1 ∧
        JunctionWF P (c.nreg ALLOC) c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) ∧
        ∃ H J N₁ N₂ L, JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2)
            (Qof P) H J ∧
          J.P.Simple ∧
          Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧
          NFWithin c.nmem (rd c bSweep 3) (c.nreg ALLOC) N₁ ∧
          NFWithin c.nmem (rd c bSweep 4) (c.nreg ALLOC) N₂ ∧
          IsNF (chainModel J.left) (Qof P) N₁ ∧ IsNF (chainModel J.right) (Qof P) N₂ ∧
          (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (rd c bSweep 6) ∧
          (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (rd c bSweep 6) ∧
          (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (rd c bSweep 5) ∧
          (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (rd c bSweep 5) ∧
          rd c bSweep 9 = L.length ∧ rd c bSweep 8 + 3 * L.length ≤ c.nreg ALLOC ∧
          ChordListAt c.nmem (rd c bSweep 8) L ∧
          (∀ q ∈ L, QueryOK J (Qof P) (rd c bSweep 7) q) ∧
          (rd c bSweep 7 = 1 → ∃ L₁ : List (ℕ × ℕ × ℕ), L = sweepEndQ N₂.chords ++ L₁ ∧
            L₁.length ≤ 3) ∧
          ∀ q ∈ L, ((chainModel (sideChain J (rd c bSweep 7))).pos (Qof P) ⟨q.1, q.2.1⟩).2 =
            ((Qof P).vtx (q.2.1 - 1)).2)
      (fun P c c' => ∀ H J (L : List (ℕ × ℕ × ℕ)),
        JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) (Qof P) H J →
        rd c bSweep 9 = L.length → ChordListAt c.nmem (rd c bSweep 8) L →
        ∃ R : List (ℕ × ℕ × ℕ × ℕ), c.nreg ALLOC ≤ rd c' bSweep 11 ∧
          rd c' bSweep 11 + 4 * L.length ≤ c'.nreg ALLOC ∧ R.length = L.length ∧
          ResultListAt c'.nmem (rd c' bSweep 11) R ∧
          ∀ j, j < L.length →
            SeesInWhole J (Qof P) (rd c bSweep 7) (L.getD j (0, 0, 0)) (R.getD j (0, 0, 0, 0)))
      (fun _ c => κ (rd c bSweep 6) *
        (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + rd c bSweep 9 + 1) *
        (F (rd c bSweep 5) +
          Nat.clog 2 (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + rd c bSweep 9 + 1) + 1))

end

end Chazelle.Core
