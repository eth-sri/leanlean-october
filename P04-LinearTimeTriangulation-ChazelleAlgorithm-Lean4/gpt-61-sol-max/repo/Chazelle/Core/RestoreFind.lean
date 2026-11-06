module

public import Chazelle.Core.RestoreLink

/-!
# WP-E, part 4: the contract of one splitting step (`FindOK`)

The restoration driver (`RestoreSpec`) works in rounds: in each round, every region of the current
normal form with more than `D` exit chords receives **one** new chord that splits it well
(`Restore.SplitsWell`), found by the procedure specified here (Lemma 3.2 with the arc-cutter and
the ray-shooter, over every ordered pair of arcs of the region).  `FindOK s κ F G H X Ok` is the
contract of such a procedure `s`, for the oracles of costs `F`, `G`, `H` on the context `X`.

Registers (band `bRestore`, from `81000`): `81000` model descriptor, `81001` normal-form handle,
`81002` region index `r`, `81003` the semigranularity `γ` (the oracles' weight bound),
`81004` the context handle, `81005` a degree cap `d` of the normal form, `81006` the target
degree `D`.  Outputs: `81007` a flag, and when it is `1`, `81008 … 81010` a chord triple
`(h, lp, rp)`.

* **soundness**: flag `1` ⇒ the triple is an attached admissible chord record at a vertex height
  of `Q` whose chord splits region `r` well;
* **completeness**: if the augmented full maps have degree `≤ D` (`FullDegLe`) and region `r` has
  more than `D` exit chords, the flag is `1`;
* registers of band `bRestore` below `81000` (the driver's) are preserved;
* cost `κ d · F γ · G γ · (H γ + ⌈log₂ γ⌉ + 1)`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Machine (Stmt)
open Chazelle.Chain (regionsIn)

/-- The region data of a valid normal form for the region correspondence `reg`. -/
def NFRegs (M : Model) (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop :=
  RegionCorr M Q N reg ∧ ChordSidesOK M Q N reg ∧ ArcsOK M Q N reg ∧ RegionsOK M Q N reg

/-- **The contract of a splitting step.** -/
def FindOK (s : Stmt) (κ : ℕ → ℕ) (F G H : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (Bo : Finset ℕ) : Prop :=
  Meets s (restoreBands ∪ Bo)
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem (c.nreg 81004) (c.nreg ALLOC) ∧
      c.nreg 81003 ≤ X.cap P c.nmem (c.nreg 81004) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 81000) ∧
      (c.nmem (c.nreg 81000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 81000 + 1) (Qof P) H C →
        HostRegular (Qof P).n H) ∧
      (c.nmem (c.nreg 81000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 81000 + 1) (Qof P) H C →
        C.P.Simple) ∧
      ∃ M N, ModelDescAt c.nmem (c.nreg 81000) (Qof P) M ∧ GoodModel M ∧ Ok P M ∧
        NFWithin c.nmem (c.nreg 81001) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
        M.DegLe (N.F M (Qof P)) (c.nreg 81005) ∧
        M.Semigranular (N.F M (Qof P)) (c.nreg 81003) ∧ c.nreg 81002 < N.nRegions)
    (fun P c c' => (∀ q, bandOf q = bRestore → q < 81000 → c'.nreg q = c.nreg q) ∧
      c'.nreg 81007 ≤ 1 ∧
      ∀ M N reg, ModelDescAt c.nmem (c.nreg 81000) (Qof P) M → NFAt c.nmem (c.nreg 81001) N →
        IsNF M (Qof P) N → NFRegs M (Qof P) N reg →
        (c'.nreg 81007 = 1 →
          (recOf (c'.nreg 81008, c'.nreg 81009, c'.nreg 81010)).Attached M (Qof P) ∧
          c'.nreg 81008 < (Qof P).n ∧
          (recOf (c'.nreg 81008, c'.nreg 81009, c'.nreg 81010)).toSet M (Qof P) ∈ M.Adm ∧
          SplitsWell M (N.F M (Qof P)) (reg (c.nreg 81002))
            ((recOf (c'.nreg 81008, c'.nreg 81009, c'.nreg 81010)).toSet M (Qof P))) ∧
        (M.FullDegLe (Qof P) (c.nreg 81006) →
          c.nreg 81006 < M.deg (N.F M (Qof P)) (reg (c.nreg 81002)) → c'.nreg 81007 = 1))
    (fun _ c => κ (c.nreg 81005) * F (c.nreg 81003) * G (c.nreg 81003) *
      (H (c.nreg 81003) + Nat.clog 2 (c.nreg 81003) + 1))

/-- **The splitting step exists** for all oracles (the procedure is built from the oracle
statements, like `RestoreSpec`'s), for chain models of `OkModel` and for the interior model of
`Q` (finding E7-B: the down phase restores conformality in the interior model). -/
def FindSpec : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    ∀ Bo : Finset ℕ, oracleBands ⊆ Bo → bRestore ∉ Bo →
    X.CapLocal → X.Halves → (∀ P M, Ok P M → OkModel P M ∨ M = interiorModel (Qof P)) →
    Bs ⊆ Bo → Bc ⊆ Bo →
    ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    FindOK (mk sh cu) κ F G H X Ok Bo

end

end Restore

end Chazelle.Core
