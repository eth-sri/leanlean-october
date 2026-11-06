module

public import Chazelle.Core.RestoreFind
public import Chazelle.Core.RestorePrune
public import Chazelle.Core.RestoreShoot

/-!
# WP-E, Lemma 3.2 part 12: the contract of a candidate test (`TestOK`)

The search of Lemma 3.2 tests candidate walk positions `x` of the host model (a chain model) in a
direction `σ`: is the ray from `x` a chord splitting the region `R` well?  One test

1. checks that the ray starts in `R` (the checks of `RestoreValid`: `valid`),
2. shoots at every arc of `R`, minus the walk edges through the positions of the origin
   (`RestoreHoles`), and keeps the first hit (`hit`), whose arrival position is `far`,
3. counts the exit chords of `R` attached strictly on each side (`CountOK`), and on success
   writes the chord record.

`TestOK s κt F X Ok` is the contract of such a procedure `s` (the oracles `sh` of cost `F` built
in).  Registers of band `bRestore` from `83000`: `83000` model descriptor, `83001` normal form,
`83002` region `r`, `83003` the weight bound `γ`, `83004` the context, `83005`, `83006` the
candidate position `x`, `83007` its height vertex `h` (the vertex of `Q` at the height of `x`),
`83008` the direction bit (`1`: `σ = 1`, otherwise `σ = -1`), `83009` a degree cap `d` of the
normal form.  The model is a chain model of `OkModel` (the candidate point on the chain) or the
interior model of `Q` (finding E7-B: the down phase restores in the interior model); the
candidate is coded canonically (height code `0` at a walk vertex, otherwise a positive
parameter).  Outputs: `83010` the bit `valid`, `83011` the bit `hit`, `83012`, `83013` the
position `far`, `83014` the bit `succ`, `83015 … 83017` the chord triple.

* **soundness** (`succ = 1`): the triple is an attached admissible chord at the height of a
  vertex of `Q`, splitting `R` well;
* **exactness** (`valid = hit = 1`): the ray from `x` starts in `R`, leaves the domain first at the
  point of `far`, and the chord to it is admissible and attached at `x` and at `far`; `succ = 1`
  iff it passes the count test;
* **completeness**: if the region has an exit chord, the ray from `x` leaves `x` into its left
  sector and its chord up to the first exit is an admissible chord outside the family whose open
  part lies in `R`, then `valid = hit = 1`;
* registers of band `bRestore` below `83000` are preserved;
* cost `κt d · (F γ + 1)`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft regionsIn)
open Chazelle.Visibility (rayPt)

/-- **The contract of a candidate test.** -/
def TestOK (s : Stmt) (κt F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (Bo : Finset ℕ) : Prop :=
  Meets s (restoreBands ∪ Bo)
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      X.holds P c.nmem (c.nreg 83004) (c.nreg ALLOC) ∧
      c.nreg 83003 ≤ X.cap P c.nmem (c.nreg 83004) ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 83000) ∧
      (c.nmem (c.nreg 83000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 83000 + 1) (Qof P) H C →
        HostRegular (Qof P).n H) ∧
      (c.nmem (c.nreg 83000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 83000 + 1) (Qof P) H C →
        C.P.Simple) ∧ c.nreg 83008 ≤ 1 ∧
      ∃ M N, ModelDescAt c.nmem (c.nreg 83000) (Qof P) M ∧ GoodModel M ∧ Ok P M ∧
        NFWithin c.nmem (c.nreg 83001) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
        M.DegLe (N.F M (Qof P)) (c.nreg 83009) ∧
        M.Semigranular (N.F M (Qof P)) (c.nreg 83003) ∧ c.nreg 83002 < N.nRegions ∧
        c.nreg 83005 < M.W.n ∧ ProperPos M (Qof P) P.n ⟨c.nreg 83005, c.nreg 83006⟩ ∧
        (c.nreg 83006 = 0 ∨ 0 < M.param (Qof P) ⟨c.nreg 83005, c.nreg 83006⟩) ∧
        (OkModel P M ∨ M = interiorModel (Qof P)) ∧
        (∀ C : Chain, M = chainModel C →
          M.pos (Qof P) ⟨c.nreg 83005, c.nreg 83006⟩ ∈ C.set) ∧
        c.nreg 83007 < P.n ∧
        ((Qof P).vtx (c.nreg 83007)).2 = (M.pos (Qof P) ⟨c.nreg 83005, c.nreg 83006⟩).2)
    (fun P c c' => (∀ q, bandOf q = bRestore → q < 83000 → c'.nreg q = c.nreg q) ∧
      c'.nreg 83010 ≤ 1 ∧ c'.nreg 83011 ≤ 1 ∧ c'.nreg 83014 ≤ 1 ∧
      ∀ M N reg, ModelDescAt c.nmem (c.nreg 83000) (Qof P) M → NFAt c.nmem (c.nreg 83001) N →
        IsNF M (Qof P) N → NFRegs M (Qof P) N reg →
        let x : WPos := ⟨c.nreg 83005, c.nreg 83006⟩
        let z := M.pos (Qof P) x
        let σ := dirOf (c.nreg 83008)
        let R := reg (c.nreg 83002)
        let far : WPos := ⟨c'.nreg 83012, c'.nreg 83013⟩
        let tr := (c'.nreg 83015, c'.nreg 83016, c'.nreg 83017)
        (c'.nreg 83014 = 1 →
          (recOf tr).Attached M (Qof P) ∧ tr.1 < (Qof P).n ∧
          (recOf tr).toSet M (Qof P) ∈ M.Adm ∧
          SplitsWell M (N.F M (Qof P)) R ((recOf tr).toSet M (Qof P))) ∧
        (c'.nreg 83010 = 1 → c'.nreg 83011 = 1 →
          ∃ T > (0 : ℝ), (∀ t, 0 < t → t < T → rayPt z σ t ∈ R) ∧
            M.pos (Qof P) far = rayPt z σ T ∧ far.edge < M.W.n ∧
            ProperPos M (Qof P) P.n far ∧
            chordOf z σ T ∈ M.Adm ∧
            SideAttach M.W (chordOf z σ T) x.edge (M.param (Qof P) x) ∧
            SideAttach M.W (chordOf z σ T) far.edge (M.param (Qof P) far) ∧
            (c'.nreg 83014 = 1 ↔
              CountOK M (N.F M (Qof P)) R (M.key (Qof P) x) (M.key (Qof P) far))) ∧
        (sideLeft M.W x.edge (M.param (Qof P) x) (rayPt z σ 1) →
          (N.region (c.nreg 83002)).chords ≠ [] →
          (∀ T > (0 : ℝ), (∀ t, 0 < t → t < T → rayPt z σ t ∈ M.D) → rayPt z σ T ∉ M.D →
            chordOf z σ T ∈ M.Adm → chordOf z σ T ∉ N.F M (Qof P) →
            chordOf z σ T ∩ M.D ⊆ R → c'.nreg 83010 = 1 ∧ c'.nreg 83011 = 1)))
    (fun _ c => κt (c.nreg 83009) * (F (c.nreg 83003) + 1))

end

end Restore

end Chazelle.Core
