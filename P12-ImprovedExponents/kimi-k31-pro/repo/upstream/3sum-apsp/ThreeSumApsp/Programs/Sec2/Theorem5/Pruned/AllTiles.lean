module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.SliceFacts

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

namespace TilesLocal

abbrev NB : ℕ := 0
abbrev LL : ℕ := 1
abbrev TT : ℕ := 2
abbrev PEA : ℕ := 3
abbrev ENCB : ℕ := 4
abbrev PST : ℕ := 5
abbrev SC : ℕ := 6
abbrev SV : ℕ := 7
abbrev SP : ℕ := 8
abbrev P10 : ℕ := 9
abbrev CB : ℕ := 10
abbrev CC : ℕ := 11
abbrev PEB : ℕ := 12
abbrev S0 : ℕ := 13
abbrev S1 : ℕ := 14
abbrev RES : ℕ := 15

end TilesLocal

open TilesLocal

/-- One tile: run the pruned recursion if the tile has wanted positions. -/
def runTile : Stmt :=
  .set S0 (M (v PST)) ;; .set S1 (M (v PST +' k 1)) ;;
  .ite (v S0 <' v S1)
    (.call pPruned [v LL, v PEA, v PEB, v SC +' v S0, v S1 -' v S0, v SV +' v S0, v SP, v P10] RES)
    .skip ;;
  .set CC (v CC +' k 1) ;; .set PEB (v PEB +' v TT) ;; .set PST (v PST +' k 1)

/-- The tiles of one row band. -/
def runTilesInner : Stmt := .while (v CC <' v NB) runTile

/-- One row band. -/
def runBand : Stmt :=
  .set CC (k 0) ;; .set PEB (v ENCB) ;; runTilesInner ;; .set CB (v CB +' k 1) ;;
  .set PEA (v PEA +' v TT)

/-- runTiles(nB, L, T, enca, encb, start, sc, sv, sp, p10). -/
def runTilesBody : Stmt := .set CB (k 0) ;; .while (v CB <' v NB) runBand

end Light.Sec2
