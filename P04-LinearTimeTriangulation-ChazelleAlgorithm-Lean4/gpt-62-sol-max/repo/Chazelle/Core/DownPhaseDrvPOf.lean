module

public import Chazelle.Core.DownPhaseDrvPMain
public import Chazelle.Core.Lemma41Of
public import Chazelle.Core.ShootCutMain

/-!
# Down-phase pieces (D4): `DrvR.PieceSpec` from the merge and a valid oracle

`pieceSpec_of'`: Lemma 4.1 (`L41.lemma41_of`, from `MergeSpec` and the shooter and cutter of
`ShootCut.shootCutSpec`) gives the contract of the pieces (`pieceSpec_of`).
-/

namespace Chazelle.Core

namespace DrvP

@[expose] public section

/-- **The pieces of a region chain (D4)**, from the merge and a valid oracle interface. -/
theorem pieceSpec_of' {O : OracleIface} (hM : MergeSpec) (hV : O.Valid) : DrvR.PieceSpec O :=
  pieceSpec_of (L41.lemma41_of O hM (ShootCut.shootCutSpec O hV))

end

end DrvP

end Chazelle.Core
