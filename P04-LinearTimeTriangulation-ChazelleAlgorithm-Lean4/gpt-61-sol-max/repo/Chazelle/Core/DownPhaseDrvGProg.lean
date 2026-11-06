module

public import Chazelle.Core.DownPhaseDrvRMgC
public import Chazelle.Core.DownPhaseDrvGPlan

/-!
# Down-phase driver, region procedure (D5), part 3: the program

`rgS sp sM` (`sp` the piece procedure of `PieceSpec`, `sM` the merge of `MergeSpec`):

1. `rgInit0`, `plS`, `rgPad`: the leaf table `hostLeaves n C 0 H` at `r219003` (count `r219004`),
   then a padding loop (the allocation of the table is at most the step count);
2. `rgInit1`: the constants of the merge steps (`MgConst`), the host data of `mgStep`
   (`219100` `HB`, `219101` points, `219103` cap `130`, `219104` context, `219107` items), the loop
   state, and three spare words for the allocator (`HB + 3 |H| + 4 ≤ ALLOC`);
3. `lfLoop`: for each leaf `(s, len, a)`: the connector `[pos, s]` if `pos < s`, the leaf, then
   `pos := s + len`; each piece is computed by `sp` (`pcS`) and merged into the accumulated
   chain `⟨H.poly Q, 0, pos⟩` (`mgStep sM`) or becomes it (the first piece);
4. `finCon`: the last connector `[pos, M]` (`M = #points - 1`) if `pos < M`;
5. `rgOut`: the outputs `219210 … 219212`.

Registers (band `bDownDrv`): inputs `219200 … 219205`, outputs `219210 … 219212`; loop state
`219220` leaf index, `219221` `pos`, `219222` the bit "a piece was computed", `219223` `M`,
`219224` the table pointer, `219226 … 219228` the current leaf, scratch `219229`; constants
`219230 = 1`, `219231 = 3`; the piece arguments `219240 … 219243` (start, edges, kind, `Q`
start); the padding `219250`, `219251`.  `plS` uses `219000 … 219029`, `mgStep` `219100 …
219146`, `PieceSpec` `218000 … 218999`.
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt DrvR

@[expose] public section

/-- The arguments of the leaf planner. -/
def rgInit0 : Stmt := block [.copyN 219000 219200, .copyN 219002 219203]

/-- The padding after the leaf table. -/
def rgPad : Stmt :=
  .seq (block [.copyN 219250 219003, .constN 219251 1])
    (.whileLtN 219250 9999 (block [.addN 219250 219250 219251]))

/-- The constants and the loop state. -/
def rgInit1 : Stmt := block [
  .constN 219140 0, .constN 219141 1, .constN 219142 2, .constN 219143 3, .constN 219144 4,
  .constN 219145 5, .constN 219146 6,
  .copyN 219100 219200, .copyN 219101 219201, .constN 219103 130, .copyN 219104 219205,
  .loadN 219107 219200,
  .constN 219230 1, .constN 219231 3, .constN 219220 0, .constN 219221 0, .constN 219222 0,
  .subN 219223 219201 219230, .copyN 219224 219003, .addN 9999 9999 219231]

/-- The arguments of `PieceSpec`. -/
def pcArgs : Stmt := block [
  .copyN 218000 219200, .copyN 218001 219240, .copyN 218002 219241, .copyN 218003 219242,
  .copyN 218004 219243, .copyN 218005 219202, .constN 218006 130, .copyN 218007 219204,
  .copyN 218008 219205]

/-- The first piece becomes the accumulated chain. -/
def pcFirst : Stmt := block [
  .copyN 219110 218010, .copyN 219111 218011, .copyN 219112 219241, .copyN 219113 219204,
  .constN 219222 1]

/-- A later piece is merged into the accumulated chain. -/
def pcNext (sM : Stmt) : Stmt :=
  .seq (block [.copyN 219114 218010, .copyN 219115 218011, .copyN 219116 219241]) (mgStep sM)

/-- **One piece** (arguments in `219240 … 219243`). -/
def pcS (sp sM : Stmt) : Stmt := .seq pcArgs (.seq sp (.ifLtN 219222 219230 pcFirst (pcNext sM)))

/-- Load the current leaf. -/
def lfLoad : Stmt := block [
  .loadN 219226 219224, .addN 219229 219224 219230, .loadN 219227 219229,
  .addN 219229 219229 219230, .loadN 219228 219229]

/-- The connector before the current leaf (if `pos < s`). -/
def conS (sp sM : Stmt) : Stmt :=
  .ifLtN 219221 219226
    (.seq (block [.copyN 219240 219221, .subN 219241 219226 219221, .constN 219242 0,
      .constN 219243 0]) (pcS sp sM)) .skip

/-- The current leaf. -/
def lfS (sp sM : Stmt) : Stmt :=
  .seq (block [.copyN 219240 219226, .copyN 219241 219227, .constN 219242 1,
    .copyN 219243 219228]) (pcS sp sM)

/-- Advance past the current leaf. -/
def lfAdv : Stmt :=
  block [.addN 219221 219226 219227, .addN 219220 219220 219230, .addN 219224 219224 219231]

section
variable (sp sM : Stmt)
include sp sM
/-- One leaf (and the connector before it). -/
def lfBody : Stmt := .seq lfLoad (.seq (conS sp sM) (.seq (lfS sp sM) lfAdv))

/-- **The leaf loop.** -/
def lfLoop : Stmt := .whileLtN 219220 219004 (lfBody sp sM)

/-- The last connector (if `pos < M`). -/
def finCon : Stmt :=
  .ifLtN 219221 219223
    (.seq (block [.copyN 219240 219221, .subN 219241 219223 219221, .constN 219242 0,
      .constN 219243 0]) (pcS sp sM)) .skip


end

/-- The outputs. -/
def rgOut : Stmt := block [.copyN 219210 219110, .copyN 219211 219111, .copyN 219212 219113]

/-- **The region procedure.** -/
def rgS (sp sM : Stmt) : Stmt :=
  .seq rgInit0 (.seq plS (.seq rgPad (.seq rgInit1 (.seq (lfLoop sp sM)
    (.seq (finCon sp sM) rgOut)))))

end

end DrvG

end Chazelle.Core
