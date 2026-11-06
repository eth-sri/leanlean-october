module

public import Chazelle.Core.GranRamBase
public import Chazelle.Core.SignKernelRam

/-!
# WP-F, RAM part 2: the integer weights on the RAM

Straight-line procedures (no stores) of band `bGran` (registers `90000 + i`):

* `cntInStmt`: `r102 := cntIn ch m r100 r101` (the counted edges of `[l, r)`);
* `gwStmt`: `r92 := gwt ch m n eg pz r90 r91` (the weight of the key interval between two ring
  positions), reading the arrays `eg`, `pz` of the state;
* `ddStmt`: `r89 := dd c r88` (does position `r88` die with the chord `c`);
* `jwStmt`: `r85 := jw c n` for the position `n` in `r86` with its death bit in `r87`.

Register map (band 9): constants `90014 γ`, `90015 n`, `90016 2m + 6`, `90017 ch`,
`90018 size`, `90019 = 1`, `90020 = 3`, `90021 = 2`, `90022 = 6`; bases `90030 … 90044`;
`90050` top, `90051` nlive; temporaries `90060 …`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Counting edges -/

/-- The bit of a Boolean. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

end

end Gran

end Chazelle.Core
